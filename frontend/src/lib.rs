// trust-ir-frontend — M1 automated THIR -> trust-ir lowering (library core).
//
// This crate's job (per ~/trust-ir/designs/2026-06-28-rust-to-trust-ir-frontend.md,
// milestone M1): take a function `LocalDefId`, read `tcx.thir_body(def)`, and
// lower a single-match-over-enum bool-returning function (target: `Level::is_zero`
// / `is_nonzero`, or the `MicroLevel` leaf from the M0 POC) into a `trust_ir::Function`
// via the `trust_ir_build` builder API:
//
//   THIR Block/Expr        -> CFG blocks
//   match                  -> discriminant read (ExtractField field 0) + Switch
//   recursion              -> Call (to the same FuncId)
//   short-circuit `&&`/`||`-> CondBr
//   field read             -> ExtractField
//
// M2 (faithful heap) update: the enum is modeled as a tagged STRUCT with a
// FINITE C layout — `{ tag: i32 @0, p0: ptr @8, p1: ptr @16 }` — whose recursive
// payload slots are POINTERS (`Ty::Ptr`), i.e. real `Box<Level>`/`Arc<Level>`
// heap pointers, NOT inline recursive struct values. The `&self` receiver is a
// pointer to such a struct. The function lowers to:
//
//   THIR Block/Expr        -> CFG blocks
//   &self                  -> a `ptr` parameter (the heap pointer to the struct)
//   match discriminant     -> Load(i32, GEP(i8, self_ptr, 0)) + Switch
//   l1.is_zero()           -> Load(ptr, GEP(i8, self_ptr, payload_off)) + Call(self, child_ptr)
//   short-circuit `&&`/`||`-> CondBr
//
// The whole-struct value never materializes in an SSA register; every field is
// reached through a typed Load over a byte-offset GEP (the design's prescribed
// struct field access). This is faithful to how Rust reads a `Box`'d ADT: it
// dereferences the pointer and reads individual fields, touching no padding.
//
// Author: M1 frontend; M2 heap lowering
// License: Apache-2.0

#![feature(rustc_private)]
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

// Forces the rustc internals to link via the single `rustc_driver` dylib, which
// is what makes a `#![feature(rustc_private)]` *test* binary (and any plain
// binary) actually link — the individual `rustc_*` crates ship only as dylib in
// the toolchain, so without this the test harness fails with "crate ... required
// to be available in rlib format".
#[allow(unused_extern_crates)]
extern crate rustc_driver;

use rustc_abi::{Size, TagEncoding, VariantIdx, Variants};
use rustc_middle::thir::{ExprId, ExprKind, PatKind, Thir};
use rustc_middle::ty::layout::LayoutCx;
use rustc_middle::ty::{self, TyCtxt, TyKind};
use rustc_span::def_id::LocalDefId;

use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::ty::{EnumVariant, FieldDef, StructDef, Ty as IrTy};
use trust_ir::value::{FuncId, StructId, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

pub mod m3;
pub mod model;
pub mod span_map;

/// rustc ABI version baked into the private driver this frontend links.
pub fn linked_rustc_version() -> Option<&'static str> {
    rustc_interface::util::rustc_version_str()
}

/// Add the sysroot of the ABI-matching external `rustc` unless the caller
/// supplied one explicitly.
///
/// A rustc-private driver commonly needs `DYLD_LIBRARY_PATH`/`LD_LIBRARY_PATH`
/// to load its own `rustc_driver`. Passing that loader override through to the
/// child used for `--print=sysroot` can make a public stage1 `rustc` load the
/// prepared private driver and report the private metadata root instead of the
/// stage1 standard-library sysroot. Query in a sanitized child and verify that
/// its compiler version matches the in-process driver before accepting it.
pub fn append_matching_rustc_sysroot(rustc_args: &mut Vec<String>) -> Result<(), String> {
    if rustc_args
        .iter()
        .any(|arg| arg == "--sysroot" || arg.starts_with("--sysroot="))
    {
        return Ok(());
    }

    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let clean_command = |arg: &str| {
        let mut command = std::process::Command::new(&rustc);
        command
            .arg(arg)
            .env_remove("DYLD_LIBRARY_PATH")
            .env_remove("DYLD_FALLBACK_LIBRARY_PATH")
            .env_remove("LD_LIBRARY_PATH");
        command
    };

    let version_output = clean_command("--version")
        .output()
        .map_err(|error| format!("failed to execute RUSTC={rustc:?} --version: {error}"))?;
    if !version_output.status.success() {
        return Err(format!(
            "RUSTC={rustc:?} --version failed with status {}: {}",
            version_output.status,
            String::from_utf8_lossy(&version_output.stderr).trim()
        ));
    }
    let actual_version = String::from_utf8(version_output.stdout)
        .map_err(|_| format!("RUSTC={rustc:?} --version returned non-UTF-8 output"))?;
    if let Some(expected_version) = linked_rustc_version() {
        if !actual_version.trim().ends_with(expected_version) {
            return Err(format!(
                "RUSTC={rustc:?} is `{}`, but this frontend is linked to rustc {expected_version}; \
                 pass an ABI-matching stage1 RUSTC or an explicit --sysroot",
                actual_version.trim()
            ));
        }
    }

    let sysroot_output = clean_command("--print=sysroot")
        .output()
        .map_err(|error| format!("failed to execute RUSTC={rustc:?} --print=sysroot: {error}"))?;
    if !sysroot_output.status.success() {
        return Err(format!(
            "RUSTC={rustc:?} --print=sysroot failed with status {}: {}",
            sysroot_output.status,
            String::from_utf8_lossy(&sysroot_output.stderr).trim()
        ));
    }
    let sysroot = String::from_utf8(sysroot_output.stdout)
        .map_err(|_| format!("RUSTC={rustc:?} --print=sysroot returned non-UTF-8 output"))?;
    let sysroot = sysroot.trim();
    if sysroot.is_empty() || !std::path::Path::new(sysroot).join("lib/rustlib").is_dir() {
        return Err(format!(
            "RUSTC={rustc:?} returned invalid sysroot `{sysroot}`; pass --sysroot explicitly"
        ));
    }
    rustc_args.push("--sysroot".into());
    rustc_args.push(sysroot.into());
    Ok(())
}

/// Public accessor for the THIR `ExprKind` diagnostic name (used by the M3
/// dispatch path to report an unexpected expr shape).
pub fn expr_kind_name_pub(kind: &ExprKind<'_>) -> &'static str {
    expr_kind_name(kind)
}

/// A diagnostic-rich error surfaced by the lowering when it meets THIR it does
/// not (yet) handle. The frontend is FAIL-LOUD by design: it never silently
/// emits wrong IR for an unsupported construct.
#[derive(Debug, Clone)]
pub struct LowerError(pub String);

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "trust-ir-frontend lowering error: {}", self.0)
    }
}
impl std::error::Error for LowerError {}

pub type LResult<T> = Result<T, LowerError>;

fn bail<T>(msg: impl Into<String>) -> LResult<T> {
    Err(LowerError(msg.into()))
}

/// The structural classification of the single enum the target function matches
/// over, recovered from the THIR scrutinee's `ty`. We model it as a tagged
/// struct: field 0 is the i32 discriminant tag, fields 1.. are payload slots
/// (one slot per max-arity payload position; recursive children are nested
/// aggregates at runtime).
#[derive(Debug, Clone)]
pub struct EnumModel {
    pub name: String,
    /// One entry per variant, in `VariantIdx` order: (variant name, discriminant tag, n payload fields).
    pub variants: Vec<(String, i128, usize)>,
    /// The trust-ir struct id chosen for the tagged-struct model.
    pub struct_id: StructId,
    /// M6: the FAITHFUL layout recovered from `tcx.layout_of`. This is the
    /// source of truth for the tag READ (offset + width + Switch values) and the
    /// per-variant field offsets, REPLACING the hand-coded `TAG_OFFSET`/
    /// `payload_offset`/`I32` constants. Both the lowering (match/construction)
    /// AND the differential heap builders read from it, so they stay byte-stable
    /// with respect to the REAL compiled layout.
    pub layout: EnumLayout,
}

impl EnumModel {
    /// The Switch VALUE for routing `idx`: a Direct enum's discriminant, or a
    /// Niche enum's encoded niche tag value. Returns `None` for the niche
    /// untagged variant (which is the Switch DEFAULT, not a case) and for an
    /// out-of-range index. (Convenience wrapper over `layout`.)
    #[allow(dead_code)]
    pub(crate) fn discr_for_variant(&self, idx: VariantIdx) -> Option<i128> {
        self.layout.switch_value_for_variant(idx)
    }
}

/// M6: how a variant's discriminant is encoded in memory — the faithful read off
/// `rustc_abi::TagEncoding`.
#[derive(Debug, Clone)]
pub enum LayoutTagEncoding {
    /// `TagEncoding::Direct`: the tag field holds the variant's discriminant
    /// value directly. Every variant has a Switch case; the default is
    /// unreachable (exhaustive) unless a wildcard arm exists.
    Direct,
    /// `TagEncoding::Niche`: the discriminant is encoded as a NICHE in a payload
    /// field. The `untagged_variant` writes NO niche (the field holds its real
    /// value) and is the Switch DEFAULT; each niche variant has a Switch case at
    /// its encoded niche value.
    Niche {
        /// The variant whose payload occupies the niche (the Switch default).
        untagged_variant: VariantIdx,
    },
}

/// M6: the per-variant in-memory layout recovered from `layout_of`.
#[derive(Debug, Clone)]
pub struct VariantLayout {
    pub name: String,
    /// The Switch VALUE that routes the loaded tag to this variant. `None` for
    /// the niche untagged variant (it is the Switch DEFAULT). For a Direct enum
    /// every variant has `Some(discriminant)`.
    pub switch_value: Option<i128>,
    /// Byte offset of each of this variant's fields, in field-index order, read
    /// from `layout.for_variant(..).fields.offset(i)`.
    pub field_offsets: Vec<i128>,
}

/// M6: the FAITHFUL enum layout from `tcx.layout_of`. REPLACES the hand-coded
/// `TAG_OFFSET=0`, `payload_offset(i)=8+8i`, and `I32` tag constants.
///
/// The whole-struct byte size/align is recorded so the tagged trust-ir struct
/// the differential `HeapAlloc`s matches the real allocation size; the tag is
/// READ at `tag_offset` with width `tag_ir_ty`; each variant's fields live at
/// their REAL per-variant offsets.
#[derive(Debug, Clone)]
pub struct EnumLayout {
    /// Total size/align of the enum (bytes). Used for the tagged struct's
    /// explicit size/align so the heap alloc matches the real footprint.
    pub size: i128,
    pub align: i128,
    /// Byte offset at which the discriminant tag/niche is READ.
    pub tag_offset: i128,
    /// The trust-ir integer type to Load the tag with (I8/I16/I32/I64), chosen
    /// from the real tag scalar's byte width.
    pub tag_ir_ty: IrTy,
    /// Direct vs Niche encoding.
    pub tag_encoding: LayoutTagEncoding,
    /// Per-variant layout, in `VariantIdx` order.
    pub variants: Vec<VariantLayout>,
}

impl EnumLayout {
    /// The Switch value for `idx` (`None` for the niche untagged variant / out of
    /// range).
    pub fn switch_value_for_variant(&self, idx: VariantIdx) -> Option<i128> {
        self.variants
            .get(idx.as_usize())
            .and_then(|v| v.switch_value)
    }

    /// Byte offset of `field` in variant `idx`.
    pub fn field_offset(&self, idx: VariantIdx, field: usize) -> Option<i128> {
        self.variants
            .get(idx.as_usize())
            .and_then(|v| v.field_offsets.get(field).copied())
    }

    /// Is this a niche-encoded enum (any non-Direct encoding)?
    pub fn is_niche(&self) -> bool {
        matches!(self.tag_encoding, LayoutTagEncoding::Niche { .. })
    }
}

// M5.5: the M1/M2 `LowerCx` lowering context + its body lowerer have been RETIRED.
// There is now ONE lowering path: the unified `MonoCx` in `m3.rs` (driven via
// `m3::lower_predicate_to_builder`, to which `lower_fn_to_builder`/
// `lower_fn_to_module` below delegate). M5.6 proved `MonoCx` subsumes the retired
// `LowerCx` leaf class (`Level::is_zero`/`is_nonzero`) at 42/42 differential
// parity, and the default-mode is_zero/is_nonzero heap differential stays 21/21
// through `MonoCx`. The shared free-fn helpers `LowerCx` used — `build_enum_model`,
// `EnumModel`, the standalone `load_field` / `pattern_variants`,
// `collect_bindings` / `record_field_binding`, `peel_ref`, `find_match_enum` —
// are KEPT: `MonoCx` reuses them.
//
// M6: the former hand-coded `TAG_OFFSET=0` / `payload_offset(i)=8+8i` constants
// are RETIRED — the tag offset, tag width, and per-variant field offsets now come
// FAITHFULLY from `enum_layout_of` (`tcx.layout_of`). `load_field`/`field_addr`/
// `store_field` still take an explicit byte offset; the caller passes the REAL
// offset from the `EnumLayout`.

/// Free-fn field accessor (the former `LowerCx::load_field` body, kept after the
/// M5.5 LowerCx retirement): emit a typed `Load(ty)` of the field at `byte_offset`
/// of the struct at `self_ptr`, reached through an `I8`-pointee byte-offset GEP.
/// The single field-access primitive the unified `MonoCx` ADT-match (in `m3.rs`)
/// uses. NOTE: MonoCx's predicate emission is the join-block form, NOT byte-
/// identical to the retired LowerCx per-arm `ret`; the preserved contract is the
/// BEHAVIORAL differential (is_zero/is_nonzero 21/21), not byte-identity.
pub(crate) fn load_field(
    fb: &mut FunctionBuilder<'_>,
    self_ptr: ValueId,
    byte_offset: i128,
    ty: IrTy,
) -> ValueId {
    let field_ptr = field_addr(fb, self_ptr, byte_offset);
    fb.load(ty, field_ptr)
}

/// M5.7b: emit ONLY the byte-offset GEP that ADDRESSES the field at `byte_offset`
/// of the struct at `self_ptr` (an `I8`-pointee GEP, returning a typed `Ptr`),
/// WITHOUT a `Load`. This is the address of the field's slot.
///
/// Used by the ADT-match payload binder for an INLINE-SCALAR field: matching
/// `&Enum`, a by-ref binding `n` of a scalar field (`Val::Lit(i64)`) has type
/// `&i64` = the ADDRESS of the inline value (the slot), NOT a pointer stored in
/// the slot. So the binder binds `n = field_addr(slot)` (typed Ptr) and the arm
/// body's `*n` (the M5.4 scalar-Deref path) does the `Load(i64, n)` that reads
/// the inline value at the right width. Contrast `load_field`, which is correct
/// for a POINTER slot (a `Box`/`&`/recursive-enum child) where the slot HOLDS the
/// pointer and a by-ref binding is the stored pointer = `Load(Ptr, GEP)`.
pub(crate) fn field_addr(
    fb: &mut FunctionBuilder<'_>,
    self_ptr: ValueId,
    byte_offset: i128,
) -> ValueId {
    let off = fb.iconst(IrTy::I64, byte_offset);
    fb.gep_inbounds(IrTy::I8, self_ptr, vec![off])
}

/// M5.7f: emit a typed `Store` of `value` (of type `ty`) into the field at
/// `byte_offset` of the struct at `self_ptr`, reached through the SAME `I8`-pointee
/// byte-offset GEP `load_field`/`field_addr` use. The single field-WRITE primitive
/// the unified `MonoCx` enum-variant construction (in `m3.rs`) uses — the DUAL of
/// `load_field`. Identical in shape to `model.rs::store_field` (the M2/M5.4
/// differential's hand-written heap builder), so a constructed value reads back
/// byte-for-byte through `load_field`.
pub(crate) fn store_field(
    fb: &mut FunctionBuilder<'_>,
    self_ptr: ValueId,
    byte_offset: i128,
    ty: IrTy,
    value: ValueId,
) {
    let field_ptr = field_addr(fb, self_ptr, byte_offset);
    fb.store(ty, field_ptr, value);
}

/// M6: map a tag scalar's byte width to the trust-ir integer type to Load it
/// with. The discriminant/niche is READ at exactly this width (a wider Load would
/// touch a neighbouring field; a narrower one would drop high bits of the tag).
fn tag_ir_ty_for_size(enum_name: &str, bytes: u64) -> LResult<IrTy> {
    match bytes {
        1 => Ok(IrTy::I8),
        2 => Ok(IrTy::I16),
        4 => Ok(IrTy::I32),
        8 => Ok(IrTy::I64),
        other => bail(format!(
            "enum `{enum_name}`: discriminant/niche tag is {other} bytes wide, which has no \
             matching trust-ir integer Load width (1/2/4/8 are supported) — refusing to \
             mis-read the tag"
        )),
    }
}

/// M6 — THE FAITHFULNESS CORE. Compute the REAL in-memory `EnumLayout` for an
/// enum ADT via `tcx.layout_of`, REPLACING the hand-coded tag/offset constants.
///
/// Direct vs Niche:
///   * `Variants::Single` — a 1-variant enum: no tag is read (the single variant
///     is always selected). Modeled as a Direct tag of value 0 at offset 0 (the
///     Switch degenerates to that one case).
///   * `Variants::Multiple { tag, tag_encoding, tag_field, variants }`:
///     - tag READ offset = `fields.offset(tag_field)`, width = `tag.size(tcx)`.
///     - `TagEncoding::Direct`: each variant's Switch value =
///       `ty.discriminant_for_variant(idx).val` (a u128, narrowed to i128/the tag
///       width). The default is unreachable unless a wildcard arm exists.
///     - `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }`:
///       the `untagged_variant` writes NO niche and is the Switch DEFAULT; each
///       niche variant `v` has Switch value =
///       `truncate_to_tag_width( niche_start + (v.index() - niche_variants.start().index()) )`
///       (wrapping add, then masked to the tag byte width) — the exact formula
///       rustc's own codegen/const-eval uses (cranelift `codegen_set_discriminant`
///       / const-eval `tag_for_variant`).
///
/// Per-variant field offsets come from `layout.for_variant(tcx, idx).fields.offset(i)`.
pub(crate) fn enum_layout_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt: ty::AdtDef<'tcx>,
) -> LResult<EnumLayout> {
    let name = tcx.item_name(adt.did()).to_string();
    // The MONOMORPHIC enum type. The corpus + M6 enums are non-generic, so the
    // identity args are concrete; a generic enum would need its instantiation
    // (out of scope — the recursive corpus enums carry no type params).
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let enum_ty =
        tcx.normalize_erasing_regions(typing_env, tcx.type_of(adt.did()).instantiate_identity());
    let tal = tcx
        .layout_of(typing_env.as_query_input(enum_ty))
        .map_err(|e| {
            LowerError(format!(
                "enum `{name}`: tcx.layout_of failed ({e:?}) — cannot derive a faithful layout"
            ))
        })?;

    let size = tal.size.bytes() as i128;
    let align = tal.align.abi.bytes() as i128;

    // `for_variant` needs a cx implementing BOTH `HasTyCtxt` and `HasTypingEnv`;
    // `TyCtxt` alone is not enough, so wrap it in a `LayoutCx`.
    let lcx = LayoutCx::new(tcx, typing_env);

    // Per-variant field offsets (shared by both encodings): read each variant's
    // OWN field offsets through `for_variant`.
    let variant_field_offsets = |idx: VariantIdx| -> Vec<i128> {
        let vlayout = tal.for_variant(&lcx, idx);
        let vdef = adt.variant(idx);
        (0..vdef.fields.len())
            .map(|i| vlayout.fields.offset(i).bytes() as i128)
            .collect()
    };

    match &tal.variants {
        // A 1-variant enum: no tag is read; the single variant is always taken.
        Variants::Single { index } => {
            let idx = *index;
            let vdef = adt.variant(idx);
            let mut variants = Vec::with_capacity(adt.variants().len());
            for (vidx, v) in adt.variants().iter_enumerated() {
                // Only the present variant has a (degenerate) Switch value 0; any
                // other variant index is uninhabited here.
                let switch_value = if vidx == idx { Some(0) } else { None };
                let field_offsets = if vidx == idx {
                    variant_field_offsets(idx)
                } else {
                    Vec::new()
                };
                variants.push(VariantLayout {
                    name: v.name.to_string(),
                    switch_value,
                    field_offsets,
                });
            }
            let _ = vdef;
            Ok(EnumLayout {
                size,
                align,
                tag_offset: 0,
                tag_ir_ty: IrTy::I8,
                tag_encoding: LayoutTagEncoding::Direct,
                variants,
            })
        }
        Variants::Multiple {
            tag,
            tag_encoding,
            tag_field,
            ..
        } => {
            let tag_offset = tal.fields.offset(tag_field.index()).bytes() as i128;
            let tag_bytes = tag.size(&tcx).bytes();
            let tag_ir_ty = tag_ir_ty_for_size(&name, tag_bytes)?;
            let tag_size = Size::from_bytes(tag_bytes);

            let mut variants: Vec<VariantLayout> = Vec::with_capacity(adt.variants().len());
            for (idx, v) in adt.variants().iter_enumerated() {
                variants.push(VariantLayout {
                    name: v.name.to_string(),
                    switch_value: None, // filled per-encoding below
                    field_offsets: variant_field_offsets(idx),
                });
            }

            let encoding = match tag_encoding {
                TagEncoding::Direct => {
                    for (idx, _) in adt.variants().iter_enumerated() {
                        let discr = adt.discriminant_for_variant(tcx, idx).val;
                        // Mask to the tag width then sign/zero handling: the tag is
                        // Loaded as `tag_ir_ty` and compared by VALUE against this
                        // Switch constant, so it must be the SAME bit pattern the
                        // Load produces. Truncate to the tag width.
                        let masked = tag_size.truncate(discr);
                        let sv = u128_to_tag_i128(&name, &v_name(adt, idx), masked, tag_bytes)?;
                        variants[idx.as_usize()].switch_value = Some(sv);
                    }
                    LayoutTagEncoding::Direct
                }
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                } => {
                    let start = niche_variants.start.as_u32();
                    for (idx, _) in adt.variants().iter_enumerated() {
                        if idx == *untagged_variant {
                            // The untagged variant writes NO niche — it is the
                            // Switch DEFAULT (switch_value stays None).
                            continue;
                        }
                        if !niche_variants.contains(&idx) {
                            // A non-niche, non-untagged variant cannot occur in a
                            // well-formed niche encoding; refuse to invent a value.
                            return bail(format!(
                                "enum `{name}`: variant `{}` is neither the untagged variant nor \
                                 in the niche range — unexpected niche layout, refusing to guess",
                                v_name(adt, idx)
                            ));
                        }
                        // tag_value = niche_start + (idx - niche_start_idx), wrapping
                        // in the tag width (rustc codegen `codegen_set_discriminant`).
                        let rel = idx.as_u32().wrapping_sub(start) as u128;
                        let raw = rel.wrapping_add(*niche_start);
                        let masked = tag_size.truncate(raw);
                        let sv = u128_to_tag_i128(&name, &v_name(adt, idx), masked, tag_bytes)?;
                        variants[idx.as_usize()].switch_value = Some(sv);
                    }
                    LayoutTagEncoding::Niche {
                        untagged_variant: *untagged_variant,
                    }
                }
            };

            Ok(EnumLayout {
                size,
                align,
                tag_offset,
                tag_ir_ty,
                tag_encoding: encoding,
                variants,
            })
        }
        // An uninhabited / empty enum has no inhabited variant to match — there is
        // nothing to lower a match over. Bail loud rather than emit a tag read.
        Variants::Empty => bail(format!(
            "enum `{name}`: layout is `Variants::Empty` (uninhabited) — a match over it has no \
             reachable arm, refusing to lower a tag read"
        )),
    }
}

/// Variant name (for diagnostics).
fn v_name<'tcx>(adt: ty::AdtDef<'tcx>, idx: VariantIdx) -> String {
    adt.variant(idx).name.to_string()
}

/// M6: narrow a tag-width-masked `u128` tag value to the `i128` the trust-ir
/// `Switch`/`Constant::Int` carries, keeping the EXACT bit pattern the typed Load
/// produces. The trust-ir interpreter Loads the tag as `tag_ir_ty` and compares
/// it as that type's value; the Switch constant is an `i128` that must equal that
/// loaded value. For widths 1/2/4 the masked value is < 2^32 so it fits an i128
/// unchanged. For an 8-byte tag, a value with the top bit set would, if the Load
/// is a SIGNED I64, decode as negative; we therefore sign-extend an 8-byte tag so
/// the constant matches a signed-I64 Load. (All corpus + M6 tags are small
/// positive values, so this never actually wraps — but it is the correct,
/// fail-safe mapping.)
fn u128_to_tag_i128(
    enum_name: &str,
    variant_name: &str,
    masked: u128,
    tag_bytes: u64,
) -> LResult<i128> {
    if tag_bytes >= 16 {
        return bail(format!(
            "enum `{enum_name}`: variant `{variant_name}` tag is {tag_bytes} bytes — a 16-byte \
             (i128-width) tag has no trust-ir Load/Switch representation"
        ));
    }
    // Sign-extend at the tag width: the trust-ir signed-int Load (I8/I16/I32/I64)
    // interprets the high bit as sign, so the Switch constant must match.
    let signed = Size::from_bytes(tag_bytes).sign_extend(masked);
    Ok(signed)
}

/// Build the tagged-struct `EnumModel` for an enum ADT, registering its struct
/// type in the module with the FAITHFUL heap layout derived from `layout_of`.
/// The trust-ir struct is `{ tag: <tag width> @0, p0: ptr, .. }` — the slot types
/// are still uniform (a tag + pointer/scalar slots) but the tag WIDTH and the tag
/// OFFSET + per-variant field OFFSETS now come from the REAL compiled layout
/// (`EnumLayout`), not hand-coded constants. Recursive payloads are `Ty::Ptr`
/// (a `Box`/`Arc`), so the struct is finite and `HeapAlloc`/`Store`/`Load` of it
/// is well-defined.
pub(crate) fn build_enum_model<'tcx>(
    tcx: TyCtxt<'tcx>,
    mb: &mut ModuleBuilder,
    adt: ty::AdtDef<'tcx>,
) -> LResult<EnumModel> {
    let name = tcx.item_name(adt.did()).to_string();
    let layout = enum_layout_of(tcx, adt)?;
    let mut variants = Vec::new();
    let mut max_payload = 0usize;
    for (idx, vdef) in adt.variants().iter_enumerated() {
        // The model's `variants` tuple keeps the Switch value for legacy callers
        // (the driver reads `.variants.len()`); the authoritative value lives in
        // `layout`. A niche untagged variant has no Switch value — record 0 as a
        // placeholder (it is the Switch DEFAULT, never compared).
        let sv = layout.switch_value_for_variant(idx).unwrap_or(0);
        let nfields = vdef.fields.len();
        max_payload = max_payload.max(nfields);
        variants.push((vdef.name.to_string(), sv, nfields));
    }
    // Tagged-struct fields: [ tag: <real width>, p0: ptr, .. p{max-1}: ptr ].
    // The struct's explicit size/align match the real footprint so the heap
    // alloc covers every real field offset (incl. niche layouts where children
    // sit AFTER the niche word). Payload slots are POINTERS (a `Box`/`Arc`).
    let self_struct = StructId::new(0);
    // The interpreter computes a struct's C-layout (offsets/size/align) from the
    // field TYPES in declaration order; the actual Store/Load go through explicit
    // byte-offset GEPs (`field_addr`) carrying the REAL per-variant offsets from
    // `layout`. So the struct def's job is only to give a finite size big enough
    // for every offset we touch. `{ tag, p0, .. }` of pointer-width slots yields a
    // C-size that covers tag@0..max-pointer-offset; we leave size/align/offset as
    // `None` (computed) rather than pinning them (the GEPs, not these, are
    // authoritative — a pinned size disagreeing with the computed one is only
    // confusing). The tag's WIDTH (i8/16/32/64) IS faithful (it drives the Load).
    //
    // M5.7e: the slot count is the MAX of (the field count) AND (the count needed
    // to cover the REAL layout SIZE). A variant whose single FIELD is an inline
    // AGGREGATE (`Span((i64, i64))`) occupies MORE than one 8-byte slot, so a
    // field-count-based size (`tag + 1 pointer` = 16 bytes) would be SMALLER than
    // the real footprint (24 bytes) and a Store at the aggregate's far sub-field
    // (offset 16) would be out of bounds. We add enough 8-byte pointer slots so the
    // computed C-size >= `layout.size`. For the pointer-payload corpus enums
    // (Level/Val/Term: real size 24, max field count 2 -> 2 slots) this is
    // UNCHANGED (2 slots either way), so their emitted struct stays byte-identical;
    // only an aggregate-bearing enum (Sym: field count 1 but real size 24) gets the
    // extra slot.
    // Pointer-width (8) slots needed to cover the bytes after the tag word. The tag
    // (<= 8 bytes) is followed by 8-aligned pointer slots, so the payload region
    // begins at offset 8; cover `layout.size - 8` more bytes in 8-byte slots.
    let payload_region = (layout.size - 8).max(0);
    let slots_for_size = ((payload_region + 7) / 8) as usize;
    let n_slots = max_payload.max(slots_for_size);
    let mut fields = vec![FieldDef {
        name: "tag".into(),
        ty: layout.tag_ir_ty.clone(),
        offset: None,
    }];
    for i in 0..n_slots {
        fields.push(FieldDef {
            name: format!("p{i}"),
            ty: IrTy::Ptr,
            offset: None,
        });
    }
    let struct_id = mb.add_struct(StructDef {
        id: self_struct,
        name: name.clone(),
        fields,
        size: None,
        align: None,
        repr: Default::default(),
    });
    debug_assert_eq!(struct_id, self_struct, "first add_struct must yield id 0");
    Ok(EnumModel {
        name,
        variants,
        struct_id,
        layout,
    })
}

// M6: the former `check_discr_fits_i32_tag` (audit FIX D) hardcoded an I32 tag
// width and rejected out-of-range discriminants. It is RETIRED: the tag width is
// now derived FAITHFULLY from the real layout (`tag_ir_ty_for_size` picks
// I8/I16/I32/I64 from the real tag byte width), and `u128_to_tag_i128` maps each
// discriminant/niche value at the real tag width — so a wider discriminant is
// handled, not rejected.

/// Public entry: lower a target `LocalDefId` into a fresh single-function trust-ir
/// `Module`. Returns the module plus the recovered `EnumModel` (for the
/// differential harness to construct matching inputs).
pub fn lower_fn_to_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> LResult<(Module, EnumModel, FuncId)> {
    let (mb, enum_model, func_id) = lower_fn_to_builder(tcx, def)?;
    Ok((mb.build(), enum_model, func_id))
}

/// Lower the predicate into a fresh `ModuleBuilder`, returning it UNBUILT so a
/// caller can append more functions (e.g. the differential's heap-constructing
/// runners) into the SAME module before `build()`. The predicate is always
/// `FuncId(0)` with signature `fn(ptr) -> bool`, and the tagged struct is
/// `StructId(0)`.
///
/// M5.5: there is now ONE lowering path. This entry DELEGATES to the unified
/// `MonoCx` lowerer (`m3::lower_predicate_to_builder`), which M5.6 proved
/// subsumes the retired `LowerCx` M1/M2 path at 42/42 differential parity. The
/// signature is unchanged so `model.rs`/`main.rs` stay untouched callers. The
/// emitted IR is MonoCx's (join-block form), not LowerCx's per-arm `ret` — the
/// preserved contract is the BEHAVIORAL differential (is_zero/is_nonzero heap),
/// not byte-identity.
pub fn lower_fn_to_builder<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> LResult<(ModuleBuilder, EnumModel, FuncId)> {
    m3::lower_predicate_to_builder(tcx, def)
}

/// Peel scopes/blocks to find the `match` and return the scrutinee's enum ADT.
pub(crate) fn find_match_enum<'tcx>(
    _tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    expr: ExprId,
) -> LResult<ty::AdtDef<'tcx>> {
    let mut cur = expr;
    loop {
        match &thir[cur].kind {
            ExprKind::Scope { value, .. } => cur = *value,
            ExprKind::Use { source } | ExprKind::NeverToAny { source } => cur = *source,
            ExprKind::Block { block } => {
                let b = &thir[*block];
                match b.expr {
                    Some(e) => cur = e,
                    None => return bail("block with no trailing expr"),
                }
            }
            ExprKind::Match { scrutinee, .. } => {
                let scrut_ty = peel_ref(thir[*scrutinee].ty);
                match scrut_ty.kind() {
                    TyKind::Adt(adt, _) if adt.is_enum() => return Ok(*adt),
                    other => return bail(format!("match scrutinee is not an enum: {other:?}")),
                }
            }
            other => {
                return bail(format!(
                    "unexpected expr while seeking match: {:?}",
                    std::mem::discriminant(other)
                ));
            }
        }
    }
}

fn peel_ref(ty: ty::Ty<'_>) -> ty::Ty<'_> {
    match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => ty,
    }
}

pub(crate) enum PatternMatch {
    Wildcard,
    Variants(Vec<VariantIdx>),
}

/// Free fn (the former `LowerCx::pattern_variants` body, kept after the M5.5
/// LowerCx retirement — a pure function of the pattern kind). The single arm-
/// pattern classifier the unified `MonoCx` ADT-match (in `m3.rs`) uses.
pub(crate) fn pattern_variants<'tcx>(kind: &PatKind<'tcx>) -> LResult<PatternMatch> {
    match kind {
        PatKind::Wild | PatKind::Missing => Ok(PatternMatch::Wildcard),
        PatKind::Binding { subpattern, .. } => match subpattern {
            None => Ok(PatternMatch::Wildcard),
            Some(p) => pattern_variants(&p.kind),
        },
        PatKind::Variant { variant_index, .. } => Ok(PatternMatch::Variants(vec![*variant_index])),
        PatKind::Leaf { .. } => Ok(PatternMatch::Variants(vec![VariantIdx::from_usize(0)])),
        PatKind::Or { pats } => {
            let mut all = Vec::new();
            for p in pats.iter() {
                match pattern_variants(&p.kind)? {
                    PatternMatch::Variants(v) => all.extend(v),
                    PatternMatch::Wildcard => return Ok(PatternMatch::Wildcard),
                }
            }
            Ok(PatternMatch::Variants(all))
        }
        PatKind::Deref { subpattern, .. } => pattern_variants(&subpattern.kind),
        other => bail(format!(
            "unsupported pattern {:?}",
            std::mem::discriminant(other)
        )),
    }
}

/// SOUNDNESS GUARD (HIGH — silent miscompile): the ADT-match lowering routes each
/// arm by its OUTER variant only and emits a flat discriminant `Switch`.
/// `pattern_variants` DISCARDS every `Variant`/`Leaf`/`Constant`/`Range`/`Or`
/// SUBpattern, so an arm carrying a NESTED constructor/constant/range constraint
/// — e.g. `IMax(_, box Zero)`, `Succ(Succ(_))`, `Max(Level::Zero, _)` — would
/// fire for the WHOLE outer variant, silently DROPPING the inner constraint and
/// returning wrong results that still validate clean. This is exactly the pattern
/// shape a real `whnf`/`is_def_eq` uses, so it MUST fail loud, not miscompile.
///
/// M5.7a REFINED this all-or-nothing guard into the three-way
/// `classify_arm_subpatterns` (`Trivial` | `OneLevelNested` | `Unsupported`): the
/// COMMON one-level nested-constructor case (`App(Lam(_), _)`, the canonical
/// β-redex shape) is now LOWERED as a decision sub-tree (inner tag-check +
/// branch), while deeper/ambiguous shapes still bail loud. See
/// `classify_arm_subpatterns` below.

/// A FIELD subpattern is trivial iff it is `Wild`/`Missing` or a plain
/// `Binding { subpattern: None }` (a simple binder). A `Binding { subpattern:
/// Some }` (`field @ P`), or any constructor/constant/range/or/deref-to-such, is
/// a NESTED constraint the flat discriminant Switch would drop, so it is NOT
/// trivial. (`Deref`/`DerefPattern` is peeled: `box Zero` is non-trivial because
/// what it wraps is non-trivial; `&x` binder stays trivial.)
fn field_subpattern_is_trivial<'tcx>(kind: &PatKind<'tcx>) -> bool {
    match kind {
        PatKind::Wild | PatKind::Missing => true,
        PatKind::Binding {
            subpattern: None, ..
        } => true,
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            field_subpattern_is_trivial(&subpattern.kind)
        }
        // `field @ P`, a nested constructor/constant/range/or — all non-trivial.
        _ => false,
    }
}

/// M5.7e: is this field subpattern an INLINE-AGGREGATE destructure — a bare
/// `Leaf` (a tuple/struct destructure, e.g. the `(a, b)` in `Span((a, b))`)
/// whose OWN sub-field subpatterns are ALL TRIVIAL (`_`/`Missing`/plain binder)?
///
/// This is DISTINCT from a nested CONSTRUCTOR (`box Lam(_)`), which is a `Leaf`/
/// `Variant` BEHIND a `Deref`/`DerefPattern` (the `box`/`&` peel) — that sits at a
/// POINTER slot and is routed by an inner tag-check (M5.7a). An inline aggregate is
/// a bare `Leaf` (NO leading deref): the tuple/struct lives INLINE at the variant's
/// field slot, so it imposes NO routing constraint — the arm fires on the OUTER
/// variant alone, and the sub-bindings are read by GEP+Load at their REAL sub-field
/// offsets WITHIN the aggregate (the M5.7e payload path).
///
/// A DEEPER aggregate (a sub-field that is itself a bare `Leaf` — an
/// aggregate-in-aggregate) is STILL recognized as an inline aggregate here (so the
/// arm is classified non-routing and routed to the aggregate binder), but the
/// aggregate binder then BAILS loud at the depth-2 boundary (`bind_aggregate_payload`
/// — only one level of sub-field walking is in scope). A nested CONSTRUCTOR
/// sub-field (a `Deref`-wrapped ctor) makes this NOT an inline aggregate (returns
/// `false`) — that is a different shape the caller reports on.
fn field_subpattern_is_inline_aggregate<'tcx>(kind: &PatKind<'tcx>) -> bool {
    match kind {
        // A bare `Leaf` (NO leading Deref): a tuple/struct destructure. Each own
        // sub-field must be TRIVIAL (a binder/wildcard) OR itself a bare-`Leaf`
        // inline aggregate (a deeper aggregate — recognized here so the dedicated
        // depth guard in `bind_aggregate_payload` reports it, rather than the
        // generic `classify_arm_subpatterns` `Unsupported` bail). A `Deref`-wrapped
        // sub-field (a Box-child ctor inside the aggregate) is NOT a supported
        // inline aggregate.
        PatKind::Leaf { subpatterns } => subpatterns.iter().all(|fp| {
            field_subpattern_is_trivial(&fp.pattern.kind)
                || matches!(fp.pattern.kind, PatKind::Leaf { .. })
        }),
        _ => false,
    }
}

// --- M5.7a: ONE-LEVEL nested-CONSTRUCTOR match-pattern support ----------------
//
// The audit's `arm_subpatterns_are_trivial` BAILED on every nested constructor.
// M5.7a turns the COMMON canonical β-redex shape — `App(Lam(_), _)`, the exact
// pattern a real clean-kernel `whnf` uses for redex detection — into correct
// support via an inner tag-check + branch, while deeper/ambiguous shapes still
// bail loud (the soundness guard is REFINED, not removed).

/// Description of the SINGLE one-level nested constructor field in an ADT-match
/// arm: which OUTER field index carries it (`App` field 0 for `App(Lam(_), _)`),
/// and which INNER variant the nested constructor selects (`Lam`'s `VariantIdx`).
/// The nested constructor's OWN fields must themselves be trivial (Wild/binder),
/// so binding them reuses the existing flat M5.4/M5.7b payload binder against the
/// nested child pointer.
#[derive(Debug, Clone, Copy)]
pub(crate) struct NestedCtorField {
    /// The OUTER variant's field index that holds the nested constructor (the Box
    /// child slot, e.g. App's field 0).
    pub outer_field: usize,
    /// The INNER (nested) variant the nested constructor matches (e.g. Lam).
    pub inner_variant: VariantIdx,
}

/// The structural classification of an ADT-match arm for the M5.4/M5.7a lowering.
/// `arm_subpatterns_are_trivial` is REFINED into this three-way classifier:
/// instead of bailing on ALL nesting, the COMMON one-level case is recognized and
/// lowered as a decision sub-tree; only deeper/ambiguous shapes still bail.
#[derive(Debug, Clone, Copy)]
pub(crate) enum ArmShape {
    /// Every field subpattern is trivial (`_`/`Missing`/plain binder) — the
    /// existing flat one-level arm (`count_succ`/`is_zero`/`eval`). Lowered
    /// EXACTLY as before (no emission change — byte-identity preserved).
    Trivial,
    /// EXACTLY ONE field is a one-level nested constructor (its own fields all
    /// trivial); every other field is trivial — the M5.7a `App(Lam(_), _)` shape.
    OneLevelNested(NestedCtorField),
    /// A shape this flat-discriminant Switch cannot faithfully route on its own
    /// (deeper nesting, >1 nested-ctor field, a nested ctor whose own fields are
    /// non-trivial, an `@`-on-a-constructor, an Or/Constant/Range, ...). BAIL LOUD.
    Unsupported,
}

/// M5.7a: classify an ADT-match arm's pattern into `ArmShape`. This SUBSUMES
/// `arm_subpatterns_are_trivial` (it returns `Trivial` for exactly the arms that
/// returned `true` there) and additionally recognizes the one-level
/// nested-constructor case.
///
/// It peels the OUTER `Deref` (the implicit `&` from `match &Enum`) and an OUTER
/// `Binding { subpattern: Some }` (a top-level `x @ Variant(..)`) to reach the
/// constructor, then inspects that constructor's field subpatterns:
///   - all trivial -> `Trivial`;
///   - EXACTLY ONE field is a one-level nested CONSTRUCTOR (a `Deref`/
///     `DerefPattern` wrapping a `Variant`/`Leaf` whose OWN fields are all
///     trivial), the rest trivial -> `OneLevelNested`;
///   - anything else -> `Unsupported`.
/// A bare wildcard/binder arm (no constructor) is `Trivial`.
pub(crate) fn classify_arm_subpatterns<'tcx>(kind: &PatKind<'tcx>) -> ArmShape {
    match kind {
        // Peel the implicit `&`/`box` deref from matching over `&Enum`/`Box<Enum>`.
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            classify_arm_subpatterns(&subpattern.kind)
        }
        // A bare binder/wildcard arm carries no field constraints.
        PatKind::Wild | PatKind::Missing => ArmShape::Trivial,
        PatKind::Binding {
            subpattern: None, ..
        } => ArmShape::Trivial,
        // A top-level `x @ P`: classify `P` (which must itself be trivial-or-nested).
        PatKind::Binding {
            subpattern: Some(p),
            ..
        } => classify_arm_subpatterns(&p.kind),
        // A constructor pattern: inspect its field subpatterns.
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => {
            let mut nested: Option<NestedCtorField> = None;
            for fp in subpatterns.iter() {
                if field_subpattern_is_trivial(&fp.pattern.kind) {
                    continue;
                }
                // M5.7e: an INLINE-AGGREGATE destructure field (`Span((a, b))`'s
                // tuple field) imposes NO routing constraint — the arm fires on the
                // OUTER variant alone, and the sub-bindings are read by GEP+Load at
                // their REAL sub-field offsets. So it is NON-routing, like a trivial
                // field: do NOT treat it as a nested constructor (it is a bare `Leaf`
                // with no leading deref, so `nested_ctor_field_variant` would not
                // match it anyway — but recognize it explicitly to keep the arm
                // `Trivial` rather than `Unsupported`). A DEEPER aggregate (an
                // aggregate-in-aggregate sub-field) is rejected inside the predicate
                // (returns false), so it falls through to `Unsupported` below.
                if field_subpattern_is_inline_aggregate(&fp.pattern.kind) {
                    continue;
                }
                // A non-trivial field: it is M5.7a-supported ONLY if it is a
                // one-level nested CONSTRUCTOR (with trivial own fields), and it
                // is the ONLY such field in this arm.
                match nested_ctor_field_variant(&fp.pattern.kind) {
                    Some(inner_variant) if nested.is_none() => {
                        nested = Some(NestedCtorField {
                            outer_field: fp.field.as_usize(),
                            inner_variant,
                        });
                    }
                    // A second nested-ctor field, OR a non-trivial field that is
                    // not a one-level nested ctor (deeper nesting / @ / range / or):
                    // out of M5.7a scope.
                    _ => return ArmShape::Unsupported,
                }
            }
            match nested {
                None => ArmShape::Trivial,
                Some(n) => ArmShape::OneLevelNested(n),
            }
        }
        // M6 gap 1: an OR-pattern arm (`Succ(_) | Param(_) => false`, the VERBATIM
        // clean-kernel `Level::is_zero`/`is_nonzero` shape). It is `Trivial` — i.e.
        // a FLAT Switch with ONE CASE PER ALTERNATIVE all targeting the SAME arm
        // block — IFF every alternative is a SIMPLE variant pattern: a `Variant`/
        // `Leaf`/`Wild`/`Missing` whose OWN field subpatterns are ALL `_`/`Missing`
        // (no nested ctor, no binder). `pattern_variants` already returns the SET of
        // alternative variant indices for such an Or, so PASS A naturally pushes one
        // `SwitchCase` per alternative discriminant -> the (shared) arm block.
        //
        // An alternative CANNOT bind a payload: Rust requires all or-alternatives to
        // bind the SAME names with the SAME types, which for VARIANT alternatives of
        // different shape means NO field bindings at all. We therefore reject ANY
        // binder inside an alternative (a binding shared across alternatives is out
        // of scope) — and any nested-ctor / deeper / `@`-on-ctor alternative — LOUD.
        PatKind::Or { pats } => {
            if pats
                .iter()
                .all(|p| or_alternative_is_simple_variant(&p.kind))
            {
                ArmShape::Trivial
            } else {
                // A non-trivial Or alternative (a nested constructor, a binder, a
                // deeper nest, an `@`/Constant/Range, ...). BAIL LOUD — the flat
                // discriminant Switch cannot faithfully route it.
                ArmShape::Unsupported
            }
        }
        // Anything else at the top (`Constant`, `Range`, `Slice`, ...) is a
        // shape this flat-discriminant Switch cannot faithfully route — reject.
        _ => ArmShape::Unsupported,
    }
}

/// M6 gap 1: is `kind` a SIMPLE variant alternative usable inside an OR-pattern
/// arm — a `Variant`/`Leaf` (or bare `Wild`/`Missing`) whose OWN field subpatterns
/// are ALL `_`/`Missing` (NO binder, NO nested constructor)? Used by
/// `classify_arm_subpatterns` to recognize `Succ(_) | Param(_)` (the clean-kernel
/// `is_zero`/`is_nonzero` shape) as a flat one-case-per-alternative Switch.
///
/// This is STRICTER than `field_subpattern_is_trivial`: a plain binder field is
/// "trivial" for a SINGLE-arm constructor, but inside an OR it would have to bind
/// the SAME name+type across alternatives of DIFFERENT shape — which Rust forbids
/// for variant alternatives — so a binder alternative is rejected here (it falls
/// through to `Unsupported` and BAILS LOUD).
fn or_alternative_is_simple_variant<'tcx>(kind: &PatKind<'tcx>) -> bool {
    match kind {
        // Peel the implicit `&`/`box` deref from matching over `&Enum`/`Box<Enum>`.
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            or_alternative_is_simple_variant(&subpattern.kind)
        }
        // A bare wildcard alternative is fine (e.g. `Foo | _`).
        PatKind::Wild | PatKind::Missing => true,
        // A simple variant/leaf alternative: every field subpattern must be a
        // wildcard (NO binder — a shared binding across mismatched alternatives is
        // out of scope; NO nested ctor — that is a deeper constraint the flat Switch
        // would drop).
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => subpatterns
            .iter()
            .all(|fp| matches!(fp.pattern.kind, PatKind::Wild | PatKind::Missing)),
        // A binder alternative, a nested Or, a constant/range alternative, an
        // `@`-binding, etc. — out of scope.
        _ => false,
    }
}

/// If `kind` is a ONE-LEVEL nested CONSTRUCTOR field subpattern — a `Deref`/
/// `DerefPattern` (the `box`/`&` peel) wrapping a single-variant `Variant`/`Leaf`
/// whose OWN field subpatterns are ALL trivial (`_`/`Missing`/plain binder) —
/// return the nested constructor's `VariantIdx`. Otherwise `None`.
///
/// This deliberately requires the nested ctor's own fields to be trivial: a
/// DEEPER nest (`App(App(Lam(_),_),_)`, the nested ctor itself carrying a nested
/// ctor) returns `None` so the caller bails loud — only one level is supported.
///
/// M5.7e: a nested CONSTRUCTOR is ALWAYS behind a `Deref`/`DerefPattern` (the
/// `box`/`&` peel) — the nested ctor lives at a POINTER slot whose inner tag is
/// read by a candidate block. A BARE `Leaf` (no leading deref) is an INLINE
/// AGGREGATE destructure (`Span((a, b))`'s tuple field), NOT a nested ctor — it has
/// no inner tag and lives inline at the field slot. So `nested_ctor_field_variant`
/// REQUIRES a leading deref before the ctor; a bare `Leaf`/`Variant` returns
/// `None`, leaving the inline-aggregate case to `field_subpattern_is_inline_aggregate`.
fn nested_ctor_field_variant<'tcx>(kind: &PatKind<'tcx>) -> Option<VariantIdx> {
    match kind {
        // A nested ctor is reached THROUGH the `box`/`&` deref. Peel it, then the
        // inner MUST be a ctor (`nested_ctor_after_deref`).
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            nested_ctor_after_deref(&subpattern.kind)
        }
        // A bare ctor (no leading deref): NOT a nested constructor for M5.7e's
        // purposes — a bare `Leaf` is an inline aggregate, and a bare `Variant`
        // field subpattern is not a Box-child nested ctor we can read an inner tag
        // from. Either way, not handled here.
        _ => None,
    }
}

/// The CONSTRUCTOR inside a peeled `box`/`&` (a one-level nested ctor): a
/// `Variant`/`Leaf` whose OWN field subpatterns are ALL trivial. Further `Deref`s
/// are peeled (a `box &Foo` chain). Returns the ctor's `VariantIdx`, or `None` for
/// a deeper nest / non-trivial own fields (the caller bails loud).
fn nested_ctor_after_deref<'tcx>(kind: &PatKind<'tcx>) -> Option<VariantIdx> {
    match kind {
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            nested_ctor_after_deref(&subpattern.kind)
        }
        PatKind::Variant {
            variant_index,
            subpatterns,
            ..
        } => {
            // The nested ctor's OWN fields must all be trivial (one level only).
            if subpatterns
                .iter()
                .all(|fp| field_subpattern_is_trivial(&fp.pattern.kind))
            {
                Some(*variant_index)
            } else {
                None
            }
        }
        // A `Leaf` is a single-variant struct/tuple ctor (variant 0); its fields
        // must likewise be trivial.
        PatKind::Leaf { subpatterns } => {
            if subpatterns
                .iter()
                .all(|fp| field_subpattern_is_trivial(&fp.pattern.kind))
            {
                Some(VariantIdx::from_usize(0))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// M5.7a: collect the bindings that live INSIDE a one-level nested constructor at
/// outer field `outer_field` — i.e. the nested ctor's OWN field bindings, recorded
/// against the nested ctor's field indices. For `App(box Lam(b), _)` this records
/// `b -> 0` (Lam's field 0). These bindings are materialized in the nested block
/// against the nested CHILD pointer (the Box child loaded from the outer slot),
/// reusing the same flat payload-binding machinery the trivial case uses.
///
/// `out` maps each bound `LocalVarId` to its index within the NESTED constructor.
/// Bindings of the OUTER arm's other (trivial) fields are NOT collected here; they
/// are handled by the existing `collect_bindings` against the outer pointer.
pub(crate) fn collect_nested_bindings<'tcx>(
    arm_kind: &PatKind<'tcx>,
    outer_field: usize,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, usize>,
) -> LResult<()> {
    // Peel to the outer constructor, find the nested field, peel its Box/&, and
    // record the nested constructor's own field bindings.
    match arm_kind {
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            collect_nested_bindings(&subpattern.kind, outer_field, out)
        }
        PatKind::Binding {
            subpattern: Some(p),
            ..
        } => collect_nested_bindings(&p.kind, outer_field, out),
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => {
            for fp in subpatterns.iter() {
                if fp.field.as_usize() == outer_field {
                    return record_nested_ctor_bindings(&fp.pattern.kind, out);
                }
            }
            bail(format!(
                "M5.7a: nested field {outer_field} not found in arm constructor"
            ))
        }
        other => bail(format!(
            "M5.7a: unexpected arm pattern while collecting nested bindings ({:?})",
            std::mem::discriminant(other)
        )),
    }
}

/// Record the OWN field bindings of a nested constructor (peeling its `box`/`&`)
/// against the nested constructor's field indices. Reuses `record_field_binding`
/// (peels `Binding`/`Deref`/`DerefPattern` consistently with the trivial check).
fn record_nested_ctor_bindings<'tcx>(
    kind: &PatKind<'tcx>,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, usize>,
) -> LResult<()> {
    match kind {
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            record_nested_ctor_bindings(&subpattern.kind, out)
        }
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => {
            for fp in subpatterns.iter() {
                record_field_binding(&fp.pattern.kind, fp.field.as_usize(), out);
            }
            Ok(())
        }
        other => bail(format!(
            "M5.7a: nested constructor is not a Variant/Leaf ({:?})",
            std::mem::discriminant(other)
        )),
    }
}

/// The single enum `VariantIdx` a pattern matches (peeling `Deref`/`Binding`),
/// if it is a single-variant pattern. Used by the ADT-match payload-binding guard
/// to look up each bound field's REAL type (so a non-pointer payload slot can be
/// rejected rather than loaded as `Ptr`). Returns `None` for a wildcard, an
/// or-pattern, or any shape without exactly one variant index.
pub(crate) fn pattern_variant_idx<'tcx>(kind: &PatKind<'tcx>) -> Option<VariantIdx> {
    match kind {
        PatKind::Variant { variant_index, .. } => Some(*variant_index),
        PatKind::Deref { subpattern, .. } => pattern_variant_idx(&subpattern.kind),
        PatKind::Binding {
            subpattern: Some(sp),
            ..
        } => pattern_variant_idx(&sp.kind),
        // A `Leaf` is a single-variant struct/tuple pattern (variant 0). Match-over-
        // enum arms always carry an explicit `Variant`, so this is only reached for
        // a struct match (out of M5.4 scope) — treat as variant 0 conservatively.
        PatKind::Leaf { .. } => Some(VariantIdx::from_usize(0)),
        _ => None,
    }
}

/// Walk a pattern and record every `Binding { var }` that sits directly at a
/// `FieldPat { field }` position (i.e. `Max(l1, l2)` binds l1->field0, l2->field1).
///
/// SOUNDNESS (MEDIUM): this used to fall into a silent `_ => {}` for a TOP-LEVEL
/// whole-value binding — `match l { x => .. }` or `x @ Pat` at the scrutinee —
/// DROPPING `x` so the arm body's `x` reference would dangle (or, worse, an `@`
/// could constrain). FIX A's `arm_subpatterns_are_trivial` already rejects a
/// top-level `x @ Variant(..)` (it constrains), but a BARE top-level binder (`x`)
/// is trivial and would still reach here. The tagged-struct ADT-match binds
/// payload CHILDREN by field offset (a Ptr to a child node); a top-level binder
/// names the WHOLE scrutinee pointer, which this field-offset machinery does not
/// model — so bail LOUD rather than silently drop it. (Bindings nested deeper
/// than one field level are likewise rejected by FIX A before we get here.)
pub(crate) fn collect_bindings<'tcx>(
    kind: &PatKind<'tcx>,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, usize>,
) -> LResult<()> {
    match kind {
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => {
            for fp in subpatterns {
                let field = fp.field.as_usize();
                record_field_binding(&fp.pattern.kind, field, out);
            }
            Ok(())
        }
        PatKind::Deref { subpattern, .. } => collect_bindings(&subpattern.kind, out),
        // A TOP-LEVEL binding at the scrutinee binds the WHOLE value, not a field.
        PatKind::Binding { .. } => bail(
            "M5: a top-level whole-value binding at the ADT-match scrutinee \
             (`match l { x => .. }` or an `@`-binding of the scrutinee) is not yet \
             supported — the tagged-struct match binds payload CHILDREN by field \
             offset, not the whole scrutinee pointer (would otherwise drop the binder)",
        ),
        _ => Ok(()),
    }
}

/// Record a binding at the given enclosing field index. Peels `Binding`'s own
/// nested subpattern only to find a direct binding name.
///
/// SOUNDNESS (audit FIX #2 — trivial-check/record consistency): the trivial
/// checks (`field_subpattern_is_trivial` / `arm_subpatterns_are_trivial`) peel
/// BOTH `PatKind::Deref` AND `PatKind::DerefPattern` before declaring a binder
/// trivial, so a `box ref x` field subpattern (a `DerefPattern` wrapping a
/// `Binding`) passes the trivial check. This recorder MUST peel the SAME set, or
/// a binding the trivial check ALLOWED would go UNRECORDED — and a body reference
/// to it would fail with a confusing "VarRef not bound" rather than a clean bail.
/// So peel `DerefPattern` exactly as `Deref` is peeled, keeping record/trivial in
/// lock-step. (The trivial check is intentionally NOT changed.)
fn record_field_binding<'tcx>(
    kind: &PatKind<'tcx>,
    field: usize,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, usize>,
) {
    match kind {
        PatKind::Binding {
            var, subpattern, ..
        } => {
            out.insert(*var, field);
            if let Some(sp) = subpattern {
                record_field_binding(&sp.kind, field, out);
            }
        }
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            record_field_binding(&subpattern.kind, field, out)
        }
        _ => {}
    }
}

/// M5.7e: collect the bindings nested INSIDE an inline-AGGREGATE destructure field
/// (the `(a, b)` in `Span((a, b))`), keyed by their FULL field PATH from the OUTER
/// variant: `Span((a, b))` records `a -> [0, 0]` (outer field 0 = the tuple,
/// sub-field 0) and `b -> [0, 1]`. These paths are later walked through
/// `tcx.layout_of` to the binding's REAL cumulative byte offset (the aggregate's
/// offset within the variant + the sub-field's offset within the aggregate) and
/// bound by the same type-classified slot read `bind_payload_field` uses.
///
/// Only fields recognized by `field_subpattern_is_inline_aggregate` are walked
/// here (a bare `Leaf` whose own sub-fields are all trivial binders/wildcards). A
/// TRIVIAL field (a plain binder / Box child) is handled by `collect_bindings` and
/// is NOT recorded here (each binding is recorded by EXACTLY ONE collector). A
/// nested CONSTRUCTOR field (behind a `box`/`&`) is handled by
/// `collect_nested_bindings`. Peels the OUTER `Deref` (the `match &Enum` peel) and
/// an OUTER `x @ P` binder to reach the variant's field subpatterns.
pub(crate) fn collect_aggregate_bindings<'tcx>(
    arm_kind: &PatKind<'tcx>,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, Vec<usize>>,
) -> LResult<()> {
    match arm_kind {
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            collect_aggregate_bindings(&subpattern.kind, out)
        }
        PatKind::Binding {
            subpattern: Some(p),
            ..
        } => collect_aggregate_bindings(&p.kind, out),
        PatKind::Variant { subpatterns, .. } | PatKind::Leaf { subpatterns } => {
            for fp in subpatterns.iter() {
                // Only walk the inline-aggregate fields; trivial / nested-ctor
                // fields are recorded by their own collectors.
                if field_subpattern_is_inline_aggregate(&fp.pattern.kind) {
                    let outer_field = fp.field.as_usize();
                    record_aggregate_subbindings(&fp.pattern.kind, &[outer_field], out)?;
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Record the bindings of an inline-aggregate `Leaf`'s OWN sub-fields, extending
/// `prefix` (the path so far) with each sub-field index. For `Span((a, b))`'s tuple
/// field, with `prefix = [0]`, this records `a -> [0, 0]`, `b -> [0, 1]`. A
/// sub-field that is itself a non-trivial aggregate is rejected upstream
/// (`field_subpattern_is_inline_aggregate` returns false), so here every sub-field
/// is a trivial binder/wildcard.
fn record_aggregate_subbindings<'tcx>(
    kind: &PatKind<'tcx>,
    prefix: &[usize],
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, Vec<usize>>,
) -> LResult<()> {
    match kind {
        PatKind::Leaf { subpatterns } => {
            for fp in subpatterns.iter() {
                let mut path = prefix.to_vec();
                path.push(fp.field.as_usize());
                // A DEEPER aggregate sub-field (an aggregate-in-aggregate): recurse
                // so the binding carries the FULL deep path. The aggregate binder
                // bails loud at the depth-2 boundary, so a deep path reaches a
                // dedicated M5.7e guard rather than silently dropping a binder.
                if matches!(fp.pattern.kind, PatKind::Leaf { .. }) {
                    record_aggregate_subbindings(&fp.pattern.kind, &path, out)?;
                } else {
                    record_aggregate_binder_at(&fp.pattern.kind, path, out);
                }
            }
            Ok(())
        }
        other => bail(format!(
            "M5.7e: inline-aggregate field is not a tuple/struct Leaf ({:?})",
            std::mem::discriminant(other)
        )),
    }
}

/// Record a single aggregate sub-field binder at its full `path`. Peels `Deref`/
/// `DerefPattern` (a `box ref x` sub-binder) consistently with the trivial check, so
/// a binder the inline-aggregate check ALLOWED is never dropped.
fn record_aggregate_binder_at<'tcx>(
    kind: &PatKind<'tcx>,
    path: Vec<usize>,
    out: &mut std::collections::HashMap<rustc_middle::thir::LocalVarId, Vec<usize>>,
) {
    match kind {
        PatKind::Binding {
            var, subpattern, ..
        } => {
            out.insert(*var, path.clone());
            if let Some(sp) = subpattern {
                record_aggregate_binder_at(&sp.kind, path, out);
            }
        }
        PatKind::Deref { subpattern, .. } | PatKind::DerefPattern { subpattern, .. } => {
            record_aggregate_binder_at(&subpattern.kind, path, out)
        }
        // A wildcard sub-field binds nothing.
        _ => {}
    }
}

/// Human-readable THIR `ExprKind` variant name for diagnostics (instead of the
/// opaque `Discriminant(N)` that `std::mem::discriminant` prints).
fn expr_kind_name(kind: &ExprKind<'_>) -> &'static str {
    match kind {
        ExprKind::Scope { .. } => "Scope",
        ExprKind::If { .. } => "If",
        ExprKind::Call { .. } => "Call",
        ExprKind::ByUse { .. } => "ByUse",
        ExprKind::Deref { .. } => "Deref",
        ExprKind::Binary { .. } => "Binary",
        ExprKind::LogicalOp { .. } => "LogicalOp",
        ExprKind::Unary { .. } => "Unary",
        ExprKind::Cast { .. } => "Cast",
        ExprKind::Use { .. } => "Use",
        ExprKind::NeverToAny { .. } => "NeverToAny",
        ExprKind::PointerCoercion { .. } => "PointerCoercion",
        ExprKind::Loop { .. } => "Loop",
        ExprKind::Let { .. } => "Let",
        ExprKind::Match { .. } => "Match",
        ExprKind::Block { .. } => "Block",
        ExprKind::Assign { .. } => "Assign",
        ExprKind::AssignOp { .. } => "AssignOp",
        ExprKind::Field { .. } => "Field",
        ExprKind::Index { .. } => "Index",
        ExprKind::VarRef { .. } => "VarRef",
        ExprKind::UpvarRef { .. } => "UpvarRef",
        ExprKind::Borrow { .. } => "Borrow",
        ExprKind::RawBorrow { .. } => "RawBorrow",
        ExprKind::Break { .. } => "Break",
        ExprKind::Continue { .. } => "Continue",
        ExprKind::Return { .. } => "Return",
        ExprKind::Repeat { .. } => "Repeat",
        ExprKind::Array { .. } => "Array",
        ExprKind::Tuple { .. } => "Tuple",
        ExprKind::Adt(_) => "Adt",
        ExprKind::Closure(_) => "Closure",
        ExprKind::Literal { .. } => "Literal",
        ExprKind::NonHirLiteral { .. } => "NonHirLiteral",
        ExprKind::ZstLiteral { .. } => "ZstLiteral",
        ExprKind::NamedConst { .. } => "NamedConst",
        ExprKind::ConstParam { .. } => "ConstParam",
        ExprKind::StaticRef { .. } => "StaticRef",
        _ => "other",
    }
}

// Unused but documents the dialect dependency for downstream readers.
#[allow(dead_code)]
fn _doc_links() {
    let _ = (
        BinOp::Add,
        ICmpOp::Eq,
        EnumVariant {
            name: String::new(),
            fields: vec![],
            field_names: Vec::new(),
        },
    );
}
