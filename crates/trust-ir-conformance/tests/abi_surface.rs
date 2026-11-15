// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The v45 ABI surface (roadmap WS3.10 + WS3.11 + WS3.12 + WS3.14(b), the WS8.5
// "ABI" reservation group; reserved 79783f80).
//
// WS3.10 (F-053): `Function.section` / `Function.visibility` /
// `Function.retained`, mirroring `Global`'s v41 triple. Rust's default for a
// non-exported cross-CGU function is `(External, Hidden)`, which had no
// spelling before v45.
//
// Rows ported from the archived proof program
// (reports/2026-09-17-two-language-proof-program/):
// * `b4.uf12` / `consumer-trust-cg/07-function-visibility-section` — a
//   function symbol's visibility and section cannot be read from the module;
// (`b6.abi.no_function_visibility_slot` is flipped in place, in
// `two_language/field_ratchets.rs`.)
//
// WS3.11 (F-054): `ParamAttrs.ext` / `ParamAttrs.pass` and the `FuncAttrs.ret`
// return slot — the plan-of-record subset of the v2 `FnAbiDescriptor`.
// Rows ported:
// * `b6.uf09` / `consumer-trust-cg/05-rust-abi-pass-modes` — a stored module
//   could not say how a by-value aggregate crosses a call edge;
// * `consumer-trust-cg/06-arg-extension-attrs` — no `zeroext` / `signext`
//   and no return-attribute slot at all (DarwinPCS narrow ints).
// (`b6.abi.no_zeroext_signext_slot` and `b6.abi.no_pass_mode_slot` are
// flipped in place, in `two_language/field_ratchets.rs`.)

use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::{Linkage, Module, Visibility};
use trust_ir_build::{ModuleBuilder, TRUSTED_HANDLE_RUNTIMES, ValidationError, validate_module};

fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// The ABI-surface wire version, read from the writer rather than spelled.
fn abi_version() -> u32 {
    trust_ir::binary::ABI_SURFACE_FORMAT_VERSION
}

fn header(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[8..12].try_into().expect("a TrustIr header"))
}

/// Every lossless codec: binary, JSON, positional MessagePack, and the
/// canonical text (compared against `canonicalize`, which renumbers SSA
/// values exactly as the canonical printer does). Returns the four decoded
/// modules' equality verdicts, so a failure names the lossy codec.
fn four_formats(module: &Module) -> [(&'static str, bool); 4] {
    let bin = serialize_module(module).expect("serialize_module: test fixture");
    let binary = deserialize_module(&bin).is_ok_and(|back| &back == module)
        && serialize_module(&deserialize_module(&bin).unwrap())
            .expect("serialize_module: test fixture")
            == bin;
    let json = serde_json::to_string(module).expect("json");
    let json_ok = serde_json::from_str::<Module>(&json).is_ok_and(|back| &back == module);
    let mp = rmp_serde::to_vec(module).expect("msgpack");
    let mp_ok = rmp_serde::from_slice::<Module>(&mp).is_ok_and(|back| &back == module);
    let text = trust_ir::format::canonical(module);
    let text_ok = trust_ir::parser::parse_module(&text)
        .is_ok_and(|back| back == trust_ir::format::canonicalize(module));
    [
        ("binary", binary),
        ("json", json_ok),
        ("msgpack", mp_ok),
        ("text", text_ok),
    ]
}

fn assert_four_formats(module: &Module) {
    let verdicts = four_formats(module);
    assert!(
        verdicts.iter().all(|(_, ok)| *ok),
        "lossy codec(s): {verdicts:?}\n{}",
        trust_ir::format::canonical(module)
    );
}

/// `fn f() {}` with the given symbol attributes.
fn symbol_module(
    linkage: Linkage,
    visibility: Visibility,
    section: Option<&str>,
    retained: bool,
) -> Module {
    let mut mb = ModuleBuilder::new("abi_function_symbol");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = &mut module.functions[0];
    f.linkage = linkage;
    f.visibility = visibility;
    f.section = section.map(str::to_owned);
    f.retained = retained;
    module
}

// ---------------------------------------------------------------------------
// WS3.10 — function visibility / section / retention
// ---------------------------------------------------------------------------

/// Positive: rustc's `(External, Hidden)` function, with a section and
/// retention, validates, selects the v45 header, round-trips all four
/// formats, and every field is visible to the semantic diff.
#[test]
fn ws3_10_external_hidden_function_round_trips_all_four_formats_and_diffs() {
    let module = symbol_module(
        Linkage::External,
        Visibility::Hidden,
        Some("__TEXT,__text_hidden"),
        true,
    );
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(
        header(&serialize_module(&module).expect("serialize_module: test fixture")),
        abi_version()
    );
    assert_four_formats(&module);

    let text = trust_ir::format::canonical(&module);
    assert!(text.contains("; #visibility: hidden"), "{text}");
    assert!(
        text.contains("; #section: \"__TEXT,__text_hidden\""),
        "{text}"
    );
    assert!(text.contains("; #retained"), "{text}");

    // Each attribute is a reported, non-cosmetic change.
    for (field, mutated) in [
        (
            "visibility",
            symbol_module(
                Linkage::External,
                Visibility::Protected,
                Some("__TEXT,__text_hidden"),
                true,
            ),
        ),
        (
            "section",
            symbol_module(Linkage::External, Visibility::Hidden, None, true),
        ),
        (
            "retained",
            symbol_module(
                Linkage::External,
                Visibility::Hidden,
                Some("__TEXT,__text_hidden"),
                false,
            ),
        ),
    ] {
        let diff = trust_ir::diff::diff(&module, &mutated);
        let rendered = format!("{diff:?}");
        assert!(
            rendered.contains(&format!("field: \"{field}\"")),
            "{field}: {rendered}"
        );
    }
    assert!(trust_ir::diff::diff(&module, &module.clone()).is_empty());
}

/// A module with no symbol attribute keeps its pre-v45 header and bytes: the
/// v45 block is written only when used.
#[test]
fn ws3_10_default_symbol_attributes_keep_the_pre_v45_bytes() {
    let module = symbol_module(Linkage::External, Visibility::Default, None, false);
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert!(header(&bytes) < abi_version(), "{}", header(&bytes));
    assert_eq!(deserialize_module(&bytes).unwrap(), module);
}

/// Negative twin: the positive fixture with `Internal` linkage is refused as
/// a contradiction, and so is `(Private, Protected)`. Mutation control:
/// `(Internal, Default)` is admitted, so the refusal is the visibility rule.
#[test]
fn ws3_10_internal_hidden_function_is_refused_as_contradictory() {
    for (linkage, visibility) in [
        (Linkage::Internal, Visibility::Hidden),
        (Linkage::Private, Visibility::Protected),
    ] {
        let errors = validate_module(&symbol_module(linkage, visibility, None, false));
        assert!(
            matches!(
                errors.as_slice(),
                [ValidationError::ContradictoryFunctionVisibility { linkage: l, visibility: v, .. }]
                    if *l == linkage && *v == visibility
            ),
            "{linkage:?}/{visibility:?}: {errors:?}"
        );
    }
    assert_eq!(
        validate_module(&symbol_module(
            Linkage::Internal,
            Visibility::Default,
            None,
            true
        )),
        vec![]
    );
}

/// A section must name something: blank and NUL-bearing names are refused as
/// `InvalidFunctionSection`; a name carrying `"`, `\`, `;` and a newline is
/// ADMITTED (an object format may spell it) and must survive the text round
/// trip injectively.
#[test]
fn ws3_10_section_names_are_checked_and_round_trip_text_injectively() {
    for bad in ["", "   ", "sec\0tion"] {
        let errors = validate_module(&symbol_module(
            Linkage::External,
            Visibility::Default,
            Some(bad),
            false,
        ));
        assert!(
            matches!(
                errors.as_slice(),
                [ValidationError::InvalidFunctionSection { .. }]
            ),
            "{bad:?}: {errors:?}"
        );
    }

    let hostile = [
        "__TEXT,\"quoted\"",
        "back\\slash",
        ".text;#visibility: hidden",
        "line\nbreak ; #retained",
        "\"; #section: \"forged\"",
    ];
    let mut seen = std::collections::BTreeSet::new();
    for section in hostile {
        let module = symbol_module(Linkage::External, Visibility::Default, Some(section), false);
        assert_eq!(validate_module(&module), vec![], "{section:?}");
        assert_four_formats(&module);
        let back = trust_ir::parser::parse_module(&trust_ir::format::canonical(&module)).unwrap();
        let f = &back.functions[0];
        assert_eq!(f.section.as_deref(), Some(section));
        assert_eq!(
            f.visibility,
            Visibility::Default,
            "{section:?} forged a visibility"
        );
        assert!(!f.retained, "{section:?} forged retention");
        assert!(seen.insert(trust_ir::format::canonical(&module)));
    }
}

/// Mutation (guards an F-072 recurrence): a text round trip that DROPS the
/// symbol attributes must fail the conformance comparison. The printed
/// directives are deleted from the canonical text by hand; the parsed module
/// must then differ from `canonicalize(original)`, so a printer that stopped
/// emitting them could not pass `assert_four_formats`.
#[test]
fn ws3_10_a_text_round_trip_that_drops_the_fields_fails_conformance() {
    let module = symbol_module(
        Linkage::External,
        Visibility::Hidden,
        Some(".text.hot"),
        true,
    );
    let text = trust_ir::format::canonical(&module);
    for directive in ["#visibility:", "#section:", "#retained"] {
        let dropped: String = text
            .lines()
            .filter(|line| !line.contains(directive))
            .map(|line| format!("{line}\n"))
            .collect();
        assert_ne!(dropped, text, "{directive} was not printed");
        let back = trust_ir::parser::parse_module(&dropped).expect("still parses");
        assert_ne!(
            back,
            trust_ir::format::canonicalize(&module),
            "dropping {directive} went unnoticed"
        );
    }
}

/// A pinned handle entry point is the runtime's default-visible symbol in its
/// default section: a `Hidden` or sectioned declaration is refused as
/// `HandleEntryPointSignatureMismatch`, naming the attribute.
#[test]
fn ws3_10_a_pinned_entry_point_with_hidden_visibility_or_a_section_is_refused() {
    let pin = &TRUSTED_HANDLE_RUNTIMES[0];
    let build = || {
        let mut mb = ModuleBuilder::new_with_target_info("abi_pinned_entry", target());
        mb.declare_handle_runtime(pin).expect("pinned declarations");
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    assert_eq!(validate_module(&build()), vec![]);
    for (what, mutate) in [
        (
            "visibility hidden",
            (|f: &mut trust_ir::Function| f.visibility = Visibility::Hidden)
                as fn(&mut trust_ir::Function),
        ),
        ("section \".text.nat\"", |f| {
            f.section = Some(".text.nat".into())
        }),
    ] {
        let mut module = build();
        let symbol = module.functions[0].name.clone();
        mutate(&mut module.functions[0]);
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::HandleEntryPointSignatureMismatch { symbol: s, actual, .. }
                    if *s == symbol && actual.contains(what)
            )),
            "{what}: {errors:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// WS3.12 — calling conventions
// ---------------------------------------------------------------------------

/// `goal-g1-g8/g1-calling-conventions` (F-059): every foreign convention has
/// its own tag — none collapses to `C` — and each round-trips through all
/// four formats on a declaration and on a `CallIndirect` site. A v45
/// convention selects the v45 header; the five legacy ones do not.
#[test]
fn goal_g1_g8_g1_calling_conventions() {
    use trust_ir::CallingConv;
    use trust_ir::inst::Inst;

    let tokens: std::collections::BTreeSet<String> = CallingConv::ALL
        .iter()
        .map(std::string::ToString::to_string)
        .collect();
    assert_eq!(
        tokens.len(),
        CallingConv::ALL.len(),
        "two conventions share a token"
    );
    assert_eq!(CallingConv::ALL.len(), 12);

    for conv in CallingConv::ALL {
        let mut mb = ModuleBuilder::new_with_target_info("abi_calling_conv", target());
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.functions[0].calling_conv = conv;
        assert_eq!(validate_module(&module), vec![], "{conv}");
        assert_four_formats(&module);
        assert_eq!(
            header(&serialize_module(&module).expect("serialize_module: test fixture"))
                == abi_version(),
            conv.is_abi_surface(),
            "{conv}: header {} for is_abi_surface {}",
            header(&serialize_module(&module).expect("serialize_module: test fixture")),
            conv.is_abi_surface()
        );
        let text = trust_ir::format::canonical(&module);
        if conv != CallingConv::C {
            assert!(text.contains(&format!("{conv} fn @f")), "{text}");
        }

        // The same convention on an indirect call site.
        let mut indirect = module.clone();
        let block = &mut indirect.functions[0].blocks[0];
        block.body.insert(
            0,
            trust_ir::node::InstrNode::new(Inst::CallIndirect {
                callee: trust_ir::value::ValueId::new(9),
                sig: trust_ir::value::FuncTyId::new(0),
                args: vec![],
                calling_conv: conv,
            }),
        );
        let bytes = serialize_module(&indirect).expect("serialize_module: test fixture");
        let back = deserialize_module(&bytes).expect("indirect site decodes");
        assert_eq!(back, indirect, "{conv}: indirect site");
        assert_eq!(
            header(&bytes) == abi_version(),
            conv.is_abi_surface(),
            "{conv}: an indirect site selects v45 exactly when the convention is v45"
        );
    }
}

/// Negative twin: a v44 reader refuses a v45 convention tag rather than
/// reading it as a legacy one. Mutation control: the same blob relabelled
/// v45 decodes, so the refusal is the version gate, not the byte.
#[test]
fn ws3_12_a_pre_v45_header_refuses_a_v45_convention_tag() {
    let mut mb = ModuleBuilder::new_with_target_info("abi_calling_conv", target());
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.functions[0].calling_conv = trust_ir::CallingConv::SysV64;
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(header(&bytes), abi_version());

    let mut older = bytes.clone();
    older[8..12].copy_from_slice(&(abi_version() - 1).to_le_bytes());
    let refused = deserialize_module(&older);
    assert!(
        matches!(refused, Err(trust_ir::binary::BinaryError::InvalidTag(6))),
        "a v44 reader must refuse convention tag 6: {refused:?}"
    );
    assert_eq!(deserialize_module(&bytes).expect("v45 decodes"), module);
}

/// A pinned handle entry point is declared `C`. Any other convention —
/// `CUnwind` included, which differs from `C` only in unwind licence — is
/// refused as `HandleEntryPointSignatureMismatch`.
#[test]
fn ws3_12_a_pinned_entry_point_declared_c_unwind_is_refused() {
    let pin = &TRUSTED_HANDLE_RUNTIMES[0];
    let mut mb = ModuleBuilder::new_with_target_info("abi_pinned_conv", target());
    mb.declare_handle_runtime(pin).expect("pinned declarations");
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), vec![]);
    let symbol = module.functions[0].name.clone();
    module.functions[0].calling_conv = trust_ir::CallingConv::CUnwind;
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol: s, actual, .. }
                if *s == symbol && actual.contains("calling convention c_unwindcc")
        )),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// WS3.14(b) / WS2.22 — 128-bit enum tag reprs
// ---------------------------------------------------------------------------

/// A module carrying `enm`, on the canonical x86_64 target.
fn enum_module(enm: trust_ir::ty::EnumDef) -> Module {
    let mut module = Module::new("abi_enum_tag_repr");
    module.target_info = Some(target());
    module.enums.push(enm);
    module
        .add_type(trust_ir::ty::Ty::Enum(trust_ir::value::EnumId::new(0)))
        .expect("Module::add_type: test fixture");
    module
}

fn wide_enum(repr: trust_ir::ty::EnumTagRepr, discriminants: Vec<Option<i128>>) -> Module {
    use trust_ir::ty::{EnumDef, EnumVariant};
    let variant = |name: &str| EnumVariant {
        name: name.into(),
        fields: vec![],
        field_names: Vec::new(),
    };
    enum_module(
        EnumDef::new(
            trust_ir::value::EnumId::new(0),
            "Wide",
            vec![variant("A"), variant("B")],
        )
        .with_discriminants(discriminants)
        .with_repr(repr),
    )
}

/// `producer-rust-thir/enum-repr-128` (F-056(b)): a `#[repr(u128)]` /
/// `#[repr(i128)]` enum is expressible, validates, round-trips every format
/// at the v45 header, and has a computable layout whose tag lane is 16 bytes
/// with the TARGET's 128-bit alignment.
#[test]
fn producer_rust_thir_enum_repr_128() {
    use trust_ir::ty::{EnumTagRepr, Ty};

    let wide = i128::from(u64::MAX) + 1;
    for (repr, discriminants) in [
        (EnumTagRepr::U128, vec![Some(0), Some(wide)]),
        (EnumTagRepr::I128, vec![Some(-wide), Some(wide)]),
    ] {
        let module = wide_enum(repr, discriminants);
        assert_eq!(validate_module(&module), vec![], "{repr}");
        assert_eq!(
            header(&serialize_module(&module).expect("serialize_module: test fixture")),
            abi_version(),
            "{repr}"
        );
        assert_four_formats(&module);
        assert!(
            trust_ir::format::canonical(&module).contains(&format!("repr({repr})")),
            "{}",
            trust_ir::format::canonical(&module)
        );

        let layout = module
            .ty_layout_shape(&Ty::Enum(trust_ir::value::EnumId::new(0)))
            .expect("a 128-bit-tagged enum has a layout");
        let scalar = module
            .ty_layout_shape(&Ty::U128)
            .expect("the canonical target has a 128-bit scalar");
        assert_eq!(layout.align_bits, scalar.align_bits, "{repr}");
    }

    // Inference keeps the 64-bit cap: only the explicit hint selects a
    // 128-bit lane, so a module with no hint stays below v45.
    assert_eq!(EnumTagRepr::smallest_for(0, wide), None);
    let narrow = wide_enum(EnumTagRepr::U64, vec![Some(0), Some(1)]);
    assert!(
        header(&serialize_module(&narrow).expect("serialize_module: test fixture")) < abi_version()
    );

    // `U128` covers only the non-negative half: a discriminant an i128
    // cannot hold as a u128 is refused, never truncated.
    assert!(EnumTagRepr::U128.fits(i128::MAX));
    assert!(!EnumTagRepr::U128.fits(-1));
    assert!(EnumTagRepr::I128.fits(i128::MIN));
    let negative = wide_enum(EnumTagRepr::U128, vec![Some(-1), Some(0)]);
    assert!(
        negative
            .enums
            .first()
            .and_then(trust_ir::ty::EnumDef::canonical_tag_repr)
            .is_none(),
        "a negative discriminant has no u128 tag"
    );
}

/// Negative twin: a v44 reader refuses tag 9 rather than reading it as a
/// narrower lane. Mutation control: the same bytes at v45 decode, so the
/// refusal is the version gate.
#[test]
fn ws3_14_a_pre_v45_header_refuses_a_128_bit_tag_repr() {
    let wide = i128::from(u64::MAX) + 1;
    let module = wide_enum(trust_ir::ty::EnumTagRepr::U128, vec![Some(0), Some(wide)]);
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    let mut older = bytes.clone();
    older[8..12].copy_from_slice(&(abi_version() - 1).to_le_bytes());
    let refused = deserialize_module(&older);
    assert!(
        matches!(refused, Err(trust_ir::binary::BinaryError::InvalidTag(9))),
        "a v44 reader must refuse tag repr 9: {refused:?}"
    );
    assert_eq!(deserialize_module(&bytes).expect("v45 decodes"), module);
}

/// Mutation control for the size/align SPLIT: a direct `u128` tag at
/// `tag_offset` 8 in an align-16 enum is refused on x86_64. A validator that
/// took the alignment from an 8-byte half-word would accept it.
#[test]
fn ws3_14_a_128_bit_tag_is_aligned_by_the_target_not_by_half_its_size() {
    use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};

    let wide = i128::from(u64::MAX) + 1;
    let descriptor = |tag_offset: u64| EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset },
        size: 32,
        align: 16,
        variant_field_offsets: vec![vec![], vec![]],
    };

    let mut aligned = wide_enum(EnumTagRepr::U128, vec![Some(0), Some(wide)]);
    aligned.enums[0].layout = Some(descriptor(0));
    assert_eq!(validate_module(&aligned), vec![]);

    let mut misaligned = wide_enum(EnumTagRepr::U128, vec![Some(0), Some(wide)]);
    misaligned.enums[0].layout = Some(descriptor(8));
    let errors = validate_module(&misaligned);
    assert!(
        errors
            .iter()
            .any(|e| format!("{e}").contains("aligned to 16 bytes")),
        "a u128 tag at offset 8 must be refused: {errors:?}"
    );

    // And the alignment is not guessed: on a target with no canonical scalar
    // table the descriptor is refused rather than assumed — by the NAMED
    // WS2.22 refusal (`EnumTagTargetScalarLayoutUnavailable`), which is the
    // validator's projection of `LayoutError::TargetScalarLayoutUnavailable`.
    let mut foreign = aligned.clone();
    foreign.target_info.as_mut().unwrap().triple = "m68k-unknown-linux-gnu".into();
    let errors = validate_module(&foreign);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::EnumTagTargetScalarLayoutUnavailable { enum_id: 0, triple }
                if triple == "m68k-unknown-linux-gnu"
        )),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// WS3.11 — per-argument ABI facts
// ---------------------------------------------------------------------------

/// A declaration `fn(param) -> ret` with the given slot facts.
fn abi_decl(
    param: trust_ir::ty::Ty,
    param_attrs: trust_ir::ParamAttrs,
    ret: trust_ir::ty::Ty,
    ret_attrs: trust_ir::ParamAttrs,
    structs: Vec<trust_ir::ty::StructDef>,
) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("abi_param_facts", target());
    let ft = mb.add_func_type(vec![param], vec![ret]);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.structs.extend(structs);
    let mut decl = trust_ir::Function::new(
        trust_ir::FuncId::new(0),
        "c_abi_decl",
        ft,
        trust_ir::value::BlockId::new(0),
    );
    decl.attrs.params = vec![param_attrs];
    decl.attrs.ret = ret_attrs;
    module
        .try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    module
}

/// A `#[repr(C)]` struct of `lanes` `u64` fields, with offsets (so its
/// layout is computable for the validator). Field offsets are text-lossy
/// (WS4.2, until WS4.5), so a check that round-trips TEXT uses
/// [`lane_tuple`] instead.
fn lane_struct(lanes: usize) -> trust_ir::ty::StructDef {
    use trust_ir::ty::{FieldDef, StructDef, StructRepr, Ty};
    StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "Lanes".into(),
        fields: (0..lanes)
            .map(|i| FieldDef {
                name: String::new(),
                ty: Ty::U64,
                offset: Some((i as u64) * 8),
            })
            .collect(),
        size: Some((lanes as u64) * 8),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    }
}

/// A `(u64, ..)` tuple of `lanes` lanes: loss-free text, for the round-trip
/// checks. Its layout is computable once [`declare_tuple_layout`] adds the
/// v42 declared descriptor (itself text-carried).
fn lane_tuple(lanes: usize) -> trust_ir::ty::Ty {
    trust_ir::ty::Ty::Tuple(vec![trust_ir::ty::Ty::U64; lanes])
}

/// Declare the `#[repr(C)]`-shaped layout of [`lane_tuple`]`(lanes)` on
/// `module`, so `Cast` coverage and `Ignore` sizing can read it.
fn declare_tuple_layout(module: &mut Module, lanes: usize) {
    let tuple_type = module
        .add_type(lane_tuple(lanes))
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: (lanes as u64) * 8,
        align: 8,
        field_offsets: (0..lanes as u64).map(|i| i * 8).collect(),
    });
}

/// `b6.abi.no_zeroext_signext_slot` + `b6.abi.no_pass_mode_slot` (F-054):
/// positive fixture — a `u8`-returning C-ABI declaration with
/// `ret.ext = ZeroExt` and a `(u64, u64)` struct parameter passed as a
/// `Pair` validates, selects v45, and round-trips the lossless transports.
#[test]
fn ws3_11_zeroext_return_and_pair_parameter_validate_and_round_trip() {
    use trust_ir::ty::Ty;
    use trust_ir::{ArgExt, ParamAttrs, PassMode};

    let mut module = abi_decl(
        lane_tuple(2),
        ParamAttrs {
            pass: Some(PassMode::Pair),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            ..ParamAttrs::default()
        },
        vec![],
    );
    declare_tuple_layout(&mut module, 2);
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(
        header(&serialize_module(&module).expect("serialize_module: test fixture")),
        abi_version()
    );
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(deserialize_module(&bytes).expect("binary"), module);
    assert_eq!(
        serde_json::from_str::<Module>(&serde_json::to_string(&module).unwrap()).unwrap(),
        module
    );
    assert_eq!(
        rmp_serde::from_slice::<Module>(&rmp_serde::to_vec(&module).unwrap()).unwrap(),
        module
    );

    // The text form carries both facts, so a producer can read them back
    // out of a dump. (A struct's field offsets are F-072's text loss, which
    // is why the round-trip slot is a tuple; `Pair` on the struct is checked
    // by the golden `abi_param_facts` and the validator cases below.)
    let text = trust_ir::format::canonical_checked(&module).expect("loss-free text");
    assert!(text.contains("; #ret_attrs: zeroext"), "{text}");
    assert!(text.contains("; #param_attrs 0: pass=pair"), "{text}");
    let back = trust_ir::parser::parse_module(&text).expect("text parses");
    assert_eq!(back.functions[0].attrs.ret.ext, ArgExt::ZeroExt);
    assert_eq!(back.functions[0].attrs.params[0].pass, Some(PassMode::Pair));

    // An unrecorded fact keeps the pre-v45 bytes.
    let plain = abi_decl(
        lane_tuple(2),
        ParamAttrs::default(),
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    assert!(
        header(&serialize_module(&plain).expect("serialize_module: test fixture")) < abi_version()
    );

    // Every pass mode round-trips, `Cast` lanes included.
    for pass in [
        PassMode::Direct,
        PassMode::Cast {
            pieces: vec![Ty::U64, Ty::U64],
        },
    ] {
        let mut m = module.clone();
        m.functions[0].attrs.params[0].pass = Some(pass.clone());
        assert_eq!(validate_module(&m), vec![], "{pass:?}");
        assert_eq!(
            deserialize_module(&serialize_module(&m).expect("serialize_module: test fixture"))
                .expect("binary"),
            m,
            "{pass:?}"
        );
    }

    // `Indirect` is the PRE-LOWERED spelling: a `byval` pointer standing for
    // the aggregate (`byval` itself requires a pointer-typed parameter, the
    // v20 rule).
    let indirect = abi_decl(
        Ty::Ptr,
        ParamAttrs {
            byval: true,
            pass: Some(PassMode::Indirect { on_stack: true }),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    assert_eq!(validate_module(&indirect), vec![]);
    assert_eq!(
        deserialize_module(&serialize_module(&indirect).expect("serialize_module: test fixture"))
            .expect("binary"),
        indirect
    );
}

/// Negative twins, each one mutation from the positive fixture and refused
/// with the named reason: `zeroext` on a `U64` slot, `Pair` on a three-lane
/// struct, `Ignore` on a sized slot, `Indirect` on a scalar, and a fact on a
/// slot the signature does not have.
#[test]
fn ws3_11_misplaced_slot_facts_are_refused_by_name() {
    use trust_ir::ty::Ty;
    use trust_ir::{ArgExt, ParamAttrs, PassMode};

    let named = |errors: &[ValidationError], needle: &str| {
        errors.iter().any(|e| {
            matches!(
                e,
                ValidationError::InvalidAbiSlotFact { detail, .. } if detail.contains(needle)
            )
        })
    };

    // `zeroext` on a 64-bit return.
    let wide = abi_decl(
        Ty::Struct(trust_ir::value::StructId::new(0)),
        ParamAttrs {
            pass: Some(PassMode::Pair),
            ..ParamAttrs::default()
        },
        Ty::U64,
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            ..ParamAttrs::default()
        },
        vec![lane_struct(2)],
    );
    assert!(
        named(&validate_module(&wide), "narrower than 64 bits"),
        "{:?}",
        validate_module(&wide)
    );

    // `Pair` on a three-lane struct.
    let three = abi_decl(
        Ty::Struct(trust_ir::value::StructId::new(0)),
        ParamAttrs {
            pass: Some(PassMode::Pair),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs::default(),
        vec![lane_struct(3)],
    );
    assert!(named(&validate_module(&three), "two-scalar-lane"));

    // `Ignore` on a sized slot, and `Indirect` on a scalar with no `byval`.
    for (pass, needle) in [
        (PassMode::Ignore, "zero-sized"),
        (PassMode::Indirect { on_stack: false }, "aggregate slot"),
    ] {
        let module = abi_decl(
            Ty::U32,
            ParamAttrs {
                pass: Some(pass.clone()),
                ..ParamAttrs::default()
            },
            Ty::U8,
            ParamAttrs::default(),
            vec![],
        );
        assert!(
            named(&validate_module(&module), needle),
            "{pass:?}: {:?}",
            validate_module(&module)
        );
    }

    // `byval` / `sret` and a non-`indirect` pass mode are two spellings of
    // one claim that disagree: half an ABI, refused on both pointer roles.
    for (byval, sret) in [(true, false), (false, true)] {
        let split = abi_decl(
            Ty::Ptr,
            ParamAttrs {
                byval,
                sret,
                pass: Some(PassMode::Direct),
                ..ParamAttrs::default()
            },
            Ty::U8,
            ParamAttrs::default(),
            vec![],
        );
        assert!(
            named(&validate_module(&split), "crosses through memory"),
            "byval={byval} sret={sret}: {:?}",
            validate_module(&split)
        );
    }

    // A fact on a slot the signature does not have.
    let mut extra = abi_decl(
        Ty::U32,
        ParamAttrs::default(),
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    extra.functions[0].attrs.params.push(ParamAttrs {
        ext: ArgExt::SignExt,
        ..ParamAttrs::default()
    });
    assert!(named(&validate_module(&extra), "does not exist"));

    // A return-slot fact with no single returned value.
    let mut void = abi_decl(
        Ty::U32,
        ParamAttrs::default(),
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    let void_ft = void
        .add_func_type(trust_ir::ty::FuncTy {
            params: vec![Ty::U32],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    void.functions[0].ty = void_ft;
    void.functions[0].attrs.ret = ParamAttrs {
        ext: ArgExt::ZeroExt,
        ..ParamAttrs::default()
    };
    assert!(named(&validate_module(&void), "exactly one returned value"));

    // Mutation control: each of those slots is admitted with the RIGHT fact,
    // so the rule — not the shape of the fixture — caused every refusal.
    let ok = abi_decl(
        Ty::U32,
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            pass: Some(PassMode::Direct),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs {
            ext: ArgExt::SignExt,
            ..ParamAttrs::default()
        },
        vec![],
    );
    assert_eq!(validate_module(&ok), vec![]);
}

/// Mutation control for `Cast`: lanes that do not cover the slot, and a lane
/// that is not a closed scalar, are refused; the covering list is admitted.
#[test]
fn ws3_11_cast_lanes_must_be_closed_scalars_that_cover_the_slot() {
    use trust_ir::ty::Ty;
    use trust_ir::{ParamAttrs, PassMode};

    let with_lanes = |pieces: Vec<Ty>| {
        abi_decl(
            Ty::Struct(trust_ir::value::StructId::new(0)),
            ParamAttrs {
                pass: Some(PassMode::Cast { pieces }),
                ..ParamAttrs::default()
            },
            Ty::U8,
            ParamAttrs::default(),
            vec![lane_struct(2)],
        )
    };
    // 16-byte struct, one 8-byte lane: too small.
    let short = with_lanes(vec![Ty::U64]);
    let errors = validate_module(&short);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidAbiSlotFact { detail, .. } if detail.contains("does not cover")
        )),
        "{errors:?}"
    );
    // A lane that is not a closed scalar.
    let aggregate_lane = with_lanes(vec![Ty::Struct(trust_ir::value::StructId::new(0))]);
    let errors = validate_module(&aggregate_lane);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidAbiSlotFact { detail, .. } if detail.contains("closed scalar")
        )),
        "{errors:?}"
    );
    // The covering list is admitted.
    assert_eq!(validate_module(&with_lanes(vec![Ty::U64, Ty::U64])), vec![]);
}

/// Wire checklist item 7 (WS3.11): `read_param_attrs` REFUSES a flag bit that
/// is not allocated at the blob's version instead of dropping it. Before the
/// fix a pre-v45 blob with bit 5 set decoded with the bit gone, so a v45
/// extension smuggled into an older blob read as "no extension recorded".
#[test]
fn ws3_11_an_unallocated_parameter_flag_bit_is_refused_at_the_blobs_version() {
    use trust_ir::ty::Ty;
    use trust_ir::{ArgExt, ParamAttrs};

    let module = abi_decl(
        Ty::U32,
        ParamAttrs {
            nonnull: true,
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    assert!(
        header(&serialize_module(&module).expect("serialize_module: test fixture")) < abi_version()
    );

    // The same module with `zeroext`: it selects v45 and decodes.
    let mut extended = module.clone();
    extended.functions[0].attrs.params[0].ext = ArgExt::ZeroExt;
    let v45 = serialize_module(&extended).expect("serialize_module: test fixture");
    assert_eq!(header(&v45), abi_version());
    assert_eq!(deserialize_module(&v45).expect("v45 decodes"), extended);

    // Relabelled to v44, the extension bit is no longer allocated: refused,
    // never silently dropped.
    let mut older = v45.clone();
    older[8..12].copy_from_slice(&(abi_version() - 1).to_le_bytes());
    let refused = deserialize_module(&older);
    assert!(
        matches!(&refused, Err(trust_ir::binary::BinaryError::InvalidData(msg))
            if msg.contains("not allocated at wire version")),
        "{refused:?}"
    );

    // Both extension bits at once is not a third extension.
    // The parameter's flags byte is `nonnull | zeroext`; setting the second
    // extension bit too is not a third extension.
    let mut both = v45.clone();
    let nonnull_zeroext = 0b010_0001u8;
    let index = both
        .iter()
        .position(|byte| *byte == nonnull_zeroext)
        .expect("the parameter flags byte is in the image");
    both[index] = nonnull_zeroext | 0b100_0000;
    let refused = deserialize_module(&both);
    assert!(
        matches!(&refused, Err(trust_ir::binary::BinaryError::InvalidData(msg))
            if msg.contains("both `zeroext` and `signext`")),
        "{refused:?}"
    );
}

// ---------------------------------------------------------------------------
// Review (WS3.10 lane): adversarial shapes the implementer did not write.
// ---------------------------------------------------------------------------

/// A `#[repr(C)]` struct of `lanes` `u64` fields with a zero-sized `()`
/// field inserted at `zst_at`, for the lane-counting cases below.
fn lane_struct_with_zst(lanes: usize, zst_at: usize) -> trust_ir::ty::StructDef {
    use trust_ir::ty::{FieldDef, Ty};
    let mut def = lane_struct(lanes);
    def.fields.insert(
        zst_at,
        FieldDef {
            name: String::new(),
            ty: Ty::Unit,
            offset: Some((zst_at as u64) * 8),
        },
    );
    def
}

/// Review: a LEGITIMATE module was refused. `indirect` in its BY-VALUE
/// spelling — the aggregate itself in the signature, no `byval`, which is
/// exactly what rustc's `FnAbi` stamps for `fn(Big)` / `fn() -> Big` on
/// SysV x86_64 and AAPCS64 — validated nowhere: on a parameter the rule
/// demanded `byval`, which the v20 rule admits only on a POINTER slot, and on
/// the return slot it demanded an `sret` parameter, which the v20 rule admits
/// only with an EMPTY return list while return-slot facts need exactly one
/// return. Both spellings now validate and round-trip; the pre-lowered
/// spelling (`byval` pointer) still does; and `indirect` on a plain scalar
/// is still refused, so the loosening is exactly the aggregate case.
#[test]
fn review_indirect_is_admitted_in_its_by_value_spelling_on_both_slots() {
    use trust_ir::ty::Ty;
    use trust_ir::{ParamAttrs, PassMode};

    // Three lanes, as a `#[repr(C)]` struct (validator-only: field offsets
    // are text-lossy) and as a tuple (loss-free, for the four formats).
    let big_struct = || Ty::Struct(trust_ir::value::StructId::new(0));

    // Parameter: `fn(Big) -> u8`, the aggregate passed through memory.
    let by_value_param = abi_decl(
        big_struct(),
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs::default(),
        vec![lane_struct(3)],
    );
    assert_eq!(validate_module(&by_value_param), vec![]);
    let by_value_param = abi_decl(
        lane_tuple(3),
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: true }),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    assert_eq!(validate_module(&by_value_param), vec![]);
    assert_four_formats(&by_value_param);

    // Return slot: `fn(u8) -> Big`, the aggregate returned through memory.
    let by_value_return = abi_decl(
        Ty::U8,
        ParamAttrs::default(),
        big_struct(),
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..ParamAttrs::default()
        },
        vec![lane_struct(3)],
    );
    assert_eq!(validate_module(&by_value_return), vec![]);
    let by_value_return = abi_decl(
        Ty::U8,
        ParamAttrs::default(),
        lane_tuple(3),
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..ParamAttrs::default()
        },
        vec![],
    );
    assert_eq!(validate_module(&by_value_return), vec![]);
    assert_four_formats(&by_value_return);

    // Mutation controls: the same facts on a scalar slot stay refused with
    // the named reason, so the rule (not the fixture) admits the aggregate.
    let scalar_param = abi_decl(
        Ty::U32,
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    let errors = validate_module(&scalar_param);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidAbiSlotFact { slot, detail, .. }
                if slot == "parameter 0" && detail.contains("aggregate slot")
        )),
        "{errors:?}"
    );
    let scalar_return = abi_decl(
        Ty::U8,
        ParamAttrs::default(),
        Ty::U64,
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..ParamAttrs::default()
        },
        vec![],
    );
    let errors = validate_module(&scalar_return);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidAbiSlotFact { slot, detail, .. }
                if slot == "return slot" && detail.contains("aggregate slot")
        )),
        "{errors:?}"
    );
}

/// Review: a FALSE claim was accepted. The return slot carries `ext`, `pass`
/// and the returned-pointer facts; `byval` / `sret` / `readonly` describe a
/// PARAMETER (`sret` is the pre-lowered spelling of an indirect return and
/// lives on the parameter that carries the slot), and `indirect(true)`
/// (`on_stack`) describes an argument's home. Each is refused by name, and
/// the admissible return facts beside them are not.
#[test]
fn review_return_slot_refuses_parameter_only_attributes() {
    use trust_ir::ty::Ty;
    use trust_ir::{ArgExt, ParamAttrs, PassMode};

    let named = |errors: &[ValidationError], needle: &str| {
        errors.iter().any(|e| {
            matches!(
                e,
                ValidationError::InvalidAbiSlotFact { slot, detail, .. }
                    if slot == "return slot" && detail.contains(needle)
            )
        })
    };
    let returning = |ret: Ty, attrs: ParamAttrs, structs| {
        abi_decl(Ty::U8, ParamAttrs::default(), ret, attrs, structs)
    };

    for (attrs, needle) in [
        (
            ParamAttrs {
                sret: true,
                ..ParamAttrs::default()
            },
            "`sret` is a parameter attribute",
        ),
        (
            ParamAttrs {
                byval: true,
                ..ParamAttrs::default()
            },
            "`byval` is a parameter attribute",
        ),
        (
            ParamAttrs {
                readonly: true,
                ..ParamAttrs::default()
            },
            "`readonly` is a parameter attribute",
        ),
    ] {
        let module = returning(Ty::Ptr, attrs.clone(), vec![]);
        assert!(
            named(&validate_module(&module), needle),
            "{attrs:?}: {:?}",
            validate_module(&module)
        );
    }
    let on_stack = returning(
        Ty::Struct(trust_ir::value::StructId::new(0)),
        ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: true }),
            ..ParamAttrs::default()
        },
        vec![lane_struct(3)],
    );
    assert!(named(&validate_module(&on_stack), "on_stack"));

    // Mutation control: the returned-pointer facts and an extension are the
    // admissible return-slot vocabulary.
    let pointer = returning(
        Ty::Ptr,
        ParamAttrs {
            nonnull: true,
            noalias: true,
            align: Some(8),
            dereferenceable: Some(16),
            pass: Some(PassMode::Direct),
            ..ParamAttrs::default()
        },
        vec![],
    );
    assert_eq!(validate_module(&pointer), vec![]);
    assert_four_formats(&pointer);
    let narrow = returning(
        Ty::I16,
        ParamAttrs {
            ext: ArgExt::SignExt,
            ..ParamAttrs::default()
        },
        vec![],
    );
    assert_eq!(validate_module(&narrow), vec![]);
}

/// Review: `pair` counted FIELDS, not ABI lanes, so `struct { u64, () }` and
/// `struct { (), () }` were admitted as pairs (a zero-sized field occupies
/// no lane — rustc classifies the first as `Scalar`) while
/// `struct { u64, (), u64 }`, a genuine `ScalarPair`, was refused. Lanes are
/// counted now. Likewise a `cast` lane of `()` has no width and covered a
/// zero-sized slot by arithmetic alone.
#[test]
fn review_pair_and_cast_count_abi_lanes_not_fields() {
    use trust_ir::ty::Ty;
    use trust_ir::{ParamAttrs, PassMode};

    let paired = |structs| {
        abi_decl(
            Ty::Struct(trust_ir::value::StructId::new(0)),
            ParamAttrs {
                pass: Some(PassMode::Pair),
                ..ParamAttrs::default()
            },
            Ty::U8,
            ParamAttrs::default(),
            structs,
        )
    };
    let refused_as_pair = |module: &Module| {
        validate_module(module).iter().any(|e| {
            matches!(
                e,
                ValidationError::InvalidAbiSlotFact { detail, .. }
                    if detail.contains("two-scalar-lane")
            )
        })
    };

    // Two lanes around a zero-sized field: a pair.
    let two_lanes_zst = paired(vec![lane_struct_with_zst(2, 1)]);
    assert_eq!(validate_module(&two_lanes_zst), vec![]);
    // One lane plus a zero-sized field: not a pair.
    assert!(refused_as_pair(&paired(vec![lane_struct_with_zst(1, 1)])));
    // No lanes at all (`struct { (), () }`): not a pair.
    let mut none = lane_struct_with_zst(0, 0);
    none.fields.push(none.fields[0].clone());
    none.align = Some(1);
    assert!(refused_as_pair(&paired(vec![none])));

    // A `cast` lane with no width.
    let mut zero_width = paired(vec![lane_struct(2)]);
    zero_width.functions[0].attrs.params[0].pass = Some(PassMode::Cast {
        pieces: vec![Ty::Unit, Ty::U64, Ty::U64],
    });
    let errors = validate_module(&zero_width);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidAbiSlotFact { detail, .. } if detail.contains("has no width")
        )),
        "{errors:?}"
    );
}

/// Review: the text form spells retention as `; #retained: true` — one
/// `<word>:` grammar for every directive (WS4.2's table) — and the strict
/// parser refuses the bare `; #retained` a pre-table printer would have
/// written, rather than reading it as a plain comment and DROPPING the fact.
#[test]
fn review_bare_retained_directive_is_refused_not_dropped() {
    let module = symbol_module(Linkage::External, Visibility::Default, None, true);
    let text = trust_ir::format::canonical(&module);
    assert!(text.contains("; #retained: true"), "{text}");
    let back = trust_ir::parser::parse_module(&text).expect("the printed form parses");
    assert!(back.functions[0].retained);

    let bare = text.replace("; #retained: true", "; #retained");
    assert_ne!(bare, text);
    let refused = trust_ir::parser::parse_module(&bare);
    assert!(
        refused.is_err(),
        "a bare `#retained` must be refused: {refused:?}"
    );
}

/// Review: a FALSE claim was accepted by the TEXT reader. The binary reader
/// refuses a parameter whose flags set both extension bits ("not a third
/// extension"), but the text grammar read `zeroext signext` — and
/// `pass=pair pass=direct`, a second `#ret_attrs:` line, and a second
/// `#visibility:` / `#retained:` directive — by letting the LATER token win.
/// A text that states two facts about one slot is now refused with the
/// restatement named; the single statement (mutation control) still parses.
#[test]
fn review_text_that_restates_a_slot_fact_or_symbol_directive_is_refused() {
    use trust_ir::ty::Ty;
    use trust_ir::{ArgExt, ParamAttrs, PassMode};

    let refused_with = |text: &str, needle: &str| {
        let parsed = trust_ir::parser::parse_module(text);
        assert!(
            matches!(&parsed, Err(err) if err.to_string().contains(needle)),
            "expected a refusal naming {needle:?}, got {parsed:?}\n{text}"
        );
    };
    let parses = |text: &str| {
        trust_ir::parser::parse_module(text).expect("the single statement parses");
    };

    // One slot line, two extensions / two pass modes.
    let slot = abi_decl(
        Ty::U16,
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            pass: Some(PassMode::Direct),
            ..ParamAttrs::default()
        },
        Ty::U8,
        ParamAttrs {
            ext: ArgExt::ZeroExt,
            ..ParamAttrs::default()
        },
        vec![],
    );
    assert_eq!(validate_module(&slot), vec![]);
    let text = trust_ir::format::canonical(&slot);
    let param_line = "; #param_attrs 0: zeroext pass=direct";
    assert!(text.contains(param_line), "{text}");
    parses(&text);
    refused_with(
        &text.replace(param_line, "; #param_attrs 0: zeroext signext pass=direct"),
        "`signext` restates the slot's extension",
    );
    refused_with(
        &text.replace(
            param_line,
            "; #param_attrs 0: zeroext pass=direct pass=pair",
        ),
        "`pass` restates the slot's pass mode",
    );
    // The same word twice is a restatement too, not an idempotent no-op.
    refused_with(
        &text.replace(param_line, "; #param_attrs 0: zeroext zeroext pass=direct"),
        "`zeroext` restates the slot's extension",
    );
    // Two return-slot lines.
    let ret_line = "    ; #ret_attrs: zeroext\n";
    assert!(text.contains(ret_line), "{text}");
    refused_with(
        &text.replace(
            ret_line,
            "    ; #ret_attrs: zeroext\n    ; #ret_attrs: signext\n",
        ),
        "duplicate #ret_attrs directive",
    );

    // Two symbol directives: `hidden` then `default` is a contradiction, not
    // a correction; `retained` twice likewise.
    let symbol = symbol_module(Linkage::External, Visibility::Hidden, None, true);
    let text = trust_ir::format::canonical(&symbol);
    let vis_line = "    ; #visibility: hidden\n";
    let ret_line = "    ; #retained: true\n";
    assert!(text.contains(vis_line) && text.contains(ret_line), "{text}");
    parses(&text);
    refused_with(
        &text.replace(
            vis_line,
            "    ; #visibility: hidden\n    ; #visibility: default\n",
        ),
        "duplicate #visibility directive",
    );
    refused_with(
        &text.replace(ret_line, "    ; #retained: true\n    ; #retained: false\n"),
        "duplicate #retained directive",
    );
}

/// Review: a WRONG MODULE IDENTITY would let one image stand for another.
/// Every v45 fact — the symbol triple, the calling convention, and each slot
/// fact on a parameter and on the return slot — must move BOTH module
/// identities: `stable_digest` (what an import authenticates) and
/// `executable_content_digest_v1` (what a codegen license is a verdict
/// about). If the executable-content projection dropped any of them, a
/// license earned by a `zeroext`-returning image would license the
/// un-extended one, whose caller reads garbage in the high bits.
#[test]
fn review_every_v45_fact_moves_both_module_identities() {
    use std::collections::BTreeSet;
    use trust_ir::ty::Ty;
    use trust_ir::{ArgExt, ParamAttrs, PassMode};

    let base = abi_decl(
        Ty::U16,
        ParamAttrs::default(),
        Ty::U8,
        ParamAttrs::default(),
        vec![],
    );
    assert_eq!(validate_module(&base), vec![]);
    let mutants: Vec<(&str, Module)> = vec![
        ("param ext", {
            let mut m = base.clone();
            m.functions[0].attrs.params[0].ext = ArgExt::ZeroExt;
            m
        }),
        ("param ext (other)", {
            let mut m = base.clone();
            m.functions[0].attrs.params[0].ext = ArgExt::SignExt;
            m
        }),
        ("param pass", {
            let mut m = base.clone();
            m.functions[0].attrs.params[0].pass = Some(PassMode::Direct);
            m
        }),
        ("ret ext", {
            let mut m = base.clone();
            m.functions[0].attrs.ret.ext = ArgExt::ZeroExt;
            m
        }),
        ("ret pass", {
            let mut m = base.clone();
            m.functions[0].attrs.ret.pass = Some(PassMode::Direct);
            m
        }),
        ("calling conv", {
            let mut m = base.clone();
            m.functions[0].calling_conv = trust_ir::CallingConv::CUnwind;
            m
        }),
        ("visibility", {
            let mut m = base.clone();
            m.functions[0].visibility = Visibility::Hidden;
            m
        }),
        ("section", {
            let mut m = base.clone();
            m.functions[0].section = Some(".text.hot".into());
            m
        }),
        ("retained", {
            let mut m = base.clone();
            m.functions[0].retained = true;
            m
        }),
    ];
    let mut stable = BTreeSet::new();
    let mut executable = BTreeSet::new();
    stable.insert(format!("{:?}", base.stable_digest()));
    executable.insert(format!("{:?}", base.executable_content_digest_v1()));
    for (what, mutant) in &mutants {
        assert_eq!(validate_module(mutant), vec![], "{what}");
        assert_ne!(
            mutant.stable_digest(),
            base.stable_digest(),
            "{what} does not move stable_digest"
        );
        assert_ne!(
            mutant.executable_content_digest_v1(),
            base.executable_content_digest_v1(),
            "{what} does not move executable_content_digest_v1"
        );
        stable.insert(format!("{:?}", mutant.stable_digest()));
        executable.insert(format!("{:?}", mutant.executable_content_digest_v1()));
    }
    // Pairwise distinct, too: no two facts collide onto one identity.
    assert_eq!(stable.len(), mutants.len() + 1);
    assert_eq!(executable.len(), mutants.len() + 1);
}

/// Review: a LEGITIMATE module was refused. rustc's `FnAbi` stamps
/// `PassMode::Pair` on every `ScalarPair` argument, and an ENUM with a tag
/// lane and a one-lane payload (`Option<u64>`, `Result<u32, u32>`) or a
/// niche-encoded enum whose dataful variant is two lanes
/// (`Option<(&T, u8)>`) IS `ScalarPair` — as is a struct whose single field
/// is a two-lane tuple. `Pair` on an enum was refused outright, so a
/// producer stamping from `FnAbi` had to decline every such argument. Lanes
/// are now counted under the enum's tag encoding. The mutation controls keep
/// the refusal where rustc says memory: a tag beside a two-lane payload, a
/// fieldless enum (one lane), three lanes through nesting.
#[test]
fn review_pair_counts_an_enums_lanes_under_its_tag_encoding() {
    use trust_ir::ty::{
        EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, Ty,
    };
    use trust_ir::value::EnumId;
    use trust_ir::{ParamAttrs, PassMode};

    let variant = |name: &str, fields: Vec<Ty>| EnumVariant {
        name: name.into(),
        fields,
        field_names: Vec::new(),
    };
    let paired = |param: Ty, enums: Vec<EnumDef>| {
        let mut module = abi_decl(
            param,
            ParamAttrs {
                pass: Some(PassMode::Pair),
                ..ParamAttrs::default()
            },
            Ty::U8,
            ParamAttrs::default(),
            vec![],
        );
        module.enums.extend(enums);
        module
    };
    let refused_as_pair = |module: &Module| {
        validate_module(module).iter().any(|e| {
            matches!(
                e,
                ValidationError::InvalidAbiSlotFact { slot, detail, .. }
                    if slot == "parameter 0" && detail.contains("two-scalar-lane")
            )
        })
    };
    let enum_ty = Ty::Enum(EnumId::new(0));

    // `Option<u64>`: tag lane + one payload lane, canonical (tagged) layout.
    let option_u64 = paired(
        enum_ty.clone(),
        vec![EnumDef::new(
            EnumId::new(0),
            "OptionU64",
            vec![variant("None", vec![]), variant("Some", vec![Ty::U64])],
        )],
    );
    assert_eq!(validate_module(&option_u64), vec![]);
    assert_four_formats(&option_u64);
    // `Result<u32, u32>`: every variant one lane.
    let result = paired(
        enum_ty.clone(),
        vec![EnumDef::new(
            EnumId::new(0),
            "ResultU32",
            vec![variant("Ok", vec![Ty::U32]), variant("Err", vec![Ty::U32])],
        )],
    );
    assert_eq!(validate_module(&result), vec![]);
    // Niche-encoded `Option<(&i64, u8)>`: the dataful variant's two lanes,
    // the other variant empty (rustc's `others_zst`).
    let mut niche = EnumDef::new(
        EnumId::new(0),
        "OptionRefU8",
        vec![
            variant("Some", vec![Ty::Ref(Box::new(Ty::I64)), Ty::U8]),
            variant("None", vec![]),
        ],
    );
    niche.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U64,
        },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![0, 8], vec![]],
    });
    let niche = paired(enum_ty.clone(), vec![niche]);
    assert_eq!(validate_module(&niche), vec![]);
    // A struct-like nesting: `((u32, u32),)` is two lanes.
    let nested = paired(Ty::Tuple(vec![Ty::Tuple(vec![Ty::U32, Ty::U32])]), vec![]);
    assert_eq!(validate_module(&nested), vec![]);
    assert_four_formats(&nested);

    // Mutation controls.
    // A tag beside a two-lane payload is a memory aggregate.
    assert!(refused_as_pair(&paired(
        enum_ty.clone(),
        vec![EnumDef::new(
            EnumId::new(0),
            "Wide",
            vec![variant("A", vec![]), variant("B", vec![Ty::U32, Ty::U32])],
        )],
    )));
    // A fieldless enum is one lane (the tag).
    assert!(refused_as_pair(&paired(
        enum_ty.clone(),
        vec![EnumDef::new(
            EnumId::new(0),
            "Fieldless",
            vec![variant("A", vec![]), variant("B", vec![])],
        )],
    )));
    // Three lanes through nesting.
    assert!(refused_as_pair(&paired(
        Ty::Tuple(vec![Ty::U32, Ty::Tuple(vec![Ty::U32, Ty::U32])]),
        vec![],
    )));
    // A niche enum whose OTHER variant carries a lane is not the dataful
    // variant's shape (rustc: `others_zst` fails, memory aggregate).
    let mut both_dataful = EnumDef::new(
        EnumId::new(0),
        "BothDataful",
        vec![
            variant("Some", vec![Ty::Ref(Box::new(Ty::I64)), Ty::U8]),
            variant("Other", vec![Ty::U8]),
        ],
    );
    both_dataful.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U64,
        },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![0, 8], vec![8]],
    });
    assert!(refused_as_pair(&paired(enum_ty, vec![both_dataful])));
}
