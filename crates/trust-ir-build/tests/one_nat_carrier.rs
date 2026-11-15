// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.4 (F-047, the carrier seam; DG-45): one `Nat` carrier across producers.
//
// Measured at `5b45b83b8` (audit c11, item 5), one two-language module
// carried THREE spellings of `trust_bignum::Nat`: the Rust lane's
// `Struct("trust_bignum::Nat")` (a by-value `{limbs: Vec<u64>}` reached
// through `Nat::from_u64`), the Clean general lane's boxed `Ptr`, and the
// pinned `Ty::Handle` — three unrelated types, one runtime, no rule between
// them. `docs/SPEC_RATIFICATIONS.md` §7 now ratifies ONE carrier: a value of
// a pinned runtime's type crosses every producer boundary as `Ty::Handle` and
// nothing else. The validator half of that ruling is a rule that only ever
// adds refusals: in a module whose handle census is non-empty, a `StructDef`
// / `EnumDef` / `RecordDef` whose `name` equals a pinned row's `runtime` path
// is `ValidationError::HandleRuntimeSpelledStructurally { def, runtime }`.
//
// What this file pins, and why each is a separate statement:
//
// * POSITIVE — a handle module plus an unrelated struct `Acct` validates `[]`
//   on the plain and the codegen lane: the rule is name-keyed, not
//   "no structs beside a handle".
// * NEGATIVE TWINS — the same module plus a `StructDef` (then an `EnumDef`,
//   then a `RecordDef`) named `trust_bignum::Nat` is EXACTLY ONE
//   `HandleRuntimeSpelledStructurally`, naming the definition and the runtime,
//   on every lane; the `Display` text says "second spelling".
// * ADVERSARIAL — a handle-free Rust module carrying that struct still
//   validates: a Rust crate that uses `trust_bignum::Nat` natively is not a
//   boundary. And the boundary is the CENSUS: a handle that occurs only in an
//   unused type-table row already makes the module one.
// * MUTATION CONTROLS — the rule is name-EXACT (a case-fold, a prefix, a
//   suffix, a leading `::` all validate: the rule catches the measured
//   spelling, not a renamed struct, which §7 records as the producer's
//   guarantee); and the REGISTRY ROW is what names the runtime: under a
//   registry that pins `other::Big` and not `trust_bignum::Nat`, the refusal
//   follows the row.
//
// * THE SPELLING THE VALIDATOR CANNOT SEE — the Clean `Ptr` spelling
//   (`l_Nat_sub` over a boxed object) cannot be detected here, because a `Ptr`
//   names no type; it is a WS6 producer obligation (F-102), recorded in §7
//   beside this rule. The archived self-declared row
//   `trust-ir-self-declared/clean-objects-stay-ptr` is ported as a test that
//   pins both halves: the boxed spelling validates beside the handle (no
//   refusal is ever a guarantee), and it still cannot meet the handle
//   (`Ptr != Handle` at the pinned call is `CallArgTypeMismatch`).

use trust_ir::proof::RejectingModuleProofAuthority;
use trust_ir::ty::{EnumDef, EnumVariant, RecordDef};
use trust_ir::value::{EnumId, RecordId, StructId};
use trust_ir::{
    BodyGate, CallingConv, FieldDef, Module, Producer, StructDef, StructPassingPolicy, StructRepr,
    TargetInfo, Ty,
};
use trust_ir::{Endianness, ModuleImport};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    HandleEntryPoint, HandleRegistry, HandleRuntimeDecls, HandleRuntimePin, ModuleBuilder,
    ModuleSet, PinnedTy, TRUSTED_HANDLE_RUNTIMES, validate_linked_module, validate_module,
    validate_module_for_codegen, validate_module_with_authority,
    validate_module_with_handle_registry,
};

const NAT_RUNTIME: &str = "trust_bignum::Nat";

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn nat_pin() -> &'static HandleRuntimePin {
    TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == NAT_RUNTIME)
        .expect("the pinned table carries trust_bignum::Nat")
}

fn gate() -> BodyGate {
    BodyGate::Gated {
        authority: "ws3-4-test".into(),
        evidence: None,
    }
}

/// A second, test-only runtime row: `("Big", "other::Big")` with a
/// constructor and a consumer — the mutation control's registry.
const ROW_BIG: HandleRuntimePin = HandleRuntimePin {
    name: "Big",
    runtime: "other::Big",
    calling_conv: CallingConv::C,
    entry_points: &[
        HandleEntryPoint {
            role: "mk",
            symbol: "other_big_mk",
            def_path: "other::Big::mk",
            params: &[PinnedTy::Scalar(Ty::U64)],
            returns: &[PinnedTy::Handle],
        },
        HandleEntryPoint {
            role: "is_zero",
            symbol: "other_big_is_zero",
            def_path: "other::Big::is_zero",
            params: &[PinnedTy::Handle],
            returns: &[PinnedTy::Scalar(Ty::Bool)],
        },
    ],
};

/// A validating handle module over `pin`: `is_zero_of(k) =
/// is_zero(lift(k))` over the two roles it calls, licensed. The proof
/// program's `b5_10` shape. `extra` may add to the module after the handle
/// function, with the pinned declarations in hand.
fn handle_module_with(
    name: &str,
    pin: &HandleRuntimePin,
    lift: &str,
    is_zero: &str,
    extra: impl FnOnce(&mut ModuleBuilder, &HandleRuntimeDecls),
) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    let decls = mb
        .declare_handle_runtime_roles(pin, &[lift, is_zero])
        .expect("pinned roles");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let mut fb = mb.function("is_zero_of", sig);
    fb.set_body_gate(gate());
    let bb0 = fb.create_block();
    let k = fb.add_block_param(bb0, Ty::U64);
    fb.switch_to_block(bb0);
    let n = fb.call(decls.entry(lift).unwrap(), vec![k]);
    let z = fb.call(decls.entry(is_zero).unwrap(), vec![n]);
    fb.ret(vec![z]);
    fb.build();
    extra(&mut mb, &decls);
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn handle_module(name: &str, pin: &HandleRuntimePin, lift: &str, is_zero: &str) -> Module {
    handle_module_with(name, pin, lift, is_zero, |_, _| {})
}

fn nat_module() -> Module {
    handle_module("ws3_4_nat", nat_pin(), "from_u64", "is_zero")
}

/// The Clean general lane's spelling beside the handle: a bodyless
/// `l_Nat_sub : (Ptr, Ptr) -> Ptr` (a Clean-producer declaration over BOXED
/// objects) and a Clean function `boxed_sub_is_zero(a, b)` that subtracts two
/// boxed objects and, when `pass_box_to_pin` is set, hands the boxed result
/// to the pinned `is_zero`; otherwise it returns the constant `false`.
fn nat_module_beside_a_boxed_ptr_nat(pass_box_to_pin: bool) -> Module {
    handle_module_with(
        "ws3_4_nat_ptr",
        nat_pin(),
        "from_u64",
        "is_zero",
        |mb, decls| {
            mb.set_default_producer(Producer::Clean);
            let sub_sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]);
            let l_nat_sub = mb.declare_function("l_Nat_sub", sub_sig);
            let sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Bool]);
            let mut fb = mb.function("boxed_sub_is_zero", sig);
            fb.set_body_gate(gate());
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, Ty::Ptr);
            let b = fb.add_block_param(bb0, Ty::Ptr);
            fb.switch_to_block(bb0);
            let boxed = fb.call(l_nat_sub, vec![a, b]);
            let z = if pass_box_to_pin {
                fb.call(decls.entry("is_zero").unwrap(), vec![boxed])
            } else {
                fb.bool_const(false)
            };
            fb.ret(vec![z]);
            fb.build();
        },
    )
}

/// The handle-FREE analog: the same shape over `U64`, no handle anywhere.
fn u64_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("ws3_4_u64", target());
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let mut fb = mb.function("is_zero_of", sig);
    fb.set_body_gate(gate());
    let bb0 = fb.create_block();
    let k = fb.add_block_param(bb0, Ty::U64);
    fb.switch_to_block(bb0);
    let zero = fb.uconst(Ty::U64, 0);
    let z = fb.icmp(trust_ir::inst::ICmpOp::Eq, Ty::U64, k, zero);
    fb.ret(vec![z]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A `repr(C)` struct `name { limbs: Ptr, len: U64 }` — what a Rust
/// `{limbs: Vec<u64>}` would spell once its `Vec` is flattened. The field
/// types are irrelevant to the rule, which reads only the NAME.
fn struct_named(id: u32, name: &str) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![
            FieldDef {
                name: "limbs".into(),
                ty: Ty::Ptr,
                offset: Some(0),
            },
            FieldDef {
                name: "len".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    }
}

fn enum_named(id: u32, name: &str) -> EnumDef {
    EnumDef::new(
        EnumId::new(id),
        name,
        vec![
            EnumVariant {
                name: "small".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            },
            EnumVariant {
                name: "big".into(),
                fields: vec![Ty::Ptr],
                field_names: vec![],
            },
        ],
    )
}

fn record_named(id: u32, name: &str) -> RecordDef {
    RecordDef {
        id: RecordId::new(id),
        name: name.into(),
        fields: vec![FieldDef {
            name: "limbs".into(),
            ty: Ty::Ptr,
            offset: None,
        }],
    }
}

/// Exactly one refusal, and it is the named rule about `def` and `runtime`.
fn only_spelled_structurally(errors: &[ValidationError], def: &str, runtime: &str) -> bool {
    matches!(
        errors,
        [ValidationError::HandleRuntimeSpelledStructurally { def: d, runtime: r }]
            if d == def && r == runtime
    )
}

fn has_spelled_structurally(errors: &[ValidationError]) -> bool {
    errors
        .iter()
        .any(|e| matches!(e, ValidationError::HandleRuntimeSpelledStructurally { .. }))
}

// ───────────────────────────── POSITIVE ─────────────────────────────

/// A handle module plus an unrelated struct `Acct` validates on both lanes:
/// the rule is keyed on the definition's NAME, not on "a struct beside a
/// handle".
#[test]
fn a_handle_module_with_an_unrelated_struct_validates() {
    let mut m = nat_module();
    m.add_struct(struct_named(0, "Acct"));
    m.add_enum(enum_named(0, "Lvl"));
    m.add_record(record_named(0, "Row"));
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(validate_module_for_codegen(&m), vec![]);
    assert_eq!(
        validate_module_with_handle_registry(&m, HandleRegistry::pinned()),
        vec![]
    );
}

// ─────────────────────────── NEGATIVE TWINS ───────────────────────────

/// The same module plus a `StructDef` named `trust_bignum::Nat` is exactly
/// one `HandleRuntimeSpelledStructurally`, on every lane, naming the
/// definition and the runtime; the text says why.
#[test]
fn a_structural_trust_bignum_nat_beside_the_handle_is_refused() {
    let mut m = nat_module();
    m.add_struct(struct_named(0, "Acct"));
    m.add_struct(struct_named(1, NAT_RUNTIME));
    let errors = validate_module(&m);
    assert!(
        only_spelled_structurally(&errors, "struct #1", NAT_RUNTIME),
        "{errors:?}"
    );
    assert!(
        only_spelled_structurally(&validate_module_for_codegen(&m), "struct #1", NAT_RUNTIME),
        "codegen lane"
    );
    assert!(
        only_spelled_structurally(
            &validate_module_with_handle_registry(&m, HandleRegistry::pinned()),
            "struct #1",
            NAT_RUNTIME
        ),
        "explicit pinned registry"
    );
    let text = errors[0].to_string();
    assert!(text.contains("struct #1"), "{text}");
    assert!(text.contains("`trust_bignum::Nat`"), "{text}");
    assert!(text.contains("second spelling"), "{text}");
    assert!(text.contains("`Ty::Handle`"), "{text}");
    // The refusal enumerates the honest repair: the handle lowering.
    let options = errors[0].repair_options();
    assert!(
        options
            .iter()
            .any(|o| o.contains("`Ty::Handle`") && o.contains("pinned `drop`")),
        "{options:?}"
    );
}

/// An `EnumDef` named `trust_bignum::Nat` is refused the same way (a Lean
/// `inductive Nat | zero | succ` re-spelled as an IR enum).
#[test]
fn a_structural_enum_named_trust_bignum_nat_is_refused() {
    let mut m = nat_module();
    m.add_enum(enum_named(0, NAT_RUNTIME));
    let errors = validate_module(&m);
    assert!(
        only_spelled_structurally(&errors, "enum #0", NAT_RUNTIME),
        "{errors:?}"
    );
    assert!(only_spelled_structurally(
        &validate_module_for_codegen(&m),
        "enum #0",
        NAT_RUNTIME
    ));
}

/// A `RecordDef` named `trust_bignum::Nat` is refused the same way.
#[test]
fn a_structural_record_named_trust_bignum_nat_is_refused() {
    let mut m = nat_module();
    m.add_record(record_named(0, NAT_RUNTIME));
    let errors = validate_module(&m);
    assert!(
        only_spelled_structurally(&errors, "record #0", NAT_RUNTIME),
        "{errors:?}"
    );
    assert!(only_spelled_structurally(
        &validate_module_for_codegen(&m),
        "record #0",
        NAT_RUNTIME
    ));
}

/// Each spelling is refused on its own: two definitions of the runtime type
/// (a struct AND an enum) are two refusals, one per definition — the rule
/// never collapses them into one, so a report names every second spelling.
#[test]
fn every_structural_spelling_is_refused_separately() {
    let mut m = nat_module();
    m.add_struct(struct_named(0, NAT_RUNTIME));
    m.add_enum(enum_named(0, NAT_RUNTIME));
    m.add_record(record_named(0, NAT_RUNTIME));
    let errors = validate_module(&m);
    let mut defs: Vec<String> = errors
        .iter()
        .map(|e| match e {
            ValidationError::HandleRuntimeSpelledStructurally { def, runtime } => {
                assert_eq!(runtime, NAT_RUNTIME);
                def.clone()
            }
            other => panic!("unexpected refusal {other:?}"),
        })
        .collect();
    defs.sort();
    assert_eq!(defs, ["enum #0", "record #0", "struct #0"]);
}

// ─────────────────────────── ADVERSARIAL ───────────────────────────

/// A handle-FREE Rust module carrying `Struct("trust_bignum::Nat")` still
/// validates: a Rust crate that uses `trust_bignum::Nat` natively is not a
/// producer boundary, and the rule is scoped to handle-bearing modules.
#[test]
fn a_handle_free_rust_module_with_the_struct_validates() {
    let mut m = u64_module();
    m.add_struct(struct_named(0, NAT_RUNTIME));
    m.add_enum(enum_named(0, NAT_RUNTIME));
    m.add_record(record_named(0, NAT_RUNTIME));
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(validate_module_for_codegen(&m), vec![]);
}

/// The boundary is the handle CENSUS, not a call: a handle that occurs only
/// in an unused type-table row already makes the module handle-bearing, and
/// the structural spelling beside it is refused. (The same module without the
/// row is the adversarial case above, which validates.)
#[test]
fn a_handle_in_an_unused_type_row_makes_the_module_a_boundary() {
    let mut m = u64_module();
    m.add_struct(struct_named(0, NAT_RUNTIME));
    assert_eq!(validate_module(&m), vec![]);
    m.types.push(nat_pin().handle_ty());
    let errors = validate_module(&m);
    assert!(
        only_spelled_structurally(&errors, "struct #0", NAT_RUNTIME),
        "{errors:?}"
    );
}

/// Ported from the archived self-declared row
/// `trust-ir-self-declared/clean-objects-stay-ptr` (F-047). §7 part 3 makes
/// two claims about the Clean general lane's boxed spelling, and this pins
/// both: (1) it is INVISIBLE to the validator — a bodyless Clean
/// `l_Nat_sub : (Ptr, Ptr) -> Ptr` and a Clean function computing with boxed
/// objects validate `[]` beside the handle on every lane, so the ABSENCE of a
/// refusal is never a guarantee that one carrier crossed the boundary (the
/// producer obligation, WS6 F-102); and (2) it still cannot MEET the handle —
/// the boxed object handed to the pinned `is_zero` is exactly one
/// `CallArgTypeMismatch` (`Ptr != Handle`), with no conversion instruction
/// between the two spellings.
#[test]
fn the_clean_ptr_spelling_is_invisible_here_but_never_meets_the_handle() {
    let invisible = nat_module_beside_a_boxed_ptr_nat(false);
    assert_eq!(validate_module(&invisible), vec![]);
    assert_eq!(validate_module_for_codegen(&invisible), vec![]);

    let meets = nat_module_beside_a_boxed_ptr_nat(true);
    let errors = validate_module(&meets);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::CallArgTypeMismatch {
                callee,
                arg_index: 0,
                expected,
                actual,
                caller_producer: Some(caller),
                ..
            }] if callee == "trust_bignum_nat_is_zero"
                && expected.contains("trust_bignum::Nat")
                && actual == "ptr"
                && caller == "clean"
        ),
        "{errors:?}"
    );
    assert!(!has_spelled_structurally(&errors));
}

// ──────────────────────── MUTATION CONTROLS ────────────────────────

/// The rule is name-EXACT. A near miss — a case-fold, a prefix, a suffix, a
/// leading `::`, the bare `Nat` — validates beside the handle: the rule
/// catches the measured spelling and no renamed struct. §7 records that the
/// guarantee proper is the producer's.
#[test]
fn the_rule_is_name_exact() {
    for near_miss in [
        "trust_bignum::nat",
        "trust_bignum::Nat2",
        "trust_bignum::Nat::Inner",
        "::trust_bignum::Nat",
        "trust_bignum",
        "Nat",
        "trust_bignum_Nat",
    ] {
        let mut m = nat_module();
        m.add_struct(struct_named(0, near_miss));
        m.add_enum(enum_named(0, near_miss));
        m.add_record(record_named(0, near_miss));
        let errors = validate_module(&m);
        assert_eq!(errors, vec![], "near miss {near_miss:?}");
    }
    // ...and the exact spelling, in the same loop shape, is refused: the loop
    // above is not vacuous.
    let mut m = nat_module();
    m.add_struct(struct_named(0, NAT_RUNTIME));
    assert!(has_spelled_structurally(&validate_module(&m)));
}

/// The REGISTRY ROW is what names the runtime. Under a registry that pins
/// `("Big", "other::Big")` and not `trust_bignum::Nat`, a `Big`-handle module
/// is refused for a struct named `other::Big` and NOT for one named
/// `trust_bignum::Nat`; under the pinned registry the same `Big` module is
/// `UntrustedHandleRuntime` and never reaches this rule.
#[test]
fn the_registry_row_is_what_names_the_runtime() {
    let big_only = HandleRegistry::from_pins(&[ROW_BIG]).expect("well-formed one-row registry");
    let base = handle_module("ws3_4_big", &ROW_BIG, "mk", "is_zero");
    assert_eq!(
        validate_module_with_handle_registry(&base, &big_only),
        vec![]
    );

    let mut spelled_big = base.clone();
    spelled_big.add_struct(struct_named(0, "other::Big"));
    let errors = validate_module_with_handle_registry(&spelled_big, &big_only);
    assert!(
        only_spelled_structurally(&errors, "struct #0", "other::Big"),
        "{errors:?}"
    );

    // `trust_bignum::Nat` is not a pinned runtime of THIS registry, so a
    // struct by that name is just a struct here.
    let mut spelled_nat = base.clone();
    spelled_nat.add_struct(struct_named(0, NAT_RUNTIME));
    assert_eq!(
        validate_module_with_handle_registry(&spelled_nat, &big_only),
        vec![]
    );

    // Under the pinned registry the `Big` handle itself is untrusted; the
    // spelling rule is not what refuses the module.
    let pinned_errors = validate_module(&spelled_big);
    assert!(
        pinned_errors
            .iter()
            .any(|e| matches!(e, ValidationError::UntrustedHandleRuntime { runtime, .. } if runtime == "other::Big")),
        "{pinned_errors:?}"
    );
    assert!(
        !has_spelled_structurally(&pinned_errors),
        "{pinned_errors:?}"
    );

    // A two-row registry refuses BOTH spellings in one module: the module is a
    // boundary once any handle occurs, and the ruling names every pinned
    // runtime, not only the handle that occurs.
    let both = HandleRegistry::from_pins(&[nat_pin().clone(), ROW_BIG]).expect("two rows");
    let mut two = base.clone();
    two.add_struct(struct_named(0, NAT_RUNTIME));
    two.add_struct(struct_named(1, "other::Big"));
    let errors = validate_module_with_handle_registry(&two, &both);
    let mut runtimes: Vec<&str> = errors
        .iter()
        .map(|e| match e {
            ValidationError::HandleRuntimeSpelledStructurally { runtime, .. } => runtime.as_str(),
            other => panic!("unexpected refusal {other:?}"),
        })
        .collect();
    runtimes.sort_unstable();
    assert_eq!(runtimes, ["other::Big", NAT_RUNTIME]);
}

// ──────────────────── REVIEW: THE COMPOSED LANES ────────────────────
//
// The rule lives in `validate_module_filtered`, which every composed entry
// point shares. The review pins that on the two lanes a consumer actually
// runs before trusting a module: the authority tier, and the linked walk —
// where the second spelling may sit in a DEPENDENCY the root never names a
// handle in. A root that is handle-free and imports a handle-bearing
// dependency carrying `Struct("trust_bignum::Nat")` must see the dependency
// refused (`ImportedModuleInvalid`, naming the rule), never admitted because
// the root's own census is empty.

/// A handle-free root importing `dep` by digest, referencing nothing in it:
/// the walk authenticates and validates EVERY import row regardless.
fn root_importing(dep: &Module) -> Module {
    let mut root = u64_module();
    root.intern_import(
        ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    root
}

/// The authority-tier lane refuses the second spelling exactly like the plain
/// lane (no proof-bearing import to refuse first).
#[test]
fn the_authority_lane_refuses_the_second_spelling() {
    let mut m = nat_module();
    m.add_struct(struct_named(0, NAT_RUNTIME));
    let errors = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    assert!(
        only_spelled_structurally(&errors, "struct #0", NAT_RUNTIME),
        "{errors:?}"
    );
    // Right-reason twin: the same lane admits the module without the struct.
    assert_eq!(
        validate_module_with_authority(&nat_module(), &RejectingModuleProofAuthority),
        vec![]
    );
}

/// The linked walk refuses a DEPENDENCY that spells the runtime twice, even
/// when the root is handle-free and cites nothing in it: the import row is
/// `ImportedModuleInvalid`, and its `first` is this rule's text. The twin
/// dependency without the struct walks clean under the same root.
#[test]
fn the_linked_walk_refuses_a_dependency_with_the_second_spelling() {
    let mut dep = nat_module();
    dep.add_struct(struct_named(0, NAT_RUNTIME));
    let root = root_importing(&dep);
    assert_eq!(
        validate_module(&root),
        vec![],
        "the root alone is a plain Rust module"
    );
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        matches!(
            report.errors(),
            [ValidationError::ImportedModuleInvalid { import: 0, errors: 1, first }]
                if first.contains("struct #0")
                    && first.contains("`trust_bignum::Nat`")
                    && first.contains("second spelling")
        ),
        "{:?}",
        report.errors()
    );

    let clean_dep = nat_module();
    let root = root_importing(&clean_dep);
    let set = ModuleSet::new([&clean_dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}

/// The linked walk refuses the ROOT's second spelling too: a handle-bearing
/// root with the struct, importing a clean dependency, reports the rule on
/// itself and nothing about the dependency.
#[test]
fn the_linked_walk_refuses_the_roots_second_spelling() {
    let dep = nat_module();
    let mut root = handle_module("ws3_4_root", nat_pin(), "from_u64", "is_zero");
    root.intern_import(
        ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    root.add_struct(struct_named(0, NAT_RUNTIME));
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        only_spelled_structurally(report.errors(), "struct #0", NAT_RUNTIME),
        "{:?}",
        report.errors()
    );
}

// ──────────────────── REVIEW: THE SHAPES THE RULE MUST STILL REACH ────────────────────
//
// The twins above all add a DEAD definition to a module whose handle sits in
// a function body. Three shapes an adversary reaches for next, each a lane
// into the census gate the twins do not exercise:
//
//  * the second spelling is LIVE — a signature actually carries it, which is
//    the measured Rust shape (`Nat::from_u64` returns the struct BY VALUE);
//  * the handle occurs only in a bodyless DECLARATION's signature, never in a
//    defined body — the shape a Rust crate has before its first handle call;
//  * the second spelling sits in a handle-FREE ROOT that imports a
//    handle-bearing dependency — the one composition where §7's per-module
//    scope deliberately does NOT refuse, and which must therefore be written
//    down rather than left to be discovered as a surprise.

/// The second spelling is refused when it is LIVE, not only when it is a dead
/// table row: a handle-bearing module whose `nat_by_value` takes
/// `Struct("trust_bignum::Nat")` by value — the measured Rust lane, where
/// `Nat::from_u64` returns `{limbs, len}` by value beside the pinned handle —
/// is still EXACTLY ONE `HandleRuntimeSpelledStructurally`, with no cascade
/// from the uses. The twin renames the struct by one character and the same
/// live module validates, so the refusal is the NAME, not the use.
#[test]
fn a_live_second_spelling_in_a_signature_is_refused() {
    let live = |name: &str| {
        handle_module_with(
            "ws3_4_live",
            nat_pin(),
            "from_u64",
            "is_zero",
            |mb, _decls| {
                let sid = mb.add_struct(struct_named(0, name));
                let sig = mb.add_func_type(vec![Ty::Struct(sid)], vec![Ty::Bool]);
                let mut fb = mb.function("nat_by_value", sig);
                fb.set_body_gate(gate());
                let bb0 = fb.create_block();
                let _n = fb.add_block_param(bb0, Ty::Struct(sid));
                fb.switch_to_block(bb0);
                let z = fb.bool_const(false);
                fb.ret(vec![z]);
                fb.build();
            },
        )
    };
    let errors = validate_module(&live(NAT_RUNTIME));
    assert!(
        only_spelled_structurally(&errors, "struct #0", NAT_RUNTIME),
        "{errors:?}"
    );
    assert_eq!(
        validate_module_for_codegen(&live(NAT_RUNTIME)),
        errors,
        "the codegen lane refuses the live spelling identically"
    );
    // mutation control: one character off the runtime path and the same live
    // module validates.
    assert_eq!(validate_module(&live("trust_bignum::Nat_")), vec![]);
}

/// A module whose ONLY handle occurrence is a bodyless pinned DECLARATION's
/// signature — no defined function mentions a handle — is already a boundary:
/// the census walks `func_types`, not just the type table and the bodies.
/// This is the shape a Rust crate has the moment it declares the runtime and
/// before it calls it, and it is exactly where a producer would still be
/// carrying its own `Struct("trust_bignum::Nat")`.
#[test]
fn the_pinned_declarations_alone_make_the_module_a_boundary() {
    let declarations_only = |extra: Option<StructDef>| {
        let mut mb = ModuleBuilder::new_with_target_info("ws3_4_decls_only", target());
        mb.declare_handle_runtime_roles(nat_pin(), &["from_u64", "is_zero"])
            .expect("pinned roles");
        let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("passthrough", sig);
        fb.set_body_gate(gate());
        let bb0 = fb.create_block();
        let k = fb.add_block_param(bb0, Ty::U64);
        fb.switch_to_block(bb0);
        fb.ret(vec![k]);
        fb.build();
        if let Some(sd) = extra {
            mb.add_struct(sd);
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    // Right-reason twin first: the declarations alone validate.
    assert_eq!(validate_module(&declarations_only(None)), vec![]);
    let errors = validate_module(&declarations_only(Some(struct_named(0, NAT_RUNTIME))));
    assert!(
        only_spelled_structurally(&errors, "struct #0", NAT_RUNTIME),
        "{errors:?}"
    );
    // mutation control: the same module with the near-miss name validates.
    assert_eq!(
        validate_module(&declarations_only(Some(struct_named(
            0,
            "trust_bignum::Nat_"
        )))),
        vec![]
    );
}

/// The RESIDUAL, written down: §7's rule is scoped PER MODULE, so a
/// handle-FREE root that imports a handle-bearing dependency keeps its own
/// `Struct("trust_bignum::Nat")` — on the plain lane and through the linked
/// walk, which validates each module under its OWN census. That is not a
/// false refusal avoided by accident: nothing in the root can confuse the two
/// spellings, because a far `Handle` never equals a local `Struct`
/// (`ty_structurally_eq_across` compares `Handle` nominally), and the module
/// that actually carries handle VALUES is refused the moment it also spells
/// the runtime structurally (the twin below). The guarantee that the root's
/// `Nat` is the same `Nat` is the producer's, per §7 part 2.
#[test]
fn a_handle_free_root_importing_a_handle_bearing_dependency_keeps_its_struct() {
    let dep = nat_module();
    let mut root = root_importing(&dep);
    root.add_struct(struct_named(0, NAT_RUNTIME));
    assert_eq!(validate_module(&root), vec![], "the root is handle-free");
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());

    // The twin that fixes the scope: move the struct into the dependency —
    // the module that actually holds handle values — and the walk refuses.
    let mut dep = nat_module();
    dep.add_struct(struct_named(0, NAT_RUNTIME));
    let root = root_importing(&dep);
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        matches!(
            report.errors(),
            [ValidationError::ImportedModuleInvalid {
                import: 0,
                errors: 1,
                ..
            }]
        ),
        "{:?}",
        report.errors()
    );
}

/// The fourth nominal type kind cannot dodge the rule's def-table scope:
/// `Ty::Dialect` is the only other type that carries a NAME, and a pinned
/// runtime PATH is unspellable in it — the dialect name alphabet is
/// `[A-Za-z0-9_]`, so `::` is `DialectTyError::InvalidName` and
/// `validate_type_table_references` refuses it as `InvalidDialectType`
/// wherever the inventory walks. A second spelling therefore has to be a
/// `StructDef` / `EnumDef` / `RecordDef`, which is exactly what the rule
/// scans.
#[test]
fn a_dialect_type_cannot_spell_a_pinned_runtime_path() {
    assert!(
        trust_ir::DialectTy::new("bignum", NAT_RUNTIME, 1)
            .validate()
            .is_err()
    );
    let mut m = nat_module();
    m.types.push(Ty::Dialect(Box::new(trust_ir::DialectTy::new(
        "bignum",
        NAT_RUNTIME,
        1,
    ))));
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidDialectType { .. })),
        "{errors:?}"
    );
    assert!(!has_spelled_structurally(&errors), "{errors:?}");
    // Right-reason twin: the same dialect type under a spellable name is
    // admitted beside the handle, so the refusal above is the `::`, not the
    // presence of a dialect type.
    let mut ok = nat_module();
    ok.types.push(Ty::Dialect(Box::new(trust_ir::DialectTy::new(
        "bignum",
        "trust_bignum_Nat",
        1,
    ))));
    assert_eq!(validate_module(&ok), vec![]);
}
