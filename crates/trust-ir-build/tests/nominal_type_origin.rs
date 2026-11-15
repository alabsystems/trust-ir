// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.9 — the v58 nominal identity key on `StructDef` / `EnumDef`.
//!
//! The rule the key implements has exactly three clauses, and each one is
//! pinned here with its negative twin:
//!
//! 1. **split** — two structurally identical definitions with DIFFERENT keys
//!    are DIFFERENT types (the mutation control: they compared EQUAL before
//!    this key existed, and the test that says so is `..._was_equal_before`);
//! 2. **refuse** — one key over two shapes is a contradiction, named
//!    `TypeOriginConflict` across a link (both module fields `Some`) and, inside
//!    one module, a key claimed twice at all is the same variant's in-module
//!    form (both module fields `None`);
//! 3. **admit nothing** — an ABSENT key is not a wildcard. An unkeyed
//!    definition compares structurally exactly as it did before v58, and no
//!    test here shows a key making two things equal that structure calls
//!    different, because the comparator cannot do it.
//!
//! The paired carrier is the reason the field exists: a Rust `enum` that
//! MIRRORS a Clean inductive carries the CLEAN key, so the two spellings are
//! ONE type across the join.

use trust_ir::imports::{TyEquivalence, ty_equivalence_across, ty_structurally_eq_across};
use trust_ir::proof::{ProofDigest, RejectingModuleProofAuthority};
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, StructDef, Ty, TypeOrigin};
use trust_ir::value::{EnumId, StructId};
use trust_ir::{Endianness, Module, ModuleImport, Producer, TargetInfo};
use trust_ir_build::{ModuleSet, ValidationError, validate_linked_module, validate_module};

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// The Clean inductive `Trust.Nat`, as a producer would key it.
fn clean_nat() -> TypeOrigin {
    TypeOrigin::Clean {
        decl: "Trust.Nat".into(),
        env_digest: ProofDigest::sha256([0x51; 32]),
    }
}

/// A rustc def path with an empty-`GenericArgs` digest.
fn rust_key(crate_id: u64, path: u8, args: u8) -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: crate_id,
        def_path_hash: [path; 16],
        args_digest: ProofDigest::sha256([args; 32]),
    }
}

/// `enum Nat { Zero, Succ(payload) }` under `name`, optionally keyed.
fn nat_enum(name: &str, payload: Ty, origin: Option<TypeOrigin>) -> EnumDef {
    let def = EnumDef::new(
        EnumId::new(0),
        name,
        vec![
            EnumVariant {
                name: "Zero".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Succ".into(),
                fields: vec![payload],
                field_names: vec![],
            },
        ],
    );
    match origin {
        Some(origin) => def.with_origin(origin),
        None => def,
    }
}

/// A module carrying exactly one `Nat`-shaped enum.
fn nat_module(module: &str, def_name: &str, payload: Ty, origin: Option<TypeOrigin>) -> Module {
    let mut m = Module::new(module);
    m.target_info = Some(target());
    m.add_enum(nat_enum(def_name, payload, origin));
    m
}

fn one_field_struct(id: u32, name: &str, ty: Ty, origin: Option<TypeOrigin>) -> StructDef {
    let def = StructDef {
        id: StructId::new(id),
        name: name.into(),
        fields: vec![FieldDef {
            name: "raw".into(),
            ty,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    };
    match origin {
        Some(origin) => def.with_origin(origin),
        None => def,
    }
}

fn enum0() -> Ty {
    Ty::Enum(EnumId::new(0))
}

// ---------------------------------------------------------------------------
// 1. SPLIT — a key distinguishes; it never merges
// ---------------------------------------------------------------------------

/// POSITIVE. The paired carrier: a Rust enum MIRRORING a Clean inductive
/// carries the CLEAN key, so the Rust-produced module and the Clean-produced
/// module agree that these are ONE type — which is the whole point of the
/// field at the two-language join.
#[test]
fn paired_carrier_with_one_clean_key_compares_equal_across_modules() {
    let rust_side = nat_module("rust_side", "Nat", Ty::U64, Some(clean_nat()));
    let clean_side = nat_module("clean_side", "Nat", Ty::U64, Some(clean_nat()));

    assert_eq!(
        ty_equivalence_across(&rust_side, &enum0(), &clean_side, &enum0()),
        TyEquivalence::Equal,
        "one key over one shape is one type across the two producers"
    );
}

/// WHAT THE KEY DOES NOT BUY, pinned because it is the first thing a producer
/// will expect of it: an equal key does NOT license a different `name`. The
/// definition name is part of cross-module structural equality and stays so —
/// admitting a name difference BECAUSE of a key would be the one thing the
/// key is forbidden to do (`TypeOrigin`, clause 3). Two producers stamping
/// one entity must agree on the name as well, and disagreeing is a loud,
/// named contradiction rather than a silent merge.
#[test]
fn one_key_does_not_license_two_names() {
    let rust_side = nat_module("rust_side", "Nat", Ty::U64, Some(clean_nat()));
    let clean_side = nat_module("clean_side", "Trust.Nat", Ty::U64, Some(clean_nat()));

    let verdict = ty_equivalence_across(&rust_side, &enum0(), &clean_side, &enum0());
    let TyEquivalence::OriginConflict(conflict) = verdict else {
        panic!("expected an origin conflict, got {verdict:?}");
    };
    assert_eq!(conflict.left, "Nat");
    assert_eq!(conflict.right, "Trust.Nat");
}

/// MUTATION CONTROL, and the behaviour change this increment makes: the same
/// two definitions, byte-for-byte structurally identical, stop comparing
/// equal the moment they carry DIFFERENT keys.
#[test]
fn different_keys_split_two_structurally_identical_defs() {
    let plain_a = nat_module("a", "Nat", Ty::U64, None);
    let plain_b = nat_module("b", "Nat", Ty::U64, None);
    // The control: with no keys, structure decides and they ARE equal. This
    // is the outcome the whole test would have had before v58.
    assert!(
        ty_structurally_eq_across(&plain_a, &enum0(), &plain_b, &enum0()),
        "unkeyed definitions still compare structurally"
    );

    let keyed_a = nat_module("a", "Nat", Ty::U64, Some(rust_key(1, 0xa1, 0x01)));
    let keyed_b = nat_module("b", "Nat", Ty::U64, Some(rust_key(2, 0xb2, 0x01)));
    assert_eq!(
        ty_equivalence_across(&keyed_a, &enum0(), &keyed_b, &enum0()),
        TyEquivalence::Unequal,
        "two source entities are two types however identical their shapes"
    );
}

/// The monomorphic clause (SPEC §1): the IR has no `Ty::Param`, so one def
/// path reaches TrustIr once per instantiation. Two instantiations therefore
/// differ ONLY in `args_digest`, and that alone must split them.
#[test]
fn one_def_path_at_two_generic_arguments_is_two_types() {
    let vec_u8 = nat_module("a", "Vec", Ty::U8, Some(rust_key(1, 0xa1, 0x01)));
    let vec_u32 = nat_module("b", "Vec", Ty::U8, Some(rust_key(1, 0xa1, 0x02)));
    assert_eq!(
        ty_equivalence_across(&vec_u8, &enum0(), &vec_u32, &enum0()),
        TyEquivalence::Unequal,
        "`args_digest` is part of the key, not decoration"
    );
}

/// ABSENCE IS NOT A WILDCARD, in both directions it could fail:
/// an unkeyed definition neither matches a keyed one automatically, nor
/// refuses one automatically. It compares structurally — the pre-v58 rule.
#[test]
fn an_absent_key_neither_admits_nor_refuses() {
    let keyed = nat_module("a", "Nat", Ty::U64, Some(clean_nat()));
    let unkeyed_same = nat_module("b", "Nat", Ty::U64, None);
    let unkeyed_other = nat_module("c", "Nat", Ty::U32, None);

    assert_eq!(
        ty_equivalence_across(&keyed, &enum0(), &unkeyed_same, &enum0()),
        TyEquivalence::Equal,
        "structure decides when one side makes no claim"
    );
    assert_eq!(
        ty_equivalence_across(&keyed, &enum0(), &unkeyed_other, &enum0()),
        TyEquivalence::Unequal,
        "and it still decides against them when the shapes differ"
    );
}

// ---------------------------------------------------------------------------
// 2. REFUSE — one key, two shapes
// ---------------------------------------------------------------------------

/// NEGATIVE TWIN of the positive above: the SAME key, and one variant's field
/// is `U32` on one side and `U64` on the other. Not "two types" — a
/// contradiction, and it is reported as one by name.
#[test]
fn one_key_over_two_shapes_is_a_named_type_origin_conflict() {
    let narrow = nat_module("rust_side", "Nat", Ty::U32, Some(clean_nat()));
    let wide = nat_module("clean_side", "Trust.Nat", Ty::U64, Some(clean_nat()));

    let verdict = ty_equivalence_across(&narrow, &enum0(), &wide, &enum0());
    let TyEquivalence::OriginConflict(conflict) = verdict else {
        panic!("expected an origin conflict, got {verdict:?}");
    };
    assert_eq!(conflict.origin, clean_nat());
    assert_eq!(conflict.table, "enum");
    assert_eq!(conflict.left, "Nat");
    assert_eq!(conflict.right, "Trust.Nat");
    // The comparator's own verdict is still "not equal": a conflict never
    // admits, it only explains.
    assert!(!ty_structurally_eq_across(
        &narrow,
        &enum0(),
        &wide,
        &enum0()
    ));
    // The two-module helper reports exactly this pair.
    assert_eq!(narrow.type_origin_conflicts_with(&wide), vec![conflict]);
}

/// The LINKED validator names it. This is the rule's cross-crate home: the
/// root and an AUTHENTICATED dependency stamp one key over two shapes.
#[test]
fn linked_validation_refuses_a_cross_crate_type_origin_conflict() {
    let mut dependency = nat_module("dep", "Trust.Nat", Ty::U64, Some(clean_nat()));
    dependency.target_info = Some(target());
    assert!(
        validate_module(&dependency).is_empty(),
        "the dependency fixture must validate alone"
    );

    let mut root = nat_module("root", "Nat", Ty::U32, Some(clean_nat()));
    root.intern_import(
        ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
            .with_producer(Producer::Clean),
    )
    .expect("Module::intern_import: test fixture");

    let set = ModuleSet::new([&dependency]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let conflict = errors
        .iter()
        .find(|error| matches!(error, ValidationError::TypeOriginConflict { .. }))
        .unwrap_or_else(|| panic!("expected a TypeOriginConflict, got {errors:?}"));
    let ValidationError::TypeOriginConflict {
        first_module,
        first_table,
        first,
        second_module,
        second_table,
        second,
        ..
    } = conflict
    else {
        unreachable!("matched above")
    };
    // Walk order: the dependency registers its key before its importer.
    assert_eq!(first_module.as_deref(), Some("dep"));
    assert_eq!(*first_table, "enum");
    assert_eq!(first, "Trust.Nat");
    assert_eq!(second_module.as_deref(), Some("root"));
    assert_eq!(*second_table, "enum");
    assert_eq!(second, "Nat");
}

/// The rule is CLOSURE-wide, not per import edge. Two SIBLING dependencies
/// (neither imports the other) that stamp one key over two shapes are a
/// contradiction in the program that links them both, even though the root
/// itself carries no key — and it is reported on the ROOT, naming both
/// modules, because neither sibling is invalid on its own.
#[test]
fn linked_validation_refuses_a_conflict_between_two_siblings() {
    let narrow = nat_module("sibling_narrow", "Nat", Ty::U32, Some(clean_nat()));
    let wide = nat_module("sibling_wide", "Nat", Ty::U64, Some(clean_nat()));
    let mut root = Module::new("root");
    root.target_info = Some(target());
    for dependency in [&narrow, &wide] {
        root.intern_import(
            ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    }

    let set = ModuleSet::new([&narrow, &wide]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let conflicts: Vec<_> = errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::TypeOriginConflict {
                first_module,
                second_module,
                ..
            } => Some((first_module.as_deref(), second_module.as_deref())),
            _ => None,
        })
        .collect();
    assert_eq!(
        conflicts,
        vec![(Some("sibling_narrow"), Some("sibling_wide"))],
        "one conflict, naming both siblings, on the root: {errors:?}"
    );
    // Neither sibling was declared invalid by the other.
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::ImportedModuleInvalid { .. })),
        "a sibling conflict is the closure's, not a dependency's: {errors:?}"
    );

    // MUTATION CONTROL: the same two siblings AGREEING raise nothing.
    let wide_twin = nat_module("sibling_wide", "Nat", Ty::U64, Some(clean_nat()));
    let wide_again = nat_module("sibling_again", "Nat", Ty::U64, Some(clean_nat()));
    let mut root = Module::new("root");
    root.target_info = Some(target());
    for dependency in [&wide_twin, &wide_again] {
        root.intern_import(
            ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    }
    let set = ModuleSet::new([&wide_twin, &wide_again]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::TypeOriginConflict { .. })),
        "agreeing siblings are one entity carried twice: {errors:?}"
    );
}

/// Closure-wide also means TRANSITIVE: a leaf reached only through a
/// dependency and a direct dependency that never import each other still
/// link into one program.
#[test]
fn linked_validation_refuses_a_conflict_across_a_transitive_edge() {
    let leaf = nat_module("leaf", "Nat", Ty::U64, Some(clean_nat()));
    let mut middle = Module::new("middle");
    middle.target_info = Some(target());
    middle
        .intern_import(
            ModuleImport::new(leaf.name.clone(), leaf.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    let direct = nat_module("direct", "Nat", Ty::U32, Some(clean_nat()));
    let mut root = Module::new("root");
    root.target_info = Some(target());
    for dependency in [&middle, &direct] {
        root.intern_import(
            ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    }

    let set = ModuleSet::new([&leaf, &middle, &direct]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let conflict = errors
        .iter()
        .find(|error| matches!(error, ValidationError::TypeOriginConflict { .. }))
        .unwrap_or_else(|| panic!("expected a TypeOriginConflict, got {errors:?}"));
    let ValidationError::TypeOriginConflict {
        first_module,
        second_module,
        ..
    } = conflict
    else {
        unreachable!("matched above")
    };
    assert_eq!(first_module.as_deref(), Some("leaf"));
    assert_eq!(second_module.as_deref(), Some("direct"));
}

/// MUTATION CONTROL for the rule above: the SAME linked shape, with the two
/// definitions AGREEING, raises nothing. A rule that refused here would
/// refuse every honest two-producer module.
#[test]
fn linked_validation_admits_an_agreeing_cross_crate_key() {
    let dependency = nat_module("dep", "Nat", Ty::U64, Some(clean_nat()));
    let mut root = nat_module("root", "Nat", Ty::U64, Some(clean_nat()));
    root.intern_import(
        ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
            .with_producer(Producer::Clean),
    )
    .expect("Module::intern_import: test fixture");

    let set = ModuleSet::new([&dependency]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::TypeOriginConflict { .. })),
        "an agreeing key is the ratified two-producer shape: {errors:?}"
    );
}

/// A key present on only ONE side of the link is not a finding: the modules
/// simply do not share that entity.
#[test]
fn a_key_only_one_side_carries_is_not_a_conflict() {
    let dependency = nat_module("dep", "Other", Ty::U64, Some(rust_key(9, 0x99, 0x09)));
    let mut root = nat_module("root", "Nat", Ty::U32, Some(clean_nat()));
    root.intern_import(
        ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
            .with_producer(Producer::Clean),
    )
    .expect("Module::intern_import: test fixture");
    let set = ModuleSet::new([&dependency]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::TypeOriginConflict { .. })),
        "unshared keys are unrelated entities, not a contradiction: {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// 3. One module, one image per key
// ---------------------------------------------------------------------------

#[test]
fn duplicate_type_origin_in_one_module_is_refused() {
    let mut m = Module::new("duplicate");
    m.target_info = Some(target());
    let key = rust_key(7, 0x77, 0x07);
    m.structs
        .push(one_field_struct(0, "First", Ty::U64, Some(key.clone())));
    // A DIFFERENT shape, so nothing merges it away: the refusal is about the
    // key being claimed twice, not about the shapes disagreeing.
    m.structs
        .push(one_field_struct(1, "Second", Ty::U32, Some(key.clone())));

    let errors = validate_module(&m);
    let duplicate = errors
        .iter()
        .find(|error| matches!(error, ValidationError::TypeOriginConflict { .. }))
        .unwrap_or_else(|| panic!("expected a TypeOriginConflict, got {errors:?}"));
    let ValidationError::TypeOriginConflict {
        first_module,
        first_table,
        first,
        second_module,
        second_table,
        second,
        ..
    } = duplicate
    else {
        unreachable!("matched above")
    };
    // The in-module form names no module: both claims are in the module
    // under validation.
    assert_eq!((first_module, second_module), (&None, &None));
    assert_eq!(*first_table, "struct");
    assert_eq!(first, "First");
    assert_eq!(*second_table, "struct");
    assert_eq!(second, "Second");
}

/// The struct and enum tables are ONE key space: a struct and an enum
/// claiming the same entity is the same collision, and scanning the tables
/// separately would miss it.
#[test]
fn a_struct_and_an_enum_claiming_one_key_is_the_same_collision() {
    let mut m = Module::new("cross_table");
    m.target_info = Some(target());
    let key = clean_nat();
    m.structs
        .push(one_field_struct(0, "NatStruct", Ty::U64, Some(key.clone())));
    m.enums.push(nat_enum("NatEnum", Ty::U64, Some(key)));

    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::TypeOriginConflict {
                first_module: None,
                first_table: "struct",
                second_module: None,
                second_table: "enum",
                ..
            }
        )),
        "one entity cannot be both a struct and an enum: {errors:?}"
    );
}

/// MUTATION CONTROL: distinct keys in one module are the ordinary case and
/// raise nothing.
#[test]
fn distinct_keys_in_one_module_are_admitted() {
    let mut m = Module::new("distinct");
    m.target_info = Some(target());
    m.structs.push(one_field_struct(
        0,
        "First",
        Ty::U64,
        Some(rust_key(7, 0x77, 0x07)),
    ));
    m.structs.push(one_field_struct(
        1,
        "Second",
        Ty::U64,
        Some(rust_key(7, 0x77, 0x08)),
    ));
    m.structs
        .push(one_field_struct(2, "Unkeyed", Ty::U64, None));
    m.structs
        .push(one_field_struct(3, "AlsoUnkeyed", Ty::U64, None));

    let errors = validate_module(&m);
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, ValidationError::TypeOriginConflict { .. })),
        "distinct keys, and any number of unkeyed defs, are fine: {errors:?}"
    );
}

/// Deduplication is keyed too: `Module::add_struct_def` merges structurally
/// identical definitions, and two that name DIFFERENT source entities must
/// survive as two rows rather than being silently merged behind the
/// validator's back.
#[test]
fn add_struct_def_does_not_dedup_across_different_keys() {
    let mut m = Module::new("dedup");
    m.target_info = Some(target());
    let a = m
        .add_struct_def(one_field_struct(
            0,
            "Same",
            Ty::U64,
            Some(rust_key(1, 0x11, 0x01)),
        ))
        .expect("Module::add_struct_def: test fixture");
    let b = m
        .add_struct_def(one_field_struct(
            1,
            "Same",
            Ty::U64,
            Some(rust_key(2, 0x22, 0x01)),
        ))
        .expect("Module::add_struct_def: test fixture");
    assert_ne!(a, b, "different entities must not collapse into one row");
    assert_eq!(m.structs.len(), 2);

    // The control: with the SAME key they are one definition, exactly as two
    // unkeyed identical definitions have always been.
    let mut n = Module::new("dedup_same");
    n.target_info = Some(target());
    let key = rust_key(1, 0x11, 0x01);
    let c = n
        .add_struct_def(one_field_struct(0, "Same", Ty::U64, Some(key.clone())))
        .expect("Module::add_struct_def: test fixture");
    let d = n
        .add_struct_def(one_field_struct(1, "Same", Ty::U64, Some(key)))
        .expect("Module::add_struct_def: test fixture");
    assert_eq!(c, d);
    assert_eq!(n.structs.len(), 1);
}

// ---------------------------------------------------------------------------
// 4. REVIEW — nested keys, keys behind signatures, and a diamond
// ---------------------------------------------------------------------------

/// `struct Outer { inner: Inner }` with `Outer` keyed `outer_key` on both
/// sides and `Inner` keyed as the caller says.
fn outer_inner_module(
    name: &str,
    outer_key: TypeOrigin,
    inner_key: Option<TypeOrigin>,
    inner_payload: Ty,
) -> Module {
    let mut m = Module::new(name);
    m.target_info = Some(target());
    m.structs
        .push(one_field_struct(0, "Inner", inner_payload, inner_key));
    m.structs.push(one_field_struct(
        1,
        "Outer",
        Ty::Struct(StructId::new(0)),
        Some(outer_key),
    ));
    m
}

fn outer() -> Ty {
    Ty::Struct(StructId::new(1))
}

/// ADVERSARIAL (a false claim through nesting). Two modules stamp ONE key on
/// `Outer`, whose only field is `Inner` — and `Inner` is keyed DIFFERENTLY on
/// the two sides over an identical shape. The inner split must PROPAGATE: the
/// two `Outer`s are one entity with two shapes (they hold different entities),
/// so the verdict is a conflict on the OUTER key, never `Equal` because the
/// bytes happen to agree. And in the module-pair helper the inner pair is not
/// a conflict at all (different keys are two types), so exactly one row.
#[test]
fn a_split_inside_a_shared_key_is_a_conflict_on_the_shared_key() {
    let outer_key = rust_key(1, 0x0a, 0x01);
    let left = outer_inner_module(
        "left",
        outer_key.clone(),
        Some(rust_key(1, 0x1a, 0x01)),
        Ty::U64,
    );
    let right = outer_inner_module(
        "right",
        outer_key.clone(),
        Some(rust_key(1, 0x1b, 0x01)),
        Ty::U64,
    );

    let verdict = ty_equivalence_across(&left, &outer(), &right, &outer());
    let TyEquivalence::OriginConflict(conflict) = verdict else {
        panic!("the inner split must surface as an outer conflict, got {verdict:?}");
    };
    assert_eq!(conflict.origin, outer_key);
    assert_eq!(conflict.table, "struct");
    assert_eq!(
        (conflict.left.as_str(), conflict.right.as_str()),
        ("Outer", "Outer")
    );

    let conflicts = left.type_origin_conflicts_with(&right);
    assert_eq!(conflicts.len(), 1, "{conflicts:?}");
    assert_eq!(conflicts[0].origin, outer_key);

    // The linked walk says the same, once, on the root.
    let mut root = Module::new("root");
    root.target_info = Some(target());
    for dependency in [&left, &right] {
        root.intern_import(
            ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                .with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    }
    let set = ModuleSet::new([&left, &right]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let named: Vec<_> = errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::TypeOriginConflict { first, second, .. } => {
                Some((first.as_str(), second.as_str()))
            }
            _ => None,
        })
        .collect();
    assert_eq!(named, vec![("Outer", "Outer")], "{errors:?}");
}

/// ADVERSARIAL twin: one key on `Outer` AND one key on `Inner`, with the inner
/// SHAPES disagreeing. Both keys are contradicted, and BOTH are reported — a
/// comparator that stopped at the first would let the second contradiction
/// ride into a later link unnamed. The single-comparison verdict names the
/// inner one, because it is the first the walk reaches.
#[test]
fn every_contradicted_key_is_reported_and_the_innermost_names_the_comparison() {
    let outer_key = rust_key(1, 0x0a, 0x01);
    let inner_key = rust_key(1, 0x1a, 0x01);
    let narrow = outer_inner_module(
        "narrow",
        outer_key.clone(),
        Some(inner_key.clone()),
        Ty::U32,
    );
    let wide = outer_inner_module("wide", outer_key.clone(), Some(inner_key.clone()), Ty::U64);

    let verdict = ty_equivalence_across(&narrow, &outer(), &wide, &outer());
    let TyEquivalence::OriginConflict(conflict) = verdict else {
        panic!("expected a conflict, got {verdict:?}");
    };
    assert_eq!(
        conflict.origin, inner_key,
        "the innermost contradiction names it"
    );

    let mut reported: Vec<TypeOrigin> = narrow
        .type_origin_conflicts_with(&wide)
        .into_iter()
        .map(|conflict| conflict.origin)
        .collect();
    reported.sort();
    let mut expected = vec![outer_key.clone(), inner_key.clone()];
    expected.sort();
    assert_eq!(reported, expected);

    let mut root = Module::new("root");
    root.target_info = Some(target());
    for dependency in [&narrow, &wide] {
        root.intern_import(
            ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                .with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    }
    let set = ModuleSet::new([&narrow, &wide]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let mut linked: Vec<String> = errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::TypeOriginConflict { origin, .. } => Some(origin.clone()),
            _ => None,
        })
        .collect();
    linked.sort();
    let mut expected: Vec<String> = [&outer_key, &inner_key]
        .iter()
        .map(ToString::to_string)
        .collect();
    expected.sort();
    assert_eq!(linked, expected, "{errors:?}");
}

/// A LEGITIMATE module is not refused: one side keys `Inner`, the other does
/// not, and `Outer` shares a key over an identical shape. The unkeyed inner
/// compares structurally (it makes no claim), so the outers agree.
#[test]
fn an_unkeyed_nested_def_under_a_shared_key_compares_structurally() {
    let outer_key = rust_key(1, 0x0a, 0x01);
    let keyed = outer_inner_module(
        "keyed",
        outer_key.clone(),
        Some(rust_key(1, 0x1a, 0x01)),
        Ty::U64,
    );
    let bare = outer_inner_module("bare", outer_key, None, Ty::U64);
    assert_eq!(
        ty_equivalence_across(&keyed, &outer(), &bare, &outer()),
        TyEquivalence::Equal
    );
    assert!(keyed.type_origin_conflicts_with(&bare).is_empty());
    assert!(bare.type_origin_conflicts_with(&keyed).is_empty());
}

/// The key reaches through a FUNCTION signature, which is how an import's
/// far function is compared against the local declaration
/// (`signatures_compatible` walks each parameter with the same comparator):
/// a keyed parameter type splits on a different key and refuses on one key
/// over two shapes, exactly as it does at top level.
#[test]
fn a_key_behind_a_function_signature_splits_and_refuses() {
    use trust_ir::ty::FuncTy;

    fn taking(name: &str, key: TypeOrigin, payload: Ty) -> Module {
        let mut m = Module::new(name);
        m.target_info = Some(target());
        m.structs
            .push(one_field_struct(0, "Arg", payload, Some(key)));
        m.add_func_type(FuncTy {
            abi: None,
            params: vec![Ty::Struct(StructId::new(0))],
            returns: vec![Ty::Unit],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
        m
    }
    let func = Ty::Func(trust_ir::value::FuncTyId::new(0));

    let a = taking("a", rust_key(1, 0x01, 0x01), Ty::U64);
    let same = taking("same", rust_key(1, 0x01, 0x01), Ty::U64);
    let other_key = taking("other_key", rust_key(2, 0x02, 0x01), Ty::U64);
    let other_shape = taking("other_shape", rust_key(1, 0x01, 0x01), Ty::U32);

    assert_eq!(
        ty_equivalence_across(&a, &func, &same, &func),
        TyEquivalence::Equal
    );
    assert_eq!(
        ty_equivalence_across(&a, &func, &other_key, &func),
        TyEquivalence::Unequal
    );
    let verdict = ty_equivalence_across(&a, &func, &other_shape, &func);
    let TyEquivalence::OriginConflict(conflict) = verdict else {
        panic!("one key over two parameter shapes is a conflict, got {verdict:?}");
    };
    assert_eq!(conflict.origin, rust_key(1, 0x01, 0x01));
}

/// A DIAMOND: the root imports two middles that both import ONE leaf, and the
/// leaf contradicts the root. The leaf is validated once (the walk is memoized
/// by digest), so its claim is registered once and the contradiction is
/// reported ONCE — not once per path, and never as the leaf disagreeing with
/// itself.
#[test]
fn a_diamond_reports_a_conflict_with_the_shared_leaf_exactly_once() {
    let leaf = nat_module("leaf", "Nat", Ty::U64, Some(clean_nat()));
    let mut middles = Vec::new();
    for name in ["middle_a", "middle_b"] {
        let mut middle = Module::new(name);
        middle.target_info = Some(target());
        middle
            .intern_import(
                ModuleImport::new(leaf.name.clone(), leaf.stable_digest())
                    .with_producer(Producer::Clean),
            )
            .expect("Module::intern_import: test fixture");
        middles.push(middle);
    }
    let mut root = nat_module("root", "Nat", Ty::U32, Some(clean_nat()));
    for middle in &middles {
        root.intern_import(
            ModuleImport::new(middle.name.clone(), middle.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    }
    let set = ModuleSet::new([&leaf, &middles[0], &middles[1]]);
    let errors = validate_linked_module(&root, &set, &RejectingModuleProofAuthority).into_errors();
    let conflicts: Vec<_> = errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::TypeOriginConflict {
                first_module,
                second_module,
                ..
            } => Some((first_module.as_deref(), second_module.as_deref())),
            _ => None,
        })
        .collect();
    assert_eq!(conflicts, vec![(Some("leaf"), Some("root"))], "{errors:?}");
}

// ---------------------------------------------------------------------------
// 6. Review — the two-module helper compares EVERY claim under a shared key
// ---------------------------------------------------------------------------

/// `Module::type_origin_conflicts_with` takes ANY two modules, including one
/// that stamps a key twice (its own validator refuses that, but the helper
/// does not run it). It used to keep ONE claim per key on the left — the
/// LAST — so a left module whose EARLIER claim disagreed with the right one
/// reported nothing whenever its later claim happened to agree.
///
/// Three adversarial left sides, each against one right side:
///
/// 1. the right side agrees with the LAST left claim: the EARLIER one is the
///    contradiction, and it must be named (the case the old helper dropped);
/// 2. the right side agrees with the FIRST left claim: the LATER one is the
///    contradiction (the old helper also caught this — the control);
/// 3. the second left claim is an ENUM: a key claimed across the two tables
///    is compared against the right side's struct and named as a conflict.
///
/// And the mutation control: a left module with ONE agreeing claim reports
/// nothing, so the helper did not simply start reporting every shared key.
#[test]
fn every_claim_under_a_shared_key_is_compared_not_only_the_last() {
    let key = rust_key(9, 0x99, 0x09);
    let doubly_keyed = |second: StructDef| {
        let mut m = Module::new("doubly_keyed");
        m.target_info = Some(target());
        m.structs
            .push(one_field_struct(0, "First", Ty::U64, Some(key.clone())));
        m.structs.push(second);
        m
    };
    let right_with = |name: &str, ty: Ty| {
        let mut m = Module::new("right");
        m.target_info = Some(target());
        m.structs
            .push(one_field_struct(0, name, ty, Some(key.clone())));
        m
    };
    let pairs = |left: &Module, right: &Module| {
        left.type_origin_conflicts_with(right)
            .into_iter()
            .map(|conflict| (conflict.table, conflict.left, conflict.right))
            .collect::<Vec<_>>()
    };

    // 1. Right agrees with the LAST left claim (`Second: U32`).
    let left = doubly_keyed(one_field_struct(1, "Second", Ty::U32, Some(key.clone())));
    assert!(
        validate_module(&left)
            .iter()
            .any(|e| matches!(e, ValidationError::TypeOriginConflict { .. })),
        "the doubly-keyed fixture is itself refused by its own validator"
    );
    assert_eq!(
        pairs(&left, &right_with("Second", Ty::U32)),
        vec![("struct", "First".to_string(), "Second".to_string())],
        "the EARLIER claim disagrees with the right side and must be named"
    );

    // 2. Right agrees with the FIRST left claim (`First: U64`).
    assert_eq!(
        pairs(&left, &right_with("First", Ty::U64)),
        vec![("struct", "Second".to_string(), "First".to_string())]
    );

    // 3. The second left claim is an enum under the same key.
    let mut cross_table = Module::new("cross_table");
    cross_table.target_info = Some(target());
    cross_table
        .structs
        .push(one_field_struct(0, "First", Ty::U64, Some(key.clone())));
    cross_table
        .enums
        .push(nat_enum("First", Ty::U64, Some(key.clone())));
    assert_eq!(
        pairs(&cross_table, &right_with("First", Ty::U64)),
        vec![("enum", "First".to_string(), "First".to_string())],
        "the enum claim cannot be the right side's struct"
    );

    // Mutation control: one agreeing claim, no finding.
    let mut single = Module::new("single");
    single.target_info = Some(target());
    single
        .structs
        .push(one_field_struct(0, "First", Ty::U64, Some(key.clone())));
    assert!(pairs(&single, &right_with("First", Ty::U64)).is_empty());
}
