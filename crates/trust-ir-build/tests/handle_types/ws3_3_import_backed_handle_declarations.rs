// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.3 (F-048): an IMPORT-BACKED handle declaration.
//!
//! A dependency may DEFINE and export `dep_double: Nat -> Nat`, but before
//! WS3.3 no importer could declare it: v43 rule 6 (`HandleForeignDeclaration`)
//! admits only pinned entry points, so the root's body-less `dep_double` was
//! refused in every lane, `validate_linked_module` included.
//!
//! The binding is the v41 spelling (DG-26, no wire): the declaration carries
//! `backed_by: ExternRef { module, symbol: "dep_double", obligation: None }`.
//! ONLY `validate_linked_module` admits it, after linked rule L11 resolves the
//! binding at `ExternRefSite::HandleDeclaration` — R1–R6 with R4 HARDENED to a
//! far DEFINITION that is not an `AvailableExternally` copy, or a far
//! declaration the dependency's own verdict authenticated. Every single-module
//! lane keeps refusing it (fail closed).

use trust_ir::proof::RejectingModuleProofAuthority;
use trust_ir::value::ImportId;
use trust_ir::{
    BodyGate, Endianness, ExternRef, ExternRefSite, FunctionSummary, ImportVerificationError,
    Linkage, Module, ModuleImport, Producer, StructPassingPolicy, TargetInfo, Ty,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    ModuleBuilder, ModuleSet, TRUSTED_HANDLE_RUNTIMES, ValidationConfig, validate_linked_module,
    validate_linked_module_with_config, validate_module, validate_module_for_codegen,
    validate_module_with_authority,
};

const SYMBOL: &str = "dep_double";

fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn gate() -> BodyGate {
    BodyGate::Gated {
        authority: "ws3.3".into(),
        evidence: None,
    }
}

/// How the dependency spells `dep_double`.
#[derive(Clone)]
enum Far {
    /// `dep_double(x: Nat) -> Nat { add(x, x) }`, producer Clean.
    Defines,
    /// The same body, with a different producer.
    DefinesAs(Producer),
    /// `dep_double(x: Nat) -> u64 { 0 }` — the skewed signature.
    DefinesReturningU64,
    /// The definition with `AvailableExternally` linkage: a body copy.
    DefinesAvailableExternally,
    /// A body-less declaration, no `backed_by`.
    Declares,
    /// A body-less declaration whose entity-only `backed_by` names import 0
    /// of THIS module (the chain's middle link).
    Redeclares,
    /// `dep_double` is absent; the module defines `other(x: Nat) -> Nat`.
    Omits,
}

fn builder(name: &str) -> ModuleBuilder {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::Clean);
    mb
}

/// A dependency module named `name` spelling `dep_double` as `far`. With
/// `Far::Redeclares`, `next` is the module import 0 names.
fn dependency(name: &str, far: Far, next: Option<&Module>) -> Module {
    let mut mb = builder(name);
    let decls = mb
        .declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .expect("pinned runtime declares");
    let add = decls.entry("add").expect("add is pinned");
    let returns = match far {
        Far::DefinesReturningU64 => Ty::U64,
        _ => nat(),
    };
    let sig = mb.add_func_type(vec![nat()], vec![returns.clone()]);
    let body_name = match far {
        Far::Omits => "other",
        _ => SYMBOL,
    };
    match far {
        Far::Declares | Far::Redeclares => {
            mb.declare_function(SYMBOL, sig);
        }
        _ => {
            let mut fb = mb.function(body_name, sig);
            if let Far::DefinesAs(producer) = &far {
                fb.set_producer(producer.clone());
            }
            fb.set_body_gate(gate());
            let entry = fb.create_block();
            let x = fb.add_block_param(entry, nat());
            fb.switch_to_block(entry);
            let out = if returns == Ty::U64 {
                fb.iconst(Ty::U64, 0)
            } else {
                fb.call(add, vec![x, x])
            };
            fb.ret(vec![out]);
            fb.build();
        }
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Far::DefinesAvailableExternally = far {
        function_mut(&mut module, SYMBOL).linkage = Linkage::AvailableExternally;
    }
    if let Far::Redeclares = far {
        let next = next.expect("a re-declaration names the next module");
        let import = module
            .intern_import(
                ModuleImport::new(next.name.clone(), next.stable_digest())
                    .with_producer(Producer::Clean),
            )
            .expect("Module::intern_import: test fixture");
        function_mut(&mut module, SYMBOL).summary = Some(binding(import));
    }
    module
}

/// The DG-26 binding: an entity-only `backed_by` naming the declaration's own
/// link symbol.
fn binding(import: ImportId) -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .backed_by(ExternRef::new(import, SYMBOL))
}

fn function_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut trust_ir::Function {
    module
        .functions
        .iter_mut()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
}

/// The root: an import row for `dep`, a body-less `dep_double: Nat -> Nat`
/// (bound with `backed_by` when `bound`), and a Rust `root_use` calling it.
fn root(dep: &Module, bound: bool) -> Module {
    let mut mb = builder("root");
    mb.declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .expect("pinned runtime declares");
    let sig = mb.add_func_type(vec![nat()], vec![nat()]);
    let far = mb.declare_function(SYMBOL, sig);
    let mut fb = mb.function("root_use", sig);
    fb.set_producer(Producer::TRust);
    fb.set_body_gate(gate());
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, nat());
    fb.switch_to_block(entry);
    let out = fb.call(far, vec![x]);
    fb.ret(vec![out]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let import = module
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    if bound {
        function_mut(&mut module, SYMBOL).summary = Some(binding(import));
    }
    module
}

fn linked_errors(root: &Module, deps: &[&Module]) -> Vec<ValidationError> {
    validate_linked_module(
        root,
        &ModuleSet::new(deps.iter().copied()),
        &RejectingModuleProofAuthority,
    )
    .into_errors()
}

/// Exactly one `HandleForeignDeclaration`, on `dep_double`, whose detail
/// contains `needle`.
fn only_foreign(errors: &[ValidationError], needle: &str) -> bool {
    matches!(
        errors,
        [ValidationError::HandleForeignDeclaration { name, handle, detail, .. }]
            if name == SYMBOL && handle.contains("trust_bignum::Nat") && detail.contains(needle)
    )
}

fn foreign_count(errors: &[ValidationError]) -> usize {
    errors
        .iter()
        .filter(|e| matches!(e, ValidationError::HandleForeignDeclaration { .. }))
        .count()
}

// ─────────────────────────────── positive ───────────────────────────────

/// Positive: the b5_13 pair with `root.dep_double` bound by an entity-only
/// `backed_by` into import 0 links clean, and L11 records it as authenticated.
/// The codegen lane composes (WS3.1): with `codegen` set on the linked config
/// the same pair is admitted.
#[test]
fn ws3_3_an_import_backed_nat_declaration_links() {
    let dep = dependency("b5_dep", Far::Defines, None);
    assert_eq!(
        validate_module(&dep),
        Vec::new(),
        "the dependency validates"
    );
    let root = root(&dep, true);
    let report = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    );
    assert!(report.is_ok(), "{:?}", report.errors());
    let local = root.function_by_name(SYMBOL).unwrap().id;
    let authenticated: Vec<_> = report
        .authenticated()
        .expect("clean")
        .authenticated_handle_declarations()
        .collect();
    assert_eq!(authenticated, vec![local]);
    assert_eq!(report.authenticated_call_edges(), 1);
    // The pinned runtime declarations are FFI externs (the runtime is linked
    // trusted base, never an import); `dep_double` is bound, not among them.
    assert!(
        report
            .unbound_declarations()
            .iter()
            .all(|decl| decl.symbol.starts_with("trust_bignum_nat_")),
        "{:?}",
        report.unbound_declarations()
    );

    let codegen = validate_linked_module_with_config(
        &root,
        &ModuleSet::new([&dep]),
        &ValidationConfig::pinned().with_codegen(true),
    );
    assert!(codegen.is_ok(), "{:?}", codegen.errors());
}

// ────────────────────────────── negative twin ──────────────────────────────

/// Negative twin: the SAME root under every single-module lane is exactly one
/// `HandleForeignDeclaration`, and the refusal says why — only the linked walk
/// can authenticate the binding.
#[test]
fn ws3_3_the_same_root_is_refused_outside_the_linked_walk() {
    let dep = dependency("b5_dep", Far::Defines, None);
    let root = root(&dep, true);
    let why = "admitted only by validate_linked_module, which authenticates the dependency";
    let plain = validate_module(&root);
    assert!(only_foreign(&plain, why), "{plain:?}");
    let authority = validate_module_with_authority(&root, &RejectingModuleProofAuthority);
    assert!(only_foreign(&authority, why), "{authority:?}");
    // Plain codegen keeps refusing (it may add its own layers' errors).
    let codegen = validate_module_for_codegen(&root);
    assert_eq!(foreign_count(&codegen), 1, "{codegen:?}");
    let rendered = plain[0].to_string();
    assert!(rendered.contains("pinned or import-backed"), "{rendered}");
}

/// Mutation control: WITHOUT the `backed_by` the linked walk refuses the very
/// same pair, and the refusal names `backed_by` as the fix — so it is the
/// binding, and nothing else in the shape, that the new rule admits. The
/// implicit call edge (L10) still resolves; rule 6 is what refuses.
#[test]
fn ws3_3_mutation_control_an_unbound_declaration_stays_refused_in_every_lane() {
    let dep = dependency("b5_dep", Far::Defines, None);
    let root = root(&dep, false);
    let fix = "no `backed_by` binds it to an import";
    let linked = linked_errors(&root, &[&dep]);
    assert!(only_foreign(&linked, fix), "{linked:?}");
    let plain = validate_module(&root);
    assert!(only_foreign(&plain, fix), "{plain:?}");
    let authority = validate_module_with_authority(&root, &RejectingModuleProofAuthority);
    assert!(only_foreign(&authority, fix), "{authority:?}");
}

// ───────────────────────── adversarial controls ─────────────────────────

/// (a) The dependency merely DECLARES `dep_double` (no body, no backing). The
/// hardened R4 refuses the far site (`FarSiteIsUnbackedDeclaration`), and the
/// linked walk refuses the root (the dependency's own bare declaration is
/// itself a foreign declaration, so the row fails first).
#[test]
fn ws3_3_a_far_bare_declaration_is_refused() {
    let dep = dependency("b5_dep", Far::Declares, None);
    let root = root(&dep, true);
    let verified = root.verify_import(ImportId::new(0), &dep).unwrap();
    let local = root.function_by_name(SYMBOL).unwrap().id;
    let reference = ExternRef::new(ImportId::new(0), SYMBOL);
    assert_eq!(
        root.resolve_handle_declaration(&reference, local, &verified, &Default::default())
            .map(|_| ()),
        Err(ImportVerificationError::FarSiteIsUnbackedDeclaration {
            symbol: SYMBOL.into()
        })
    );
    let linked = linked_errors(&root, &[&dep]);
    assert!(
        matches!(
            linked.as_slice(),
            [ValidationError::ImportedModuleInvalid { import: 0, first, .. }]
                if first.contains(SYMBOL) && first.contains("no `backed_by` binds it")
        ),
        "{linked:?}"
    );
}

/// (b) The dependency's `dep_double` is `Nat -> u64` while the root declares
/// `Nat -> Nat`: R6 `SignatureMismatch`, named in the refusal.
#[test]
fn ws3_3_a_skewed_far_signature_is_refused() {
    let dep = dependency("b5_dep", Far::DefinesReturningU64, None);
    assert_eq!(validate_module(&dep), Vec::new());
    let root = root(&dep, true);
    let linked = linked_errors(&root, &[&dep]);
    assert!(only_foreign(&linked, "signature mismatch"), "{linked:?}");
}

/// (c) The dependency was recompiled: its digest is not the recorded one
/// (`DigestMismatch`, named at the import row), and the handle site adds
/// nothing on top of the row-level refusal.
#[test]
fn ws3_3_a_recompiled_dependency_is_a_digest_mismatch() {
    let dep = dependency("b5_dep", Far::Defines, None);
    let root = root(&dep, true);
    let recompiled = dependency("b5_dep", Far::DefinesAs(Producer::Clean), None);
    let mut recompiled = recompiled;
    function_mut(&mut recompiled, SYMBOL).display_path = Some("dep::dep_double_v2".into());
    assert_ne!(recompiled.stable_digest(), dep.stable_digest());
    let resolver = |_: &ModuleImport| Some(&recompiled);
    let errors =
        validate_linked_module(&root, &resolver, &RejectingModuleProofAuthority).into_errors();
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::UnauthenticatedImport { import: 0, site: "import", detail }]
                if detail.contains("is not the recorded")
        ),
        "{errors:?}"
    );
}

/// (d) The dependency's `dep_double` is recorded as produced by tRust while
/// the import row says Clean: R5 `ProducerMismatch`.
#[test]
fn ws3_3_a_producer_mismatch_is_refused() {
    let dep = dependency("b5_dep", Far::DefinesAs(Producer::TRust), None);
    assert_eq!(validate_module(&dep), Vec::new());
    let root = root(&dep, true);
    let linked = linked_errors(&root, &[&dep]);
    assert!(
        only_foreign(&linked, "the far function was produced by"),
        "{linked:?}"
    );
}

/// (e) A PINNED symbol carrying a `backed_by` is never this site: the
/// pinned-symbol rules own it. Its binding is resolved as an ordinary call
/// edge (and refused, because the dependency only declares the runtime), and
/// no `HandleForeignDeclaration` names it in any lane.
#[test]
fn ws3_3_a_pinned_symbol_with_backed_by_keeps_the_pinned_rules() {
    const PINNED: &str = "trust_bignum_nat_add";
    let dep = dependency("b5_dep", Far::Defines, None);
    let mut root = root(&dep, true);
    function_mut(&mut root, PINNED).summary = Some(
        FunctionSummary::new()
            .with_params(vec!["a".to_string(), "b".to_string()])
            .backed_by(ExternRef::new(ImportId::new(0), PINNED)),
    );
    let names_pinned = |errors: &[ValidationError]| {
        errors.iter().any(|e| {
            matches!(e, ValidationError::HandleForeignDeclaration { name, .. } if name == PINNED)
        })
    };
    let plain = validate_module(&root);
    assert!(!names_pinned(&plain), "{plain:?}");
    let linked = linked_errors(&root, &[&dep]);
    assert!(!names_pinned(&linked), "{linked:?}");
    assert_eq!(foreign_count(&linked), 0, "{linked:?}");
    assert!(
        matches!(
            linked.as_slice(),
            [ValidationError::UnauthenticatedImport { import: 0, site: "call", detail }]
                if detail.contains(PINNED)
        ),
        "{linked:?}"
    );
}

/// (f) CHAIN LAUNDERING (REVIEW). `mid` re-declares `dep_double` with an
/// entity-only `backed_by` into `leaf`. The chain is admitted only when it
/// bottoms out in a definition the walk checked; when `leaf` omits the symbol,
/// or defines it at the wrong signature, the root is refused.
#[test]
fn ws3_3_a_re_declaration_chain_must_bottom_out_in_a_checked_definition() {
    // The honest chain: leaf defines, mid re-declares, root imports mid.
    let leaf = dependency("leaf", Far::Defines, None);
    let mid = dependency("mid", Far::Redeclares, Some(&leaf));
    let root_ok = root(&mid, true);
    let report = validate_linked_module(
        &root_ok,
        &ModuleSet::new([&mid, &leaf]),
        &RejectingModuleProofAuthority,
    );
    assert!(report.is_ok(), "{:?}", report.errors());

    for (label, leaf) in [
        (
            "leaf omits dep_double",
            dependency("leaf", Far::Omits, None),
        ),
        (
            "leaf defines dep_double: Nat -> u64",
            dependency("leaf", Far::DefinesReturningU64, None),
        ),
    ] {
        let mid = dependency("mid", Far::Redeclares, Some(&leaf));
        let root = root(&mid, true);
        let errors = linked_errors(&root, &[&mid, &leaf]);
        assert!(
            matches!(
                errors.as_slice(),
                [ValidationError::ImportedModuleInvalid { import: 0, first, .. }]
                    if first.contains("HandleForeignDeclaration") || first.contains(SYMBOL)
            ),
            "{label}: {errors:?}"
        );

        // Mutation control for the R4 hardening: the general R4 (the call-
        // edge site) ADMITS mid's re-declaration, because an entity-only
        // `backed_by` "records a backing". The handle site refuses it unless
        // mid's own verdict vouches for it — so a regression to the general
        // R4 would let this chain validate.
        let verified = root.verify_import(ImportId::new(0), &mid).unwrap();
        let local = root.function_by_name(SYMBOL).unwrap().id;
        let reference = ExternRef::new(ImportId::new(0), SYMBOL);
        assert!(
            root.resolve_extern_ref(&reference, local, ExternRefSite::CallEdge, &verified)
                .is_ok(),
            "{label}: the general R4 admits a re-declaration that records a backing"
        );
        assert_eq!(
            root.resolve_handle_declaration(&reference, local, &verified, &Default::default())
                .map(|_| ()),
            Err(ImportVerificationError::FarSiteIsUnbackedDeclaration {
                symbol: SYMBOL.into()
            }),
            "{label}"
        );
    }
}

/// (g) A far `AvailableExternally` body copy is refused as the far site: the
/// linker binds that symbol to another object, never to the copy validated.
#[test]
fn ws3_3_a_far_available_externally_copy_is_refused() {
    let dep = dependency("b5_dep", Far::DefinesAvailableExternally, None);
    assert_eq!(validate_module(&dep), Vec::new());
    let root = root(&dep, true);
    let linked = linked_errors(&root, &[&dep]);
    assert!(
        only_foreign(&linked, "`available_externally` body copy"),
        "{linked:?}"
    );
}

// ─────────────────────── review: adversarial additions ───────────────────────

/// Review (h) SHADOWED CHAIN. The root binds `dep_double` to `mid`, whose
/// re-declaration bottoms out in `leaf`'s checked `Nat -> Nat` body — but the
/// root ALSO directly imports `rogue`, which DEFINES and exports `dep_double`
/// at `Nat -> u64`. A declaration is not an exporter, so the call-edge
/// ambiguity rule sees ONE exporter (`rogue`) and says nothing, while the
/// handle site authenticates the chain: the linker is left with two
/// definitions of the symbol, one of them never checked against the root's
/// signature. The handle site must refuse a direct exporter that is not the
/// body the binding bottoms out in.
#[test]
fn ws3_3_review_a_direct_exporter_shadowing_a_chain_is_refused() {
    let leaf = dependency("leaf", Far::Defines, None);
    let mid = dependency("mid", Far::Redeclares, Some(&leaf));
    let rogue = dependency("rogue", Far::DefinesReturningU64, None);
    assert_eq!(validate_module(&rogue), Vec::new());
    let mut shadowed = root(&mid, true);
    shadowed
        .intern_import(
            ModuleImport::new(rogue.name.clone(), rogue.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    let errors = linked_errors(&shadowed, &[&mid, &leaf, &rogue]);
    assert!(
        only_foreign(&errors, "is also exported by import #1"),
        "{errors:?}"
    );

    // Control: the honest diamond — the root imports `leaf` directly too, so
    // the direct exporter IS the body the chain bottoms out in — links.
    let mut diamond = root(&mid, true);
    diamond
        .intern_import(
            ModuleImport::new(leaf.name.clone(), leaf.stable_digest())
                .with_producer(Producer::Clean),
        )
        .expect("Module::intern_import: test fixture");
    let report = validate_linked_module(
        &diamond,
        &ModuleSet::new([&mid, &leaf]),
        &RejectingModuleProofAuthority,
    );
    assert!(report.is_ok(), "{:?}", report.errors());
}

/// Review (i) the binding names ANOTHER symbol than the declaration's own:
/// the linker binds the declaration's name, so a `backed_by` naming a
/// different far function authenticates nothing the call reaches
/// (`LinkSymbolMismatch`).
#[test]
fn ws3_3_review_a_binding_to_another_symbol_is_refused() {
    let dep = dependency("b5_dep", Far::Defines, None);
    let mut root = root(&dep, true);
    let decl = function_mut(&mut root, SYMBOL);
    decl.name = "my_double".into();
    let errors = linked_errors(&root, &[&dep]);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::HandleForeignDeclaration { name, detail, .. }]
                if name == "my_double" && detail.contains("link symbol")
        ),
        "{errors:?}"
    );
}

/// Review (j) an `ExternalWeak` local handle declaration: the linker may bind
/// it to NULL, so it is not a checked handle origin even though the claim-free
/// call-edge site admits the weak-import idiom.
#[test]
fn ws3_3_review_a_weak_local_declaration_is_refused() {
    let dep = dependency("b5_dep", Far::Defines, None);
    let mut root = root(&dep, true);
    function_mut(&mut root, SYMBOL).linkage = Linkage::ExternalWeak;
    let errors = linked_errors(&root, &[&dep]);
    assert_eq!(foreign_count(&errors), 1, "{errors:?}");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::HandleForeignDeclaration { detail, .. }
                if detail.contains("interposable")
        )),
        "{errors:?}"
    );
}

/// Review (k) an interposable far definition (`Weak`): the linker may replace
/// the checked body with another object's.
#[test]
fn ws3_3_review_a_weak_far_definition_is_refused() {
    let mut dep = dependency("b5_dep", Far::Defines, None);
    function_mut(&mut dep, SYMBOL).linkage = Linkage::Weak;
    let root = root(&dep, true);
    let errors = linked_errors(&root, &[&dep]);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::HandleForeignDeclaration { detail, .. }
                if detail.contains("interposable")
        )),
        "{errors:?}"
    );
    assert!(
        !validate_linked_module(
            &root,
            &ModuleSet::new([&dep]),
            &RejectingModuleProofAuthority
        )
        .is_ok()
    );
}

/// Review (l) a `backed_by` citing an import row that does not exist: the
/// linked walk must not admit the declaration (the row-level error names it).
#[test]
fn ws3_3_review_a_dangling_binding_is_not_admitted() {
    let dep = dependency("b5_dep", Far::Defines, None);
    let mut root = root(&dep, true);
    function_mut(&mut root, SYMBOL).summary = Some(binding(ImportId::new(7)));
    let report = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    );
    assert!(!report.is_ok(), "a dangling binding must not link");
    assert!(
        report
            .errors()
            .iter()
            .any(|e| matches!(e, ValidationError::UnauthenticatedImport { import: 7, .. })),
        "{:?}",
        report.errors()
    );
}
