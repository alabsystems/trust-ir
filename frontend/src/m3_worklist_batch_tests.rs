// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Actual source/compiler-context consumers of the ordinary worklist. No
//! hand-built key, signature-only identity, symbol-only dedup or proof claim.

use super::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use std::collections::HashSet;
use std::path::Path;

struct ActualSourceChecks {
    ran: bool,
}

fn find(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_body_owners()
        .find(|def| {
            matches!(
                tcx.def_kind(def.to_def_id()),
                DefKind::Fn | DefKind::AssocFn
            ) && tcx.item_name(def.to_def_id()).as_str() == name
        })
        .unwrap_or_else(|| panic!("actual source has no {name}"))
}

fn root<'tcx>(tcx: TyCtxt<'tcx>, name: &str, concrete: ty::Ty<'tcx>) -> MonoInstance<'tcx> {
    let def = find(tcx, name);
    let args = args_for_single_type_param(tcx, def.to_def_id(), concrete);
    MonoInstance { def, args }
}

impl Callbacks for ActualSourceChecks {
    fn after_expansion(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        self.ran = true;
        check_shared_folder_and_original_root_order(tcx);
        check_distinct_generic_instances_with_identical_abi(tcx);
        check_method_owner_identity_and_legacy_root_exports(tcx);
        check_nominal_family_refusal_and_region_canonicalization(tcx);
        check_current_function_item_and_pattern_apis(tcx);
        check_bound_or_unresolved_function_arguments_refuse(tcx);
        check_explicit_by_use_is_not_a_transparent_wrapper(tcx);
        Compilation::Stop
    }
}

fn check_shared_folder_and_original_root_order(tcx: TyCtxt<'_>) {
    let roots = [
        root(tcx, "two", tcx.types.i64),
        root(tcx, "one", tcx.types.i64),
        root(tcx, "two", tcx.types.i64),
    ];
    let (wl, ordinals) = worklist_batch::collect_roots(tcx, roots).expect("collect actual roots");
    assert_eq!(ordinals, [0, 1, 0]);
    let folder = find(tcx, "fold");
    assert_eq!(
        wl.instances
            .iter()
            .filter(|instance| instance.def == folder)
            .count(),
        1
    );
    assert_eq!(
        wl.instances.len(),
        3,
        "two source roots share one actual folder"
    );
    let mut wrong_base = ModuleBuilder::new("wrong-source-base");
    let error = emit_worklist(
        tcx,
        &mut wrong_base,
        &wl,
        WorklistSymbols::SourceOwned,
        1,
        true,
    )
    .err()
    .expect("a caller cannot invent the builder's FuncId base");
    assert!(error.0.contains("actual builder id"), "{error:?}");
    let refused = wrong_base.build().expect("ModuleBuilder::build: test fixture");
    assert!(refused.functions.is_empty());
    assert!(
        refused.structs.is_empty(),
        "base refusal precedes nominal layout mutation"
    );

    // A prior function makes every actual root id NONZERO. Do not substitute
    // the root ordinal or assume the second requested root is the first body.
    let mut mb = ModuleBuilder::new("actual-batch");
    let sig = mb.add_func_type(vec![], vec![]);
    let mut prefix = mb.function("prefix", sig);
    let entry = prefix.create_block();
    prefix.switch_to_block(entry);
    prefix.ret(vec![]);
    prefix.build();
    let base = mb.peek_next_func_id().expect("peek_next_func_id: test fixture").index();
    let lowered = emit_worklist(tcx, &mut mb, &wl, WorklistSymbols::SourceOwned, base, true)
        .expect("actual batch emission");
    let selected = worklist_batch::selected_roots(&lowered, &ordinals).expect("retained root ids");
    assert_eq!(
        selected
            .iter()
            .map(|root| root.func_id.index())
            .collect::<Vec<_>>(),
        [base, base + 1, base]
    );
    let folder_ordinal = wl
        .instances
        .iter()
        .position(|instance| instance.def == folder)
        .unwrap();
    assert_eq!(
        wl.by_key[&wl.instances[folder_ordinal].key()] as usize,
        folder_ordinal
    );
    let folder_id = lowered[folder_ordinal].func_id;
    let runners: Vec<_> = selected
        .iter()
        .map(|root| add_nary_runner(&mut mb, root, &[]))
        .collect();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    let names: HashSet<_> = module
        .functions
        .iter()
        .map(|function| &function.name)
        .collect();
    assert_eq!(names.len(), module.functions.len());
    for source in &selected {
        let function = module.function_by_id(source.func_id).unwrap();
        assert!(function.instructions().any(|node| matches!(
            node.inst, trust_ir::Inst::Call { callee, .. } if callee == folder_id
        )));
    }
    for (runner, expected) in runners.into_iter().zip([2, 1, 2]) {
        assert_eq!(interp_int(&module, runner).unwrap(), expected);
    }
    assert!(worklist_batch::selected_roots(&lowered, &[u32::MAX]).is_err());
}

fn check_distinct_generic_instances_with_identical_abi(tcx: TyCtxt<'_>) {
    let u32_root = root(tcx, "same_abi", tcx.types.u32);
    let i64_root = root(tcx, "same_abi", tcx.types.i64);
    assert_eq!(u32_root.def, i64_root.def);
    assert_ne!(u32_root.args, i64_root.args);
    let (wl, ordinals) = worklist_batch::collect_roots(tcx, [u32_root.clone(), i64_root, u32_root])
        .expect("typed distinct generic arguments");
    assert_eq!(ordinals, [0, 1, 0]);
    assert_eq!(wl.instances.len(), 2);
    let mut mb = ModuleBuilder::new("same-abi-distinct-source");
    let lowered = emit_worklist(tcx, &mut mb, &wl, WorklistSymbols::SourceOwned, 0, true).unwrap();
    assert_eq!(lowered[0].param_tys, lowered[1].param_tys);
    assert_eq!(lowered[0].ret_ty, lowered[1].ret_ty);
    assert_ne!(lowered[0].func_id, lowered[1].func_id);
    assert_ne!(lowered[0].name, lowered[1].name);
    for (instance, lowered) in wl.instances.iter().zip(&lowered) {
        assert_eq!(
            lowered.name,
            tcx.symbol_name(Instance::new_raw(instance.def.to_def_id(), instance.args))
                .name
        );
    }
    let errors = trust_ir_build::validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(errors.is_empty(), "{errors:?}");
}

fn check_method_owner_identity_and_legacy_root_exports(tcx: TyCtxt<'_>) {
    let mut mb = ModuleBuilder::new("actual-trait-owners");
    let (yes, n) = lower_trait_caller(tcx, &mut mb, find(tcx, "yes"), "i64", 0).unwrap();
    let (no, _) = lower_trait_caller(tcx, &mut mb, find(tcx, "no"), "i64", n).unwrap();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(module.function_by_id(yes.caller).unwrap().name, "yes__i64");
    assert_eq!(module.function_by_id(no.caller).unwrap().name, "no__i64");
    assert!(interp_bool(&module, yes.caller).unwrap());
    assert!(!interp_bool(&module, no.caller).unwrap());
    let methods: Vec<_> = module
        .functions
        .iter()
        .filter(|function| function.id != yes.caller && function.id != no.caller)
        .collect();
    assert_eq!(methods.len(), 2);
    assert_eq!(
        module.func_type(methods[0].ty),
        module.func_type(methods[1].ty)
    );
    assert_ne!(methods[0].name, methods[1].name);
    // Legacy standalone exports still use the unchanged explicit adapter.
    let legacy = emit_construct_roundtrip_module(tcx, find(tcx, "two")).unwrap();
    assert!(legacy
        .functions
        .iter()
        .any(|function| function.name == "two__i64"));
    assert!(legacy
        .functions
        .iter()
        .any(|function| function.name == "fold__i64"));
}

fn check_nominal_family_refusal_and_region_canonicalization(tcx: TyCtxt<'_>) {
    let (wl, _) = worklist_batch::collect_roots(
        tcx,
        [
            root(tcx, "one", tcx.types.i64),
            root(tcx, "other", tcx.types.i64),
        ],
    )
    .unwrap();
    let mut mb = ModuleBuilder::new("different-nominal-enums");
    let error = emit_worklist(tcx, &mut mb, &wl, WorklistSymbols::SourceOwned, 0, true)
        .err()
        .expect("the existing single-nominal model cannot own two enums");
    assert!(error.0.contains("distinct enums"), "{error:?}");
    let region_root = root(tcx, "borrow_chain", tcx.types.i64);
    let (wl, ordinals) =
        worklist_batch::collect_roots(tcx, [region_root.clone(), region_root]).unwrap();
    assert_eq!(ordinals, [0, 0]);
    assert_eq!(wl.instances.len(), 2);
    for instance in &wl.instances {
        assert_eq!(
            instance.args,
            tcx.normalize_erasing_regions(
                TypingEnv::fully_monomorphized(),
                ty::Unnormalized::new(instance.args),
            )
        );
    }
    assert!(worklist_batch::collect_roots(tcx, []).is_err());
}

fn check_current_function_item_and_pattern_apis(tcx: TyCtxt<'_>) {
    let roots = [
        root(tcx, "generic_chain", tcx.types.u32),
        root(tcx, "generic_chain", tcx.types.i64),
        root(tcx, "concrete_alias", tcx.types.i64),
        root(tcx, "signed_pattern", tcx.types.i64),
    ];
    let (worklist, ordinals) = worklist_batch::collect_roots(tcx, roots).unwrap();
    let mut builder = ModuleBuilder::new("current-rustc-call-and-pattern-apis");
    let lowered = emit_worklist(
        tcx,
        &mut builder,
        &worklist,
        WorklistSymbols::SourceOwned,
        0,
        true,
    )
    .unwrap();
    let selected = worklist_batch::selected_roots(&lowered, &ordinals).unwrap();
    let cases: [&[(i128, i128)]; 4] = [
        &[(0, 0), (u32::MAX as i128, u32::MAX as i128)],
        &[(i64::MIN as i128, i64::MIN as i128), (7, 7)],
        &[(-7, -7), (i64::MAX as i128, i64::MAX as i128)],
        &[(-7, 17), (0, 23), (1, 31), (i64::MIN as i128, 31)],
    ];
    let mut runners = Vec::new();
    for (instance, cases) in selected.iter().zip(cases) {
        for &(input, expected) in cases {
            runners.push((
                add_nary_runner(&mut builder, instance, &[input]),
                instance.ret_ty.clone(),
                expected,
            ));
        }
    }
    let module = builder.build().expect("actual source module");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    for (runner, result_ty, expected) in runners {
        let outcome = Interpreter::with_module(&module)
            .execute_func(runner, [])
            .unwrap();
        assert_eq!(
            outcome.returns,
            [InterpretValue::int(result_ty, expected).unwrap()]
        );
    }
}

fn check_bound_or_unresolved_function_arguments_refuse(tcx: TyCtxt<'_>) {
    let def = find(tcx, "identity").to_def_id();
    let env = TypingEnv::fully_monomorphized();
    let unresolved = ty::GenericArgs::identity_for_item(tcx, def);
    let unresolved_ty = ty::Ty::new_fn_def(tcx, def, ty::Binder::dummy(unresolved));
    let error = resolve_user_call(tcx, env, unresolved, unresolved_ty)
        .err()
        .expect("an unresolved source type cannot become a monomorphic instance");
    assert!(error.0.contains("not fully monomorphic"), "{error:?}");

    let bound = ty::Ty::new_bound(
        tcx,
        ty::INNERMOST,
        ty::BoundTy {
            var: ty::BoundVar::from_u32(0),
            kind: ty::BoundTyKind::Anon,
        },
    );
    let bound_args = tcx.mk_args(&[bound.into()]);
    let bound_vars =
        tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon)]);
    let bound_ty = ty::Ty::new_fn_def(tcx, def, ty::Binder::bind_with_vars(bound_args, bound_vars));
    let error = resolve_user_call(tcx, env, ty::GenericArgs::empty(), bound_ty)
        .err()
        .expect("a higher-ranked function item cannot shed its binder");
    assert!(
        error.0.contains("late-bound function arguments"),
        "{error:?}"
    );
}

fn check_explicit_by_use_is_not_a_transparent_wrapper(tcx: TyCtxt<'_>) {
    let (worklist, _) =
        worklist_batch::collect_roots(tcx, [root(tcx, "explicit_use", tcx.types.i64)]).unwrap();
    let mut builder = ModuleBuilder::new("explicit-by-use-refusal");
    let error = emit_worklist(
        tcx,
        &mut builder,
        &worklist,
        WorklistSymbols::SourceOwned,
        0,
        true,
    )
    .err()
    .expect("explicit .use retains its existing unsupported semantics");
    assert!(error.0.contains("ByUse"), "{error:?}");
}

#[test]
fn actual_multi_root_compilation_reuses_typed_instances_and_retains_root_and_owner_custody() {
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/m3_multi_root_corpus.rs");
    let mut args = vec![
        "trust_ir_frontend".into(),
        fixture.display().to_string(),
        "--crate-type=lib".into(),
        "-Ztrust-verify=off".into(),
    ];
    // Exactly the existing artifact-only lane: this test checks actual THIR
    // lowering/validation/interpretation, not Trust verification or codegen.
    crate::append_matching_rustc_sysroot(&mut args).expect("matching installed Trust compiler");
    let mut checks = ActualSourceChecks { ran: false };
    rustc_driver::run_compiler(&args, &mut checks);
    assert!(checks.ran, "the actual source consumer did not execute");
}

#[test]
fn worklist_function_id_boundaries_refuse_wrapping() {
    assert_eq!(
        worklist_batch::function_id(0, u32::MAX).unwrap(),
        FuncId::new(u32::MAX)
    );
    assert_eq!(
        worklist_batch::function_id(u32::MAX, 0).unwrap(),
        FuncId::new(u32::MAX)
    );
    assert_eq!(
        worklist_batch::function_id(u32::MAX - 1, 1).unwrap(),
        FuncId::new(u32::MAX)
    );
    assert!(worklist_batch::function_id(u32::MAX, 1).is_err());
    assert!(worklist_batch::function_id(1, u32::MAX).is_err());
}
