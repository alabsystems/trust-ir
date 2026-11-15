//! `docs/SPEC_RATIFICATIONS.md` §17 (2026-09-27): aggregate passing has ONE
//! slot predicate (`Module::is_by_value_aggregate_slot`), and the three
//! `StructPassingPolicy` values differ only in where a slot's classification
//! comes from.
//!
//! What trust-ir DECIDES, and this file holds:
//! * `AlwaysMemory` admits no by-value aggregate slot in any `FuncTy` — a
//!   parameter, a return, a refined aggregate, a `Vector`, a `Closure`, and a
//!   signature only a `CallIndirect` names are each refused as
//!   `AlwaysMemoryByValueAggregate`, while the pre-lowered spelling
//!   (`byval` / `sret` pointers) is admitted.
//! * `NativeC` and `Unclassified` require no `ParamAttrs`: under them the
//!   CONSUMER classifies, or refuses (the consumer rows of the must-refuse
//!   corpus), and `validate_module` decides nothing.
//! * The `pass = indirect` placement rule reads the same predicate, so a
//!   refined aggregate slot may carry it and a scalar slot may not.

use trust_ir::{
    ClosureTy, Endianness, FieldDef, PassMode, Pred, StructDef, StructId, StructPassingPolicy,
    TargetInfo, Ty,
};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn target(policy: StructPassingPolicy) -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: policy,
    }
}

/// `struct Point { a: i32, b: f64 }` (16 bytes, align 8).
fn point(mb: &mut ModuleBuilder) -> Ty {
    Ty::Struct(mb.add_struct(StructDef {
        id: StructId::new(0),
        name: "Point".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::F64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }))
}

/// `fn take(x: <slot>) -> i32 { 0 }`.
fn take(mb: &mut ModuleBuilder, slot: Ty) {
    let ft = mb.add_func_type(vec![slot.clone()], vec![Ty::I32]);
    let mut f = mb.function("take", ft);
    let entry = f.create_block();
    f.add_block_param(entry, slot);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::I32, 0);
    f.ret(vec![zero]);
    f.build();
}

/// The `AlwaysMemoryByValueAggregate` findings, as `(func_ty, slot)`.
fn always_memory_findings(errors: &[ValidationError]) -> Vec<(u32, String)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::AlwaysMemoryByValueAggregate { func_ty, slot, .. } => {
                Some((*func_ty, slot.clone()))
            }
            _ => None,
        })
        .collect()
}

#[test]
fn always_memory_refuses_a_by_value_aggregate_parameter() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "always_memory_param",
        target(StructPassingPolicy::AlwaysMemory),
    );
    let point = point(&mut mb);
    take(&mut mb, point);
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert_eq!(
        always_memory_findings(&errors),
        vec![(0, "parameter 0".to_string())],
        "AlwaysMemory says every aggregate crossing is pre-lowered: {errors:?}"
    );
    assert_eq!(errors.len(), 1, "nothing else is wrong here: {errors:?}");
}

#[test]
fn always_memory_refuses_a_by_value_aggregate_return() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "always_memory_return",
        target(StructPassingPolicy::AlwaysMemory),
    );
    let point = point(&mut mb);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![point.clone()]);
    let mut f = mb.function("make", ft);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let v = f.load(point, p);
    f.ret(vec![v]);
    f.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert_eq!(
        always_memory_findings(&errors),
        vec![(0, "return 0".to_string())],
        "a returned aggregate must be an sret parameter under AlwaysMemory: {errors:?}"
    );
}

#[test]
fn always_memory_refuses_a_refined_aggregate_slot() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "always_memory_refine",
        target(StructPassingPolicy::AlwaysMemory),
    );
    let point = point(&mut mb);
    let top = mb.intern_pred(Pred::Top).expect("Top is canonical");
    let refined = mb.refine_ty(point, top);
    take(&mut mb, refined);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        module.is_by_value_aggregate_slot(&module.func_types[0].params[0]),
        "a refinement has its base's representation"
    );
    let errors = validate_module(&module);
    assert_eq!(
        always_memory_findings(&errors),
        vec![(0, "parameter 0".to_string())],
        "the predicate looks through Refine: {errors:?}"
    );
}

#[test]
fn always_memory_holds_a_signature_only_call_indirect_names() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "always_memory_call_indirect",
        target(StructPassingPolicy::AlwaysMemory),
    );
    let point = point(&mut mb);
    // No function HAS this signature; only the indirect call spells it.
    let callee_sig = mb.add_func_type(vec![point.clone()], vec![]);
    let caller_sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut f = mb.function("caller", caller_sig);
    let entry = f.create_block();
    let fp = f.add_block_param(entry, Ty::Ptr);
    let p = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let v = f.load(point, p);
    f.call_indirect_void(fp, callee_sig, vec![v]);
    f.ret(vec![]);
    f.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(
        module.functions.iter().all(|func| func.ty != callee_sig),
        "the refused signature must be reached only through CallIndirect"
    );
    let errors = validate_module(&module);
    assert_eq!(
        always_memory_findings(&errors),
        vec![(callee_sig.index(), "parameter 0".to_string())],
        "the whole func_types table is scanned, a superset of the call edges: {errors:?}"
    );
}

#[test]
fn always_memory_admits_the_pre_lowered_spelling() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "always_memory_pre_lowered",
        target(StructPassingPolicy::AlwaysMemory),
    );
    let point = point(&mut mb);
    // `fn copy(out: sret *Point, x: byval *Point)`: the argument as a byval
    // pointer, the returned aggregate as the single sret slot, nothing
    // returned by value.
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut f = mb.function("copy", ft);
    let entry = f.create_block();
    let out = f.add_block_param(entry, Ty::Ptr);
    let x = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let v = f.load(point.clone(), x);
    f.store(point, out, v);
    f.ret(vec![]);
    let id = f.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let func = module.function_by_id_mut(id).expect("copy");
    func.attrs.params = vec![
        trust_ir::ParamAttrs {
            sret: true,
            ..Default::default()
        },
        trust_ir::ParamAttrs {
            byval: true,
            ..Default::default()
        },
    ];
    assert_eq!(
        validate_module(&module),
        [],
        "the pre-lowered spelling is what AlwaysMemory asks for"
    );
}

#[test]
fn native_c_and_unclassified_need_no_param_attrs() {
    for policy in [
        StructPassingPolicy::NativeC,
        StructPassingPolicy::Unclassified,
    ] {
        let mut mb = ModuleBuilder::new_with_target_info("no_param_attrs", target(policy));
        let point = point(&mut mb);
        take(&mut mb, point.clone());
        let ft = mb.add_func_type(vec![Ty::Ptr], vec![point.clone()]);
        let mut f = mb.function("make", ft);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(point, p);
        f.ret(vec![v]);
        f.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert!(module.functions.iter().all(|f| f.attrs.params.is_empty()));
        assert_eq!(
            validate_module(&module),
            [],
            "{policy}: no value requires ParamAttrs; the consumer classifies or refuses"
        );
    }
}

#[test]
fn always_memory_refuses_vector_and_closure_slots() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "always_memory_vector_closure",
        target(StructPassingPolicy::AlwaysMemory),
    );
    let vector = Ty::Vector(Box::new(Ty::I32), 4);
    // `ClosureTy::func` is the APPARENT signature; the captures are spread
    // as leading arguments when the closure is applied.
    let code = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let closure = Ty::Closure(mb.add_closure_type(ClosureTy {
        func: code,
        captures: vec![Ty::I64, Ty::I64, Ty::I64],
    }));
    let vector_sig = mb.add_func_type(vec![vector], vec![]);
    let closure_sig = mb.add_func_type(vec![closure], vec![]);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let findings = always_memory_findings(&validate_module(&module));
    for (sig, what) in [(vector_sig, "Vector(I32, 4)"), (closure_sig, "a closure")] {
        assert!(
            findings.contains(&(sig.index(), "parameter 0".to_string())),
            "{what} is a by-value aggregate slot under AlwaysMemory: {findings:?}"
        );
    }
}

#[test]
fn indirect_placement_reads_the_shared_predicate() {
    let mut mb = ModuleBuilder::new_with_target_info(
        "indirect_placement",
        target(StructPassingPolicy::NativeC),
    );
    let point = point(&mut mb);
    let top = mb.intern_pred(Pred::Top).expect("Top is canonical");
    let refined = mb.refine_ty(point, top);
    for (name, slot) in [("refined", refined), ("scalar", Ty::I32)] {
        let ft = mb.add_func_type(vec![slot.clone()], vec![]);
        let mut f = mb.function(name, ft);
        let entry = f.create_block();
        f.add_block_param(entry, slot);
        f.switch_to_block(entry);
        f.ret(vec![]);
        f.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    for func in &mut module.functions {
        func.attrs.params = vec![trust_ir::ParamAttrs {
            pass: Some(PassMode::Indirect { on_stack: false }),
            ..Default::default()
        }];
    }
    let refused: Vec<String> = validate_module(&module)
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidAbiSlotFact { function, .. } => Some(
                module
                    .functions
                    .iter()
                    .find(|f| f.id.index() == *function)
                    .map_or_else(String::new, |f| f.name.clone()),
            ),
            _ => None,
        })
        .collect();
    assert_eq!(
        refused,
        vec!["scalar".to_string()],
        "`indirect` sits on a (refined) aggregate slot and never on a scalar one; the \
         placement rule reads Module::is_by_value_aggregate_slot"
    );
}
