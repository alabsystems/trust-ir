// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// v43 nominal opaque runtime handles: the validator's ORIGIN and TRANSPORT
// rules. The threat model is "a module forges a handle" — by casting a
// pointer into one, loading one from memory, declaring the runtime's entry
// point with a pointer-typed signature, exchanging one runtime's handle with
// another's, or defining the entry point locally. Every forgery below is a
// NAMED refusal; the one positive module is the shape a producer emits.

// WS8.7: the 2026-09-17 proof program's claim repro c11 (F-120), ported from
// `reports/2026-09-17-two-language-proof-program/verify/`.
#[path = "handle_types/c11_nat_handle_limits.rs"]
mod c11_nat_handle_limits;
// WS3.3 (F-048): an import-backed handle declaration, admitted only by the
// linked walk.
#[path = "handle_types/ws3_3_import_backed_handle_declarations.rs"]
mod ws3_3_import_backed_handle_declarations;
// WS3.7 (F-047, memory half): a handle spilled to a SEALED stack slot.
#[path = "handle_types/ws3_7_sealed_handle_slots.rs"]
mod ws3_7_sealed_handle_slots;

use trust_ir::inst::{AllocOrigin, CastOp, ICmpOp};
use trust_ir::{
    Block, BlockId, BodyGate, CallingConv, Constant, Endianness, FieldDef, FuncId, FuncTy,
    Function, Global, HandleTy, Inst, InstrNode, Linkage, Module, StructDef, StructId,
    StructPassingPolicy, TargetInfo, Ty, ValueId, Visibility,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    HandleDeclError, HandleEntryPoint, HandleRegistry, HandleRuntimePin, ModuleBuilder, PinnedTy,
    TRUSTED_HANDLE_RUNTIMES, validate_changed, validate_module, validate_module_for_codegen,
    validate_module_with_authority, validate_module_with_handle_registry,
};

fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
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

fn nat_pin() -> &'static HandleRuntimePin {
    TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins trust_bignum::Nat")
}

/// A second, test-only runtime row: `("Foo", "other::Foo")` with a
/// constructor and a consumer.
const ROW_B: HandleRuntimePin = HandleRuntimePin {
    name: "Foo",
    runtime: "other::Foo",
    calling_conv: CallingConv::C,
    entry_points: &[
        HandleEntryPoint {
            role: "mk",
            symbol: "other_foo_mk",
            def_path: "other::Foo::mk",
            params: &[],
            returns: &[PinnedTy::Handle],
        },
        HandleEntryPoint {
            role: "use",
            symbol: "other_foo_use",
            def_path: "other::Foo::use",
            params: &[PinnedTy::Handle],
            returns: &[PinnedTy::Scalar(Ty::Bool)],
        },
    ],
};

/// Value ids inside `pred`: `X` is the parameter, `Z = is_zero(X)`,
/// `ONE = 1u64`, `O = from_u64(ONE)`, `R = sub(X, O)`.
const X: ValueId = ValueId::new(0);
const Z: ValueId = ValueId::new(1);
const ONE: ValueId = ValueId::new(2);
const O: ValueId = ValueId::new(3);
const R: ValueId = ValueId::new(4);
/// How many entry points the pinned `trust_bignum::Nat` row declares: five
/// v1 roles plus the Clean kernel's native `Nat` surface (WS3.2). Derived,
/// never spelled, so a later row edit cannot silently make two test
/// functions share an id.
const NAT_ENTRY_COUNT: u32 = TRUSTED_HANDLE_RUNTIMES[0].entry_points.len() as u32;
/// `pred`'s own id: `nat_module()` declares the whole row (ids
/// `0..NAT_ENTRY_COUNT`) and then adds `pred`.
const PRED: FuncId = FuncId::new(NAT_ENTRY_COUNT);
/// A fresh id for one extra function a test adds to `nat_module()`.
const EXTRA: FuncId = FuncId::new(NAT_ENTRY_COUNT + 4);
/// `forge_through`'s two functions, likewise past `pred`.
const NOOP: FuncId = FuncId::new(NAT_ENTRY_COUNT + 1);
const FORGE: FuncId = FuncId::new(NAT_ENTRY_COUNT + 2);

/// `pred(x) = if is_zero(x) { x } else { sub(x, from_u64(1)) }` over the
/// pinned declarations. Blocks: bb0 entry, bb1 zero (returns x), bb2 step.
fn pred_function(
    id: FuncId,
    unop: trust_ir::FuncTyId,
    is_zero: FuncId,
    from_u64: FuncId,
    sub: FuncId,
) -> Function {
    let h = nat();
    let mut pred = Function::new(id, "pred", unop, b(0));
    let mut entry = Block::new(b(0)).with_param(X, h);
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: is_zero,
            args: vec![X],
        })
        .with_result(Z),
    );
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: Z,
        then_target: b(1),
        then_args: vec![],
        else_target: b(2),
        else_args: vec![],
    }));
    let mut zero = Block::new(b(1));
    zero.body
        .push(InstrNode::new(Inst::Return { values: vec![X] }));
    let mut step = Block::new(b(2));
    step.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(ONE),
    );
    step.body.push(
        InstrNode::new(Inst::Call {
            callee: from_u64,
            args: vec![ONE],
        })
        .with_result(O),
    );
    step.body.push(
        InstrNode::new(Inst::Call {
            callee: sub,
            args: vec![X, O],
        })
        .with_result(R),
    );
    step.body
        .push(InstrNode::new(Inst::Return { values: vec![R] }));
    pred.blocks = vec![entry, zero, step];
    pred.body_gate = Some(BodyGate::Gated {
        authority: "handle-types-test".into(),
        evidence: None,
    });
    pred
}

/// The positive module: pinned declarations through the builder plus `pred`.
fn nat_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("nat_pred", target());
    let decls = mb.declare_handle_runtime(nat_pin()).unwrap();
    assert_eq!(decls.handle, nat());
    let unop = mb.add_func_type(vec![nat()], vec![nat()]);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(module.functions.len(), NAT_ENTRY_COUNT as usize);
    assert!(module.functions.iter().all(|f| f.id != PRED));
    module
        .try_add_function(pred_function(
            PRED,
            unop,
            decls.entry("is_zero").unwrap(),
            decls.entry("from_u64").unwrap(),
            decls.entry("sub").unwrap(),
        ))
        .expect("Module::try_add_function: test fixture");
    module
}

fn function_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut Function {
    module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
}

fn pred_mut(module: &mut Module) -> &mut Function {
    function_mut(module, "pred")
}

/// Insert `inst` (with an optional result) into `pred`'s step block, right
/// before its `Return`, where `X`, `Z`, `ONE`, `O` and `R` are all defined.
fn insert_in_step(module: &mut Module, inst: Inst, result: Option<ValueId>) {
    let step = &mut pred_mut(module).blocks[2];
    let at = step.body.len() - 1;
    let mut node = InstrNode::new(inst);
    if let Some(result) = result {
        node = node.with_result(result);
    }
    step.body.insert(at, node);
}

fn has<F: Fn(&ValidationError) -> bool>(errors: &[ValidationError], pred: F) -> bool {
    errors.iter().any(pred)
}

fn nat_struct(module: &mut Module) -> Ty {
    let id = StructId::new(0);
    module.add_struct(StructDef {
        id,
        name: "Holder".into(),
        fields: vec![FieldDef {
            name: "n".into(),
            ty: nat(),
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::StructRepr::C,
        origin: None,
    });
    Ty::Struct(id)
}

fn global(name: &str, ty: Ty) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

// ───────────────────────────── POSITIVE ─────────────────────────────

#[test]
fn pinned_declarations_and_a_transport_body_validate_clean_including_for_codegen() {
    let module = nat_module();
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(validate_module_for_codegen(&module), vec![]);
    // The registry the entry points used is the pinned one.
    assert_eq!(
        validate_module_with_handle_registry(&module, HandleRegistry::pinned()),
        vec![]
    );
    // Every declaration is exactly the pinned shape.
    for entry in nat_pin().entry_points {
        let decl = module
            .functions
            .iter()
            .find(|f| f.name == entry.symbol)
            .unwrap();
        assert!(decl.is_declaration());
        assert_eq!(decl.linkage, Linkage::External);
        assert_eq!(decl.calling_conv, CallingConv::C);
        assert_eq!(decl.display_path.as_deref(), Some(entry.def_path));
        assert_eq!(module.func_type(decl.ty), Some(&nat_pin().func_ty(entry)));
    }
}

#[test]
fn declare_handle_runtime_is_idempotent_per_symbol_and_refuses_a_conflicting_declaration() {
    let mut mb = ModuleBuilder::new_with_target_info("idempotent", target());
    let first = mb.declare_handle_runtime(nat_pin()).unwrap();
    let second = mb.declare_handle_runtime(nat_pin()).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.entries().count(), NAT_ENTRY_COUNT as usize);
    assert_eq!(first.entry("nope"), None);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(module.functions.len(), NAT_ENTRY_COUNT as usize);
    // One signature per distinct shape: `(u64) -> H`, `(H, H) -> H` (`add`,
    // `sub`, `mul`, the bitwise and shift roles, `pow`), `(H) -> bool`
    // (`is_zero`, `fits_u64`), the release's `(H) -> ()`, `(H, H) -> bool`
    // (`beq`, `ble`), `(H) -> u64` (`to_u64`) and `(H) -> H` (`clone`).
    assert_eq!(module.func_types.len(), 7);
    assert_eq!(validate_module(&module), vec![]);

    let mut mb = ModuleBuilder::new_with_target_info("conflict", target());
    let ptr_sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]);
    mb.declare_function("trust_bignum_nat_add", ptr_sig);
    assert_eq!(
        mb.declare_handle_runtime(nat_pin()),
        Err(HandleDeclError::ConflictingDeclaration {
            symbol: "trust_bignum_nat_add".into()
        })
    );
    // Nothing was added by the refused call.
    assert_eq!(
        mb.build()
            .expect("ModuleBuilder::build: test fixture")
            .functions
            .len(),
        1
    );
}

// ─────────────────────── UntrustedHandleRuntime ───────────────────────

#[test]
fn an_unpinned_pair_is_refused_in_a_signature_an_unused_table_and_a_type_attribute() {
    let untrusted = |errors: &[ValidationError], name: &str, runtime: &str| {
        has(
            errors,
            |e| matches!(e, ValidationError::UntrustedHandleRuntime { name: n, runtime: r, .. } if n == name && r == runtime),
        )
    };
    // Same runtime, unpinned name, in a (unused) signature.
    let mut module = nat_module();
    module
        .add_func_type(FuncTy {
            params: vec![Ty::handle("Int", "trust_bignum::Nat")],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    assert!(untrusted(
        &validate_module(&module),
        "Int",
        "trust_bignum::Nat"
    ));

    // Pinned name, foreign runtime, only in an unused type-table entry.
    let mut module = nat_module();
    module.types.push(Ty::handle("Nat", "evil::Nat"));
    assert!(untrusted(&validate_module(&module), "Nat", "evil::Nat"));

    // Unpinned pair as a dialect-op type attribute.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::DialectOp(Box::new(
            trust_ir::dialect::DialectInst::new("example", "marker").with_attr(
                "type",
                trust_ir::dialect::AttrValue::Ty(Ty::handle("Nat", "evil::Nat")),
            ),
        )),
        None,
    );
    assert!(untrusted(&validate_module(&module), "Nat", "evil::Nat"));
}

#[test]
fn an_empty_registry_refuses_the_pinned_nat_module() {
    let module = nat_module();
    let empty = HandleRegistry::from_pins(&[]).unwrap();
    let errors = validate_module_with_handle_registry(&module, &empty);
    assert!(has(&errors, |e| matches!(
        e,
        ValidationError::UntrustedHandleRuntime { name, runtime, .. }
            if name == "Nat" && runtime == "trust_bignum::Nat"
    )));
    // ... and, with no pinned symbols, the declarations are foreign origins.
    assert!(has(
        &errors,
        |e| matches!(e, ValidationError::HandleForeignDeclaration { name, .. } if name == "trust_bignum_nat_add")
    ));
}

// ─────────────────────── InvalidHandleType ───────────────────────

#[test]
fn malformed_identities_are_refused_at_every_occurrence() {
    for (name, runtime) in [
        ("", "trust_bignum::Nat"),
        ("Nat", "trust_bignum::"),
        ("Nat", "-"),
    ] {
        let mut module = nat_module();
        module
            .types
            .push(Ty::Tuple(vec![Ty::Handle(Box::new(HandleTy::new(
                name, runtime,
            )))]));
        let errors = validate_module(&module);
        assert!(
            has(&errors, |e| matches!(
                e,
                ValidationError::InvalidHandleType { .. }
            )),
            "{name:?} {runtime:?}: {errors:?}"
        );
        // Lexically malformed is refused as malformed, not as untrusted.
        assert!(!has(&errors, |e| matches!(
            e,
            ValidationError::UntrustedHandleRuntime { .. }
        )));
    }
}

// ─────────────── HandleEntryPointSignatureMismatch ───────────────

fn signature_mismatch(errors: &[ValidationError], symbol: &str) -> bool {
    has(
        errors,
        |e| matches!(e, ValidationError::HandleEntryPointSignatureMismatch { symbol: s, .. } if s == symbol),
    )
}

#[test]
fn a_pointer_typed_declaration_of_a_pinned_symbol_is_refused() {
    let mut module = nat_module();
    let ptr_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    function_mut(&mut module, "trust_bignum_nat_add").ty = ptr_sig;
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_add"
    ));
}

#[test]
fn a_pinned_symbol_with_the_wrong_convention_variadic_tail_naked_or_return_is_refused() {
    let mut module = nat_module();
    function_mut(&mut module, "trust_bignum_nat_add").calling_conv = CallingConv::Rust;
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_add"
    ));

    let mut module = nat_module();
    let vararg = module
        .add_func_type(FuncTy {
            params: vec![nat(), nat()],
            returns: vec![nat()],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    function_mut(&mut module, "trust_bignum_nat_add").ty = vararg;
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_add"
    ));

    let mut module = nat_module();
    function_mut(&mut module, "trust_bignum_nat_add")
        .attrs
        .naked = true;
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_add"
    ));

    let mut module = nat_module();
    let i32_ret = module
        .add_func_type(FuncTy {
            params: vec![nat()],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    function_mut(&mut module, "trust_bignum_nat_is_zero").ty = i32_ret;
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_is_zero"
    ));
}

#[test]
fn a_pinned_symbol_may_omit_its_display_path_but_not_name_another() {
    let mut module = nat_module();
    function_mut(&mut module, "trust_bignum_nat_add").display_path =
        Some("trust_bignum::Nat::mul".into());
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_add"
    ));

    let mut module = nat_module();
    function_mut(&mut module, "trust_bignum_nat_add").display_path = None;
    assert_eq!(validate_module(&module), vec![]);
}

// ─────────────── HandleEntryPointDefinedLocally / ShadowedByGlobal ───────────────

#[test]
fn a_pinned_symbol_defined_locally_or_weakly_linked_is_refused() {
    let mut module = nat_module();
    let add = function_mut(&mut module, "trust_bignum_nat_add");
    let mut body = Block::new(b(0))
        .with_param(v(0), nat())
        .with_param(v(1), nat());
    body.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    add.blocks.push(body);
    assert!(has(
        &validate_module(&module),
        |e| matches!(e, ValidationError::HandleEntryPointDefinedLocally { symbol, .. } if symbol == "trust_bignum_nat_add")
    ));

    let mut module = nat_module();
    function_mut(&mut module, "trust_bignum_nat_add").linkage = Linkage::Weak;
    assert!(has(
        &validate_module(&module),
        |e| matches!(e, ValidationError::HandleEntryPointDefinedLocally { symbol, .. } if symbol == "trust_bignum_nat_add")
    ));
}

#[test]
fn a_global_named_as_a_pinned_symbol_is_refused() {
    let mut module = nat_module();
    module.globals.push(global("trust_bignum_nat_add", Ty::I64));
    assert!(has(
        &validate_module(&module),
        |e| matches!(e, ValidationError::HandleEntryPointShadowedByGlobal { global, symbol } if global == "trust_bignum_nat_add" && symbol == global)
    ));
}

#[test]
fn the_symbol_namespace_is_guarded_even_in_a_handle_free_module() {
    // The forgery: declare the runtime's symbol with pointer types and never
    // spell a handle anywhere. No handle occurs, so no reachability is
    // built — the symbol rule must still fire.
    let mut module = Module::new("no_handle");
    module.target_info = Some(target());
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut add = Function::new(FuncId::new(0), "trust_bignum_nat_add", sig, b(0));
    add.calling_conv = CallingConv::C;
    module
        .try_add_function(add)
        .expect("Module::try_add_function: test fixture");
    assert!(signature_mismatch(
        &validate_module(&module),
        "trust_bignum_nat_add"
    ));
}

// ─────────────────────── HandleForeignDeclaration ───────────────────────

fn foreign(errors: &[ValidationError], name: &str) -> bool {
    has(
        errors,
        |e| matches!(e, ValidationError::HandleForeignDeclaration { name: n, handle, .. } if n == name && handle.contains("trust_bignum::Nat")),
    )
}

#[test]
fn unpinned_declarations_reaching_a_handle_are_refused_however_the_handle_is_reached() {
    // Directly, as parameters and result.
    let mut module = nat_module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![nat(), nat()],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut evil = Function::new(EXTRA, "evil_add", sig, b(0));
    evil.calling_conv = CallingConv::C;
    module
        .try_add_function(evil)
        .expect("Module::try_add_function: test fixture");
    assert!(foreign(&validate_module(&module), "evil_add"));

    // A constructor from a scalar.
    let mut module = nat_module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::new(EXTRA, "mk", sig, b(0)))
        .expect("Module::try_add_function: test fixture");
    assert!(foreign(&validate_module(&module), "mk"));

    // Only inside a reference.
    let mut module = nat_module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ref(Box::new(nat()))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::new(EXTRA, "peek_ref", sig, b(0)))
        .expect("Module::try_add_function: test fixture");
    assert!(foreign(&validate_module(&module), "peek_ref"));

    // Only through a struct field (table-backed).
    let mut module = nat_module();
    let holder = nat_struct(&mut module);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![holder],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::new(EXTRA, "peek_struct", sig, b(0)))
        .expect("Module::try_add_function: test fixture");
    assert!(foreign(&validate_module(&module), "peek_struct"));

    // A Rust-ABI declaration is no less foreign.
    let mut module = nat_module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![nat()],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut rusty = Function::new(EXTRA, "rust_is_zero", sig, b(0));
    rusty.calling_conv = CallingConv::Rust;
    module
        .try_add_function(rusty)
        .expect("Module::try_add_function: test fixture");
    assert!(foreign(&validate_module(&module), "rust_is_zero"));
}

// ─────────────────────────── InvalidHandleUse ───────────────────────────

fn invalid_use(errors: &[ValidationError]) -> bool {
    has(errors, |e| {
        matches!(e, ValidationError::InvalidHandleUse { .. })
    })
}

fn assert_invalid_use(label: &str, module: &Module) {
    let errors = validate_module(module);
    assert!(invalid_use(&errors), "{label}: {errors:?}");
}

#[test]
fn no_cast_produces_or_consumes_a_handle() {
    // Int -> handle.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::U64,
            dst_ty: nat(),
            operand: ONE,
        },
        Some(v(100)),
    );
    assert_invalid_use("IntToPtr", &module);

    // Ptr -> handle, by every pointer-preserving cast. THE ORDERING HAZARD:
    // `Bitcast`'s width test alone would accept two one-word types, so the
    // transport rule must fire first and the cast rule must refuse too.
    for op in [CastOp::PtrToPtr, CastOp::Bitcast, CastOp::Transmute] {
        let mut module = nat_module();
        insert_in_step(&mut module, Inst::NullPtr, Some(v(100)));
        insert_in_step(
            &mut module,
            Inst::Cast {
                op,
                src_ty: Ty::Ptr,
                dst_ty: nat(),
                operand: v(100),
            },
            Some(v(101)),
        );
        let errors = validate_module(&module);
        assert!(invalid_use(&errors), "{op}: {errors:?}");
        assert!(
            has(&errors, |e| matches!(
                e,
                // The layout-sensitive ops surface the cast refusal as
                // `CastLayoutUnsupported`, the structural ones as
                // `CastIncompatible`; either way the transport rule was not
                // the only guard.
                ValidationError::CastIncompatible { .. }
                    | ValidationError::CastLayoutUnsupported { .. }
            )),
            "{op}: the cast rule is the second line of defence: {errors:?}"
        );
    }

    // Handle -> int.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Cast {
            op: CastOp::PtrToInt,
            src_ty: nat(),
            dst_ty: Ty::U64,
            operand: X,
        },
        Some(v(100)),
    );
    assert_invalid_use("PtrToInt", &module);
}

/// Every memory operation that reaches a handle is refused, with ONE
/// carve-out since WS3.7 (F-047, memory half): a SEALED function-local stack
/// slot — an `Alloca` of exactly one handle whose pointer never escapes,
/// loaded and stored only at its exact type, never read before a dominating
/// store (`ws3_7_sealed_handle_slots.rs` holds that rule's positives and its
/// twins). Everything below goes through a pointer that is not such a slot,
/// or is not a slot at all.
#[test]
fn no_memory_operation_touches_a_handle() {
    let mut module = nat_module();
    insert_in_step(&mut module, Inst::NullPtr, Some(v(100)));
    insert_in_step(
        &mut module,
        Inst::Load {
            ty: nat(),
            ptr: v(100),
            volatile: false,
            align: None,
        },
        Some(v(101)),
    );
    assert_invalid_use("Load", &module);

    let mut module = nat_module();
    insert_in_step(&mut module, Inst::NullPtr, Some(v(100)));
    insert_in_step(
        &mut module,
        Inst::Store {
            ty: nat(),
            ptr: v(100),
            value: X,
            volatile: false,
            align: None,
        },
        None,
    );
    assert_invalid_use("Store", &module);

    // WS3.7: an `Alloca` of one handle whose pointer is never used is a
    // (vacuously) sealed slot — the carve-out, admitted...
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Alloca {
            ty: nat(),
            count: None,
            align: None,
        },
        Some(v(100)),
    );
    assert_eq!(validate_module(&module), vec![]);
    // ...but a dynamic count makes it an ARRAY of handles, which no rule
    // opens.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Alloca {
            ty: nat(),
            count: Some(ONE),
            align: None,
        },
        Some(v(100)),
    );
    assert_invalid_use_saying("Alloca (dynamic count)", &module, "dynamic count");

    let mut module = nat_module();
    insert_in_step(&mut module, Inst::NullPtr, Some(v(100)));
    insert_in_step(
        &mut module,
        Inst::GEP {
            pointee_ty: nat(),
            base: v(100),
            indices: vec![],
            inbounds: false,
        },
        Some(v(101)),
    );
    assert_invalid_use("GEP", &module);

    // The HEAP surface, measured rather than assumed. Neither of these was
    // pinned before the release entry point was ratified, and the question
    // "does the transport rule already cover them?" had to be answered before
    // deciding whether a new rule was needed. It does: both fall to the
    // handle arm's catch-all, because `HeapAlloc` reaches a handle through an
    // INLINE type and `Dealloc` through an OPERAND, and the arm's permitted
    // set is a whitelist. A pinned-runtime handle is not a TrustIr heap
    // allocation, so allocating or freeing one here would be a second,
    // unpinned origin (and a release that bypasses the pinned symbol).
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::HeapAlloc {
            ty: nat(),
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        },
        Some(v(100)),
    );
    assert_invalid_use("HeapAlloc", &module);

    let mut module = nat_module();
    insert_in_step(&mut module, Inst::Dealloc { ptr: X }, None);
    assert_invalid_use("Dealloc", &module);
}

/// WS3.6 (F-047, aggregate half): a lane of a handle-bearing struct is read
/// and written ONLY at exactly its declared type. Both shapes here name the
/// WHOLE aggregate type where the lane is a handle, which is the classic
/// reinterpretation, and both stay refused — the positive twin is
/// [`a_handle_struct_lane_round_trips_at_its_exact_type`].
#[test]
fn no_aggregate_access_reaches_a_handle_field_at_the_wrong_type() {
    for extract in [true, false] {
        let mut module = nat_module();
        let holder = nat_struct(&mut module);
        let sig = module
            .add_func_type(FuncTy {
                params: vec![holder.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut peek = Function::new(EXTRA, "peek", sig, b(0));
        let mut entry = Block::new(b(0)).with_param(v(0), holder.clone());
        let inst = if extract {
            Inst::ExtractField {
                ty: holder,
                aggregate: v(0),
                field: 0,
            }
        } else {
            Inst::InsertField {
                ty: holder,
                aggregate: v(0),
                field: 0,
                value: v(0),
            }
        };
        entry.body.push(InstrNode::new(inst).with_result(v(1)));
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        peek.blocks.push(entry);
        module
            .try_add_function(peek)
            .expect("Module::try_add_function: test fixture");
        assert_invalid_use(
            if extract {
                "ExtractField"
            } else {
                "InsertField"
            },
            &module,
        );
    }
}

/// `fn wrap(n: Nat) -> Acct { let a = Acct { bal: n }; let b = a.bal;
/// Acct { bal: b } }` — the positive shape WS3.6 admits: `MakeAggregate`
/// seeds the lane from an exact-typed handle operand, `ExtractField` reads it
/// back at exactly `Ty::Handle`, `InsertField` writes it back.
fn handle_struct_module(lane_operand: Ty, read_as: Ty) -> Module {
    let mut module = nat_module();
    let holder = nat_struct(&mut module);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![lane_operand.clone()],
            returns: vec![holder.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut wrap = Function::new(EXTRA, "wrap", sig, b(0));
    let mut entry = Block::new(b(0)).with_param(v(0), lane_operand);
    entry.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: holder.clone(),
            variant: None,
            fields: vec![v(0)],
        })
        .with_result(v(1)),
    );
    entry.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: read_as,
            aggregate: v(1),
            field: 0,
        })
        .with_result(v(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::InsertField {
            ty: holder,
            aggregate: v(1),
            field: 0,
            value: v(2),
        })
        .with_result(v(3)),
    );
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
    wrap.blocks.push(entry);
    module
        .try_add_function(wrap)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn a_handle_struct_lane_round_trips_at_its_exact_type() {
    let errors = validate_module(&handle_struct_module(nat(), nat()));
    assert!(errors.is_empty(), "{errors:?}");
}

/// The two mutation controls on that positive: a lane FED by a scalar, and a
/// lane READ as a scalar (the `PtrToInt` leak by another spelling).
#[test]
fn a_handle_struct_lane_refuses_a_scalar_seed_or_a_scalar_read() {
    assert_invalid_use(
        "MakeAggregate lane fed by U64",
        &handle_struct_module(Ty::U64, nat()),
    );
    assert_invalid_use(
        "ExtractField reads the handle lane as U64",
        &handle_struct_module(nat(), Ty::U64),
    );
}

/// A tuple is the second admitted carrier, and a NON-handle lane of a
/// handle-bearing tuple is readable at its own exact type.
#[test]
fn a_handle_tuple_lane_and_its_scalar_sibling_round_trip() {
    let build = |lane: u32, read_as: Ty| -> Module {
        let mut module = nat_module();
        let tuple = Ty::Tuple(vec![Ty::U64, nat()]);
        let sig = module
            .add_func_type(FuncTy {
                params: vec![Ty::U64, nat()],
                returns: vec![tuple.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut pair = Function::new(EXTRA, "pair", sig, b(0));
        let mut entry = Block::new(b(0))
            .with_param(v(0), Ty::U64)
            .with_param(v(1), nat());
        entry.body.push(
            InstrNode::new(Inst::MakeAggregate {
                ty: tuple.clone(),
                variant: None,
                fields: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        entry.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: read_as,
                aggregate: v(2),
                field: lane,
            })
            .with_result(v(3)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        pair.blocks.push(entry);
        module
            .try_add_function(pair)
            .expect("Module::try_add_function: test fixture");
        module
    };
    for (lane, read_as) in [(0, Ty::U64), (1, nat())] {
        let errors = validate_module(&build(lane, read_as));
        assert!(errors.is_empty(), "lane {lane}: {errors:?}");
    }
    // Mutation control: the scalar lane read at the handle's type.
    assert_invalid_use("lane 0 read as a handle", &build(0, nat()));
}

/// Rule 6: every other carrier stays refused in v1 — here a `Record` whose
/// field is a handle, built by the same instruction a struct is built with.
#[test]
fn no_record_carrier_builds_a_handle_lane() {
    let mut module = nat_module();
    let record_id = trust_ir::value::RecordId::new(0);
    module.records.push(trust_ir::ty::RecordDef {
        id: record_id,
        name: "Boxed".into(),
        fields: vec![FieldDef {
            name: "n".into(),
            ty: nat(),
            offset: None,
        }],
    });
    let record = Ty::Record(record_id);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![nat()],
            returns: vec![record.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut wrap = Function::new(EXTRA, "wrap", sig, b(0));
    let mut entry = Block::new(b(0)).with_param(v(0), nat());
    entry.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: record,
            variant: None,
            fields: vec![v(0)],
        })
        .with_result(v(1)),
    );
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    wrap.blocks.push(entry);
    module
        .try_add_function(wrap)
        .expect("Module::try_add_function: test fixture");
    assert_invalid_use("MakeAggregate at a Record", &module);
}

// ───────────────── WS3.6: the enum tag-switch guard (TREE-06) ─────────────────

/// One probe over `fn level(a: E, b: E, fb: Nat) -> Nat`:
///
/// ```text
/// bb0(a, b, fb): t = extract_field <tag> <scrutinee> 0
///                switch t <cases> default <default_target>
/// bb1 / bb2:     [the projection]  return fb
/// ```
///
/// The projection always reads `a` (v0), so pointing `scrutinee` at `b` (v1)
/// is the "switch on a DIFFERENT value" forgery with nothing else changed.
struct EnumProbe {
    scrutinee: ValueId,
    /// `(case value, target block)` in canonical terminator order.
    cases: Vec<(i128, u32)>,
    default_target: u32,
    /// `0` = before the switch in bb0 (no guard at all), else bb1 / bb2.
    project_in: u32,
    project_lane: u32,
    project_as: Ty,
    /// Write a fresh `U64` into `project_lane` instead of reading it.
    insert_u64: bool,
}

impl EnumProbe {
    /// The TREE-06 shape: switch on `a`'s tag, take the `param` case, read
    /// lane 1 as `Nat`.
    fn tree_06() -> Self {
        Self {
            scrutinee: v(0),
            cases: vec![(1, 1)],
            default_target: 2,
            project_in: 1,
            project_lane: 1,
            project_as: nat(),
            insert_u64: false,
        }
    }
}

/// `inductive Lvl | zero | param (n : Nat)` — the TREE-06 enum.
fn lvl_variants(payload: Ty) -> Vec<trust_ir::EnumVariant> {
    vec![
        trust_ir::EnumVariant {
            name: "zero".into(),
            fields: vec![],
            field_names: vec![],
        },
        trust_ir::EnumVariant {
            name: "param".into(),
            fields: vec![payload],
            field_names: vec!["n".into()],
        },
    ]
}

fn enum_probe_module(variants: Vec<trust_ir::EnumVariant>, probe: EnumProbe) -> Module {
    let mut module = nat_module();
    let id = trust_ir::value::EnumId::new(0);
    let def = trust_ir::EnumDef::new(id, "Lvl", variants);
    let tag_ty = def.canonical_tag_repr().expect("a canonical tag repr").ty();
    module.add_enum(def);
    let e = Ty::Enum(id);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![e.clone(), e.clone(), nat()],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut level = Function::new(EXTRA, "level", sig, b(0));
    let projection = |body: &mut Vec<InstrNode>| {
        if probe.insert_u64 {
            body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::U64,
                    value: Constant::Int(7),
                })
                .with_result(v(5)),
            );
            body.push(
                InstrNode::new(Inst::InsertField {
                    ty: e.clone(),
                    aggregate: v(0),
                    field: probe.project_lane,
                    value: v(5),
                })
                .with_result(v(4)),
            );
        } else {
            body.push(
                InstrNode::new(Inst::ExtractField {
                    ty: probe.project_as.clone(),
                    aggregate: v(0),
                    field: probe.project_lane,
                })
                .with_result(v(4)),
            );
        }
    };
    let mut bb0 = Block::new(b(0))
        .with_param(v(0), e.clone())
        .with_param(v(1), e.clone())
        .with_param(v(2), nat());
    bb0.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: tag_ty,
            aggregate: probe.scrutinee,
            field: 0,
        })
        .with_result(v(3)),
    );
    if probe.project_in == 0 {
        projection(&mut bb0.body);
    }
    bb0.body.push(InstrNode::new(Inst::Switch {
        value: v(3),
        default: b(probe.default_target),
        default_args: vec![],
        cases: probe
            .cases
            .iter()
            .map(|(value, target)| trust_ir::inst::SwitchCase {
                value: Constant::Int(*value),
                target: b(*target),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }));
    let mut blocks = vec![bb0];
    for index in 1..=2u32 {
        let mut block = Block::new(b(index));
        if probe.project_in == index {
            projection(&mut block.body);
        }
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        blocks.push(block);
    }
    level.blocks = blocks;
    module
        .try_add_function(level)
        .expect("Module::try_add_function: test fixture");
    module
}

/// TREE-06 (`small-designs/TREE-06-nat-payload-in-constructor`): the handle
/// payload of an enum constructor is projectable under the tag switch that
/// selects the variant carrying it — and the tag read the switch consumes is
/// itself admitted.
#[test]
fn tree_06_nat_payload_in_constructor_projects_under_its_tag_switch() {
    let errors = validate_module(&enum_probe_module(
        lvl_variants(nat()),
        EnumProbe::tree_06(),
    ));
    assert!(errors.is_empty(), "{errors:?}");
}

/// The mutation control: the very same module with the U64 payload validates
/// too, so the positive above measures the handle rule and not the shape.
#[test]
fn tree_06_shape_validates_at_a_scalar_payload_too() {
    let errors = validate_module(&enum_probe_module(
        lvl_variants(Ty::U64),
        EnumProbe {
            project_as: Ty::U64,
            project_in: 0,
            ..EnumProbe::tree_06()
        },
    ));
    assert!(errors.is_empty(), "{errors:?}");
}

/// Every forgery the guard rule closes. Each row is ONE change against
/// [`EnumProbe::tree_06`].
#[test]
fn an_enum_handle_lane_is_read_only_under_a_dominating_tag_switch_case() {
    let refused: [(&str, Vec<trust_ir::EnumVariant>, EnumProbe); 7] = [
        (
            // The plain negative twin: no guard at all.
            "projection outside any switch successor",
            lvl_variants(nat()),
            EnumProbe {
                project_in: 0,
                ..EnumProbe::tree_06()
            },
        ),
        (
            // (a) the switch scrutinises a DIFFERENT enum value.
            "switch on b's tag, projection of a",
            lvl_variants(nat()),
            EnumProbe {
                scrutinee: v(1),
                ..EnumProbe::tree_06()
            },
        ),
        (
            // (b) the selected variant does not carry the lane at that type.
            "case selects the U64 variant, lane read as a handle",
            vec![
                trust_ir::EnumVariant {
                    name: "small".into(),
                    fields: vec![Ty::U64],
                    field_names: vec![],
                },
                trust_ir::EnumVariant {
                    name: "big".into(),
                    fields: vec![nat()],
                    field_names: vec![],
                },
            ],
            EnumProbe {
                cases: vec![(0, 1)],
                ..EnumProbe::tree_06()
            },
        ),
        (
            // (c) two cases target the same successor, so the edge selects
            // no single variant.
            "two cases, one successor",
            lvl_variants(nat()),
            EnumProbe {
                cases: vec![(1, 1), (0, 1)],
                ..EnumProbe::tree_06()
            },
        ),
        (
            // (d) an enum lane is never written in place.
            "insert_field into a handle-bearing enum lane",
            lvl_variants(nat()),
            EnumProbe {
                insert_u64: true,
                ..EnumProbe::tree_06()
            },
        ),
        (
            // (e) the handle's word read as an integer: the PtrToInt leak.
            "handle lane read as U64 under the handle variant's case",
            lvl_variants(nat()),
            EnumProbe {
                project_as: Ty::U64,
                ..EnumProbe::tree_06()
            },
        ),
        (
            // (f) only EXPLICIT cases select; the default edge never does,
            // however few variants can reach it.
            "projection on the default edge",
            lvl_variants(nat()),
            EnumProbe {
                cases: vec![(0, 2)],
                default_target: 1,
                ..EnumProbe::tree_06()
            },
        ),
    ];
    for (label, variants, probe) in refused {
        // Each row is refused by the ENUM rule, named in the detail — not by
        // some unrelated handle refusal the fixture happens to trip.
        let needle = if probe.insert_u64 {
            "insert_field cannot rewrite a lane of a handle-bearing enum"
        } else {
            GUARD_REFUSAL
        };
        assert_invalid_use_saying(label, &enum_probe_module(variants, probe), needle);
    }
}

/// The detail every guard refusal carries.
const GUARD_REFUSAL: &str = "a handle lane of an enum is read only under a tag switch that \
                             selects a variant carrying it";

fn assert_invalid_use_saying(label: &str, module: &Module, needle: &str) {
    let errors = validate_module(module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains(needle)
        )),
        "{label}: expected an InvalidHandleUse saying {needle:?}, got {errors:?}"
    );
}

/// `fn walk(a: Lvl, b: Lvl, fb: Nat) -> Nat` over an explicit CFG, so the
/// guard is measured as EDGE DOMINANCE rather than "the block right after the
/// switch". `blocks` is `(params, body-before-terminator, terminator)` per
/// block; every body may use `a` = v0, `b` = v1, `fb` = v2 and the entry's tag
/// read `t` = v3 (bb0 is always `t = tag a; <terminator>`).
/// One block of [`lvl_cfg_module`]: `(params, body-before-terminator, terminator)`.
type ProbeBlock = (Vec<(ValueId, Ty)>, Vec<InstrNode>, Inst);

fn lvl_cfg_module(blocks: Vec<ProbeBlock>) -> Module {
    let mut module = nat_module();
    let id = trust_ir::value::EnumId::new(0);
    let def = trust_ir::EnumDef::new(id, "Lvl", lvl_variants(nat()));
    module.add_enum(def);
    let e = Ty::Enum(id);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![e.clone(), e.clone(), nat()],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut walk = Function::new(EXTRA, "walk", sig, b(0));
    walk.blocks = blocks
        .into_iter()
        .enumerate()
        .map(|(index, (params, body, terminator))| {
            let mut block = Block::new(b(index as u32));
            for (value, ty) in params {
                block = block.with_param(value, ty);
            }
            block.body = body;
            block.body.push(InstrNode::new(terminator));
            block
        })
        .collect();
    module
        .try_add_function(walk)
        .expect("Module::try_add_function: test fixture");
    module
}

fn lvl() -> Ty {
    Ty::Enum(trust_ir::value::EnumId::new(0))
}

fn lvl_tag() -> Ty {
    trust_ir::EnumDef::new(trust_ir::value::EnumId::new(0), "Lvl", lvl_variants(nat()))
        .canonical_tag_repr()
        .expect("a canonical tag repr")
        .ty()
}

fn tag_of(aggregate: ValueId, result: ValueId) -> InstrNode {
    InstrNode::new(Inst::ExtractField {
        ty: lvl_tag(),
        aggregate,
        field: 0,
    })
    .with_result(result)
}

fn payload_of(aggregate: ValueId, result: ValueId) -> InstrNode {
    InstrNode::new(Inst::ExtractField {
        ty: nat(),
        aggregate,
        field: 1,
    })
    .with_result(result)
}

fn switch_param(selector: ValueId, param_case: u32, default: u32) -> Inst {
    Inst::Switch {
        value: selector,
        default: b(default),
        default_args: vec![],
        cases: vec![trust_ir::inst::SwitchCase {
            value: Constant::Int(1),
            target: b(param_case),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    }
}

fn br(target: u32, args: Vec<ValueId>) -> Inst {
    Inst::Br {
        target: b(target),
        args,
    }
}

fn ret(value: ValueId) -> Inst {
    Inst::Return {
        values: vec![value],
    }
}

fn entry_block(terminator: Inst) -> ProbeBlock {
    (
        vec![(v(0), lvl()), (v(1), lvl()), (v(2), nat())],
        vec![tag_of(v(0), v(3))],
        terminator,
    )
}

/// The guard is edge DOMINANCE: a projection two blocks below the `param`
/// case still sits under it, and is admitted; the same projection moved to
/// the block where the `param` and `default` paths JOIN is not, because the
/// default path reaches it with no variant selected.
///
/// ```text
/// bb0: t = tag a; switch t [1 -> bb1] default bb2
/// bb1: br bb3            bb2: br bb4
/// bb3: [proj?] br bb4    bb4: [proj?] return fb
/// ```
#[test]
fn an_enum_handle_lane_guard_is_edge_dominance_not_adjacency() {
    let build = |project_in: u32| {
        let proj = |block: u32| {
            if block == project_in {
                vec![payload_of(v(0), v(4))]
            } else {
                vec![]
            }
        };
        lvl_cfg_module(vec![
            entry_block(switch_param(v(3), 1, 2)),
            (vec![], vec![], br(3, vec![])),
            (vec![], vec![], br(4, vec![])),
            (vec![], proj(3), br(4, vec![])),
            (vec![], proj(4), ret(v(2))),
        ])
    };
    let chained = validate_module(&build(3));
    assert!(chained.is_empty(), "two blocks below the case: {chained:?}");
    assert_invalid_use_saying("projection at the join", &build(4), GUARD_REFUSAL);
}

/// A loop over a block-parameter enum: the header switches on ITS OWN
/// parameter's tag, the case body projects that parameter and loops back with
/// a different value. Every entry to the body re-runs the switch on the value
/// it projects, so the read is guarded; the same projection hoisted into the
/// header, above the switch, is not (a block is never dominated by its own
/// out-edge).
///
/// ```text
/// bb0(a, b, fb): t = tag a; br bb1(a)
/// bb1(x):        [proj x?] u = tag x; switch u [1 -> bb2] default bb3
/// bb2:           [proj x?] br bb1(b)
/// bb3:           return fb
/// ```
#[test]
fn an_enum_handle_lane_guard_follows_a_loop_header_parameter() {
    let build = |in_header: bool| {
        let mut header = vec![];
        let mut body = vec![];
        if in_header {
            header.push(payload_of(v(10), v(12)));
        } else {
            body.push(payload_of(v(10), v(12)));
        }
        header.push(tag_of(v(10), v(11)));
        lvl_cfg_module(vec![
            entry_block(br(1, vec![v(0)])),
            (vec![(v(10), lvl())], header, switch_param(v(11), 2, 3)),
            (vec![], body, br(1, vec![v(1)])),
            (vec![], vec![], ret(v(2))),
        ])
    };
    let guarded = validate_module(&build(false));
    assert!(guarded.is_empty(), "the loop body: {guarded:?}");
    assert_invalid_use_saying("projection in the header", &build(true), GUARD_REFUSAL);
}

/// The filtered entry point decides the guard exactly as the whole-module one
/// does: it builds the same per-function guard state for every function it
/// validates, so it neither admits an unguarded read nor refuses a guarded one.
#[test]
fn validate_changed_decides_the_enum_guard_like_validate_module() {
    let guarded = enum_probe_module(lvl_variants(nat()), EnumProbe::tree_06());
    assert!(validate_changed(&guarded, &[EXTRA]).is_empty());
    let unguarded = enum_probe_module(
        lvl_variants(nat()),
        EnumProbe {
            project_in: 0,
            ..EnumProbe::tree_06()
        },
    );
    let errors = validate_changed(&unguarded, &[EXTRA]);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains(GUARD_REFUSAL)
        )),
        "{errors:?}"
    );
}

/// A node that reaches a handle AND a nominal dialect type is decided by
/// BOTH rules. The handle rule admits a `make_aggregate` whose handle lane is
/// exact; the dialect rule has no aggregate rule at all, so the tuple that
/// also carries a `Ty::Dialect` lane stays refused — the handle widening may
/// not open what the dialect rule keeps closed. The twin with a `U64` in the
/// dialect's place validates, so the refusal is the dialect lane's.
#[test]
fn a_handle_lane_does_not_admit_a_dialect_lane_beside_it() {
    let build = |other: Ty| {
        let mut module = nat_module();
        let tuple = Ty::Tuple(vec![nat(), other.clone()]);
        let sig = module
            .add_func_type(FuncTy {
                params: vec![nat(), other.clone()],
                returns: vec![tuple.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut mix = Function::new(EXTRA, "mix", sig, b(0));
        let mut entry = Block::new(b(0))
            .with_param(v(0), nat())
            .with_param(v(1), other);
        entry.body.push(
            InstrNode::new(Inst::MakeAggregate {
                ty: tuple,
                variant: None,
                fields: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        mix.blocks.push(entry);
        module
            .try_add_function(mix)
            .expect("Module::try_add_function: test fixture");
        module
    };
    let scalar = validate_module(&build(Ty::U64));
    assert!(scalar.is_empty(), "{scalar:?}");
    let dialect = Ty::Dialect(Box::new(trust_ir::DialectTy::new("example", "value", 1)));
    let errors = validate_module(&build(dialect));
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::InvalidDialectType { .. }
        )),
        "{errors:?}"
    );
}

/// The guard covers EVERY payload lane of a handle-bearing enum, not only an
/// index where some variant carries a handle. `enum E { A(u64, u64), B(Nat) }`
/// has no handle at lane 2 in any variant, yet in a concrete layout A's second
/// word may share bytes with B's handle, so an unguarded `u64` read of lane 2
/// is refused; under a case selecting `A` it is admitted. The mutation control
/// — the same enum with `B(u64)`, which reaches no handle — reads lane 2
/// unguarded under the ordinary enum rules.
#[test]
fn every_payload_lane_of_a_handle_bearing_enum_needs_the_guard() {
    let variants = |b_payload: Ty| {
        vec![
            trust_ir::EnumVariant {
                name: "a".into(),
                fields: vec![Ty::U64, Ty::U64],
                field_names: vec![],
            },
            trust_ir::EnumVariant {
                name: "b".into(),
                fields: vec![b_payload],
                field_names: vec![],
            },
        ]
    };
    let lane_2 = |project_in: u32| EnumProbe {
        cases: vec![(0, 1)],
        project_in,
        project_lane: 2,
        project_as: Ty::U64,
        ..EnumProbe::tree_06()
    };
    assert_invalid_use_saying(
        "unguarded read of a lane no variant has a handle at",
        &enum_probe_module(variants(nat()), lane_2(0)),
        GUARD_REFUSAL,
    );
    let guarded = validate_module(&enum_probe_module(variants(nat()), lane_2(1)));
    assert!(guarded.is_empty(), "under the `a` case: {guarded:?}");
    let handle_free = validate_module(&enum_probe_module(variants(Ty::U64), lane_2(0)));
    assert!(
        handle_free.is_empty(),
        "no handle in the enum: {handle_free:?}"
    );
}

/// The tag lane itself is admitted only at the canonical tag repr: a wider
/// read of it is the same reinterpretation in the one place the rule has to
/// let an integer out.
#[test]
fn an_enum_tag_lane_is_read_only_at_its_canonical_repr() {
    assert_invalid_use(
        "tag lane read as U64",
        &enum_probe_module(
            lvl_variants(nat()),
            EnumProbe {
                project_in: 0,
                project_lane: 0,
                project_as: Ty::U64,
                ..EnumProbe::tree_06()
            },
        ),
    );
}

/// WS3.6: a niche is an integer read of a covering field's invalid values. A
/// handle has no declared valid range, so a descriptor that carves its niche
/// out of a handle field's bytes is refused by name.
#[test]
fn a_niche_lane_cannot_overlap_a_handle_field() {
    let build = |payload: Ty| -> Module {
        let mut module = nat_module();
        let id = trust_ir::value::EnumId::new(0);
        let mut def = trust_ir::EnumDef::new(id, "Lvl", lvl_variants(payload));
        def.layout = Some(trust_ir::EnumLayoutDescriptor {
            encoding: trust_ir::EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: trust_ir::EnumTagRepr::U64,
            },
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![], vec![0]],
        });
        module.add_enum(def);
        module
    };
    let niche = |errors: &[ValidationError]| {
        has(errors, |e| {
            matches!(e, ValidationError::HandleLaneNiche { .. })
        })
    };
    let at_handle = validate_module(&build(nat()));
    assert!(niche(&at_handle), "{at_handle:?}");
    // Mutation control: the identical descriptor over a U64 payload is the
    // ordinary, admitted niche.
    let at_u64 = validate_module(&build(Ty::U64));
    assert!(!niche(&at_u64), "{at_u64:?}");
}

#[test]
fn no_constant_undef_or_global_materializes_a_handle() {
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Const {
            ty: nat(),
            value: Constant::Int(0),
        },
        Some(v(100)),
    );
    assert_invalid_use("Const", &module);

    let mut module = nat_module();
    insert_in_step(&mut module, Inst::Undef { ty: nat() }, Some(v(100)));
    assert_invalid_use("Undef", &module);

    // A handle-typed global, and its address taken.
    let mut module = nat_module();
    module.globals.push(global("stash", nat()));
    assert_invalid_use("Global", &module);
    insert_in_step(
        &mut module,
        Inst::GlobalAddr {
            global: trust_ir::value::GlobalId::new(0),
        },
        Some(v(100)),
    );
    assert_invalid_use("GlobalAddr", &module);

    // An aggregate constant for a struct with a handle field.
    let mut module = nat_module();
    let holder = nat_struct(&mut module);
    insert_in_step(
        &mut module,
        Inst::Const {
            ty: holder.clone(),
            value: Constant::Aggregate(vec![Constant::Int(0)]),
        },
        Some(v(100)),
    );
    assert_invalid_use("Constant::Aggregate", &module);

    // WS3.6 rule 5: widening the handle arm to aggregates does NOT open a
    // seed. `Undef` at the handle-bearing aggregate stays refused, so every
    // such value still originates from `MakeAggregate` over pinned-call
    // results, a parameter, a call result, or an extract of one of those.
    let mut module = nat_module();
    let holder = nat_struct(&mut module);
    insert_in_step(&mut module, Inst::Undef { ty: holder }, Some(v(100)));
    assert_invalid_use("Undef of a handle-bearing struct", &module);
}

#[test]
fn no_comparison_or_reference_count_operation_accepts_a_handle() {
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: nat(),
            lhs: X,
            rhs: X,
        },
        Some(v(100)),
    );
    assert_invalid_use("ICmp", &module);

    for (label, inst, result) in [
        ("Retain", Inst::Retain { ptr: X }, None),
        ("Release", Inst::Release { ptr: X }, None),
        ("IsUnique", Inst::IsUnique { ptr: X }, Some(v(100))),
    ] {
        let mut module = nat_module();
        insert_in_step(&mut module, inst, result);
        assert_invalid_use(label, &module);
    }
}

#[test]
fn no_dialect_operation_produces_consumes_or_names_a_handle() {
    use trust_ir::dialect::{AttrValue, DialectInst};
    // Handle operand.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::DialectOp(Box::new(
            DialectInst::new("example", "consume").with_operand(X),
        )),
        None,
    );
    assert_invalid_use("DialectOp operand", &module);

    // Handle result.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::DialectOp(Box::new(
            DialectInst::new("example", "produce").with_result_ty(nat()),
        )),
        Some(v(100)),
    );
    assert_invalid_use("DialectOp result_ty", &module);

    // A `clean.obj.box`-shaped op: scalar in, handle out.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::DialectOp(Box::new(
            DialectInst::new("clean", "obj_box")
                .with_operand(ONE)
                .with_result_ty(nat()),
        )),
        Some(v(100)),
    );
    assert_invalid_use("clean.obj_box", &module);

    // Even a PINNED handle as a type attribute is a handle reach.
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::DialectOp(Box::new(
            DialectInst::new("example", "marker").with_attr("type", AttrValue::Ty(nat())),
        )),
        None,
    );
    assert_invalid_use("DialectOp AttrValue::Ty", &module);
}

#[test]
fn an_indirect_call_over_a_raw_pointer_cannot_return_a_handle_but_an_exact_fn_value_can() {
    let mut module = nat_module();
    let unop = function_mut(&mut module, "pred").ty;
    insert_in_step(&mut module, Inst::NullPtr, Some(v(100)));
    insert_in_step(
        &mut module,
        Inst::CallIndirect {
            callee: v(100),
            sig: unop,
            args: vec![X],
            calling_conv: CallingConv::C,
        },
        Some(v(101)),
    );
    assert_invalid_use("CallIndirect over Ptr", &module);

    // The permitted form: the callee IS the exact signature.
    let mut module = nat_module();
    let unop = function_mut(&mut module, "pred").ty;
    insert_in_step(
        &mut module,
        Inst::Const {
            ty: Ty::Func(unop),
            value: Constant::FnDef(PRED),
        },
        Some(v(100)),
    );
    insert_in_step(
        &mut module,
        Inst::CallIndirect {
            callee: v(100),
            sig: unop,
            args: vec![X],
            calling_conv: CallingConv::C,
        },
        Some(v(101)),
    );
    assert_eq!(validate_module(&module), vec![]);
}

#[test]
fn a_handle_cannot_enter_a_variadic_slot() {
    let mut module = nat_module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let mut printf_like = Function::new(EXTRA, "printf_like", sig, b(0));
    printf_like.calling_conv = CallingConv::C;
    module
        .try_add_function(printf_like)
        .expect("Module::try_add_function: test fixture");
    insert_in_step(
        &mut module,
        Inst::Call {
            callee: EXTRA,
            args: vec![X],
        },
        None,
    );
    let errors = validate_module(&module);
    assert!(
        has(
            &errors,
            |e| matches!(e, ValidationError::InvalidHandleUse { detail, .. } if detail.contains("variadic"))
        ),
        "{errors:?}"
    );
}

#[test]
fn control_flow_cannot_scrutinize_a_handle() {
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Switch {
            value: X,
            default: b(1),
            default_args: vec![],
            cases: vec![],
            exhaustive_enum_unreachable: false,
        },
        None,
    );
    assert_invalid_use("Switch", &module);

    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::CondBr {
            cond: X,
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        },
        None,
    );
    assert_invalid_use("CondBr", &module);
}

#[test]
fn a_copy_must_keep_the_exact_handle_type() {
    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Copy {
            ty: Ty::Ptr,
            operand: X,
        },
        Some(v(100)),
    );
    assert_invalid_use("Copy to Ptr", &module);

    let mut module = nat_module();
    insert_in_step(
        &mut module,
        Inst::Copy {
            ty: nat(),
            operand: X,
        },
        Some(v(100)),
    );
    assert_eq!(validate_module(&module), vec![]);
}

// ──────────────── cross-runtime exchange (two-row registry) ────────────────

fn two_row_registry() -> HandleRegistry {
    HandleRegistry::from_pins(&[nat_pin().clone(), ROW_B]).unwrap()
}

/// The Nat module plus row B's declarations.
fn two_runtime_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("two_runtimes", target());
    let nat_decls = mb.declare_handle_runtime(nat_pin()).unwrap();
    let foo_decls = mb.declare_handle_runtime(&ROW_B).unwrap();
    assert_ne!(nat_decls.handle, foo_decls.handle);
    let unop = mb.add_func_type(vec![nat()], vec![nat()]);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The whole Nat row (the release entry point and the WS3.2 kernel
    // surface included) and row B's two precede `pred`.
    assert_eq!(module.functions.len(), NAT_ENTRY_COUNT as usize + 2);
    module
        .try_add_function(pred_function(
            FuncId::new(NAT_ENTRY_COUNT + 2),
            unop,
            nat_decls.entry("is_zero").unwrap(),
            nat_decls.entry("from_u64").unwrap(),
            nat_decls.entry("sub").unwrap(),
        ))
        .expect("Module::try_add_function: test fixture");
    module
}

fn foo() -> Ty {
    ROW_B.handle_ty()
}

#[test]
fn two_runtimes_cannot_exchange_handles() {
    let registry = two_row_registry();
    let module = two_runtime_module();
    assert_eq!(
        validate_module_with_handle_registry(&module, &registry),
        vec![]
    );
    // Under the production registry row B is untrusted.
    assert!(has(
        &validate_module(&module),
        |e| matches!(e, ValidationError::UntrustedHandleRuntime { runtime, .. } if runtime == "other::Foo")
    ));

    // A Nat into row B's consumer.
    let mut module = two_runtime_module();
    let foo_use = module
        .functions
        .iter()
        .find(|f| f.name == "other_foo_use")
        .unwrap()
        .id;
    insert_in_step(
        &mut module,
        Inst::Call {
            callee: foo_use,
            args: vec![X],
        },
        Some(v(100)),
    );
    let errors = validate_module_with_handle_registry(&module, &registry);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::CallArgTypeMismatch { .. }
        )),
        "{errors:?}"
    );

    // Returning a Nat from a Foo signature.
    let mut module = two_runtime_module();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![nat()],
            returns: vec![foo()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut cross = Function::new(FuncId::new(NAT_ENTRY_COUNT + 10), "cross", sig, b(0));
    let mut entry = Block::new(b(0)).with_param(v(0), nat());
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    cross.blocks.push(entry);
    module
        .try_add_function(cross)
        .expect("Module::try_add_function: test fixture");
    let errors = validate_module_with_handle_registry(&module, &registry);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::ReturnTypeMismatch { .. }
        )),
        "{errors:?}"
    );
}

#[test]
fn a_branch_edge_cannot_retype_a_handle_as_a_pointer() {
    let registry = two_row_registry();
    let mut module = two_runtime_module();
    let pred = pred_mut(&mut module);
    // bb1 now jumps to a Ptr-typed block parameter with the handle.
    pred.blocks[1].body[0] = InstrNode::new(Inst::Br {
        target: b(3),
        args: vec![X],
    });
    let mut sink = Block::new(b(3)).with_param(v(100), Ty::Ptr);
    sink.body
        .push(InstrNode::new(Inst::Return { values: vec![X] }));
    pred.blocks.push(sink);
    let errors = validate_module_with_handle_registry(&module, &registry);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::BranchArgTypeMismatch { .. }
        )),
        "{errors:?}"
    );
}

/// How `forge` hands its value back to `user`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ForgeExit {
    Return,
    CoroSuspend,
}

/// ```text
/// fn forge(frame: Ptr, p: V) -> Nat { <exit> p }
/// fn user(frame: Ptr, p: V) -> bool { trust_bignum_nat_is_zero(forge(frame, p)) }
/// ```
///
/// with `<exit>` either `ret p` or `coro_suspend frame[0] := 1, yield p`.
fn forge_module(value_ty: Ty, exit: ForgeExit) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("nat_coro_forge", target());
    let decls = mb.declare_handle_runtime(nat_pin()).unwrap();
    let forge_sig = mb.add_func_type(vec![Ty::Ptr, value_ty.clone()], vec![nat()]);
    let user_sig = mb.add_func_type(vec![Ty::Ptr, value_ty.clone()], vec![Ty::Bool]);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The first ids after the pinned declarations (however many the row pins).
    let next = module
        .functions
        .iter()
        .map(|f| f.id.index() + 1)
        .max()
        .unwrap_or(0);
    let forge_id = FuncId::new(next);
    let user_id = FuncId::new(next + 1);

    let mut forge = Function::new(forge_id, "forge", forge_sig, b(0));
    forge.body_gate = Some(BodyGate::Gated {
        authority: "handle-types-test".into(),
        evidence: None,
    });
    let mut entry = Block::new(b(0))
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), value_ty.clone());
    entry.body.push(InstrNode::new(match exit {
        ForgeExit::Return => Inst::Return { values: vec![v(1)] },
        ForgeExit::CoroSuspend => Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(1),
        },
    }));
    forge.blocks.push(entry);
    module
        .try_add_function(forge)
        .expect("Module::try_add_function: test fixture");

    let mut user = Function::new(user_id, "user", user_sig, b(0));
    user.body_gate = Some(BodyGate::Gated {
        authority: "handle-types-test".into(),
        evidence: None,
    });
    let mut entry = Block::new(b(0))
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), value_ty);
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: forge_id,
            args: vec![v(0), v(1)],
        })
        .with_result(v(2)),
    );
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: decls.entry("is_zero").unwrap(),
            args: vec![v(2)],
        })
        .with_result(v(3)),
    );
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
    user.blocks.push(entry);
    module
        .try_add_function(user)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Port of the 2026-09-17 proof-program ratchet
/// `b5.gap.UNEXPECTED.coro_suspend_value_not_checked_against_return_type_forges_a_nat`
/// (audit row c03). A `CoroSuspend` "returns `value` to the resumer" — by
/// definition it macro-expands to `GEP` + `Store` + `Return(value)` — but the
/// return-type rule matched `Inst::Return` alone, and the transport rule
/// (v43 rule 7) never saw the node because nothing ON it was handle-typed when
/// `value` was a `Ptr`. So `forge` above validated, for codegen too, and the
/// pinned runtime received an arbitrary pointer typed as a `Nat`: a forged
/// handle, contradicting the origin invariant. The ratchet asserted the hole
/// was open; this asserts it is closed by the NAMED return rule the suspend
/// now shares with `Return` (WS2.1, F-028), and that both controls still hold.
#[test]
fn a_coroutine_suspend_cannot_yield_a_pointer_or_integer_as_a_handle() {
    let is_forgery = |errors: &[ValidationError], actual: &str| {
        has(errors, |e| {
            matches!(
                e,
                ValidationError::ReturnTypeMismatch { block: 0, expected, actual: got }
                    if *expected == nat().to_string() && got == actual
            )
        })
    };

    // Control 1: the same laundering spelled as a `Return` is refused by the
    // same rule — `check_return_values` is shared, so the two exits agree.
    for (value_ty, actual) in [(Ty::Ptr, "ptr"), (Ty::U64, "u64")] {
        let via_return = validate_module(&forge_module(value_ty, ForgeExit::Return));
        assert_eq!(via_return.len(), 1, "{actual}: {via_return:?}");
        assert!(
            matches!(
                &via_return[0],
                ValidationError::ReturnTypeMismatch { block: 0, expected, actual: got }
                    if *expected == nat().to_string() && got == actual
            ),
            "{actual}: {via_return:?}"
        );
    }

    // Control 2: an HONEST yield of a real `Nat` is still refused by the
    // transport rule — `CoroSuspend` is not in the v43 transport set (DG-36,
    // option (a)) — and the return rule has nothing to add, because the
    // types agree.
    let honest = validate_module(&forge_module(nat(), ForgeExit::CoroSuspend));
    assert!(
        has(&honest, |e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. }
                if detail.contains("`CoroSuspend` cannot produce, consume or reinterpret an opaque runtime handle")
        )),
        "{honest:?}"
    );
    assert!(
        !has(&honest, |e| matches!(
            e,
            ValidationError::ReturnTypeMismatch { .. }
                | ValidationError::ReturnArityMismatch { .. }
        )),
        "{honest:?}"
    );

    // The forgeries: a `Ptr` and a `U64` yielded into `-> Nat`. Each is ONE
    // defect, named, at every entry point the ratchet measured clean.
    for (value_ty, actual) in [(Ty::Ptr, "ptr"), (Ty::U64, "u64")] {
        let forged = forge_module(value_ty, ForgeExit::CoroSuspend);
        let errors = validate_module(&forged);
        assert!(is_forgery(&errors, actual), "{actual}: {errors:?}");
        assert_eq!(errors.len(), 1, "{actual}: {errors:?}");
        let codegen = validate_module_for_codegen(&forged);
        assert!(is_forgery(&codegen, actual), "{actual}: {codegen:?}");
        let registry = HandleRegistry::from_pins(TRUSTED_HANDLE_RUNTIMES).unwrap();
        let pinned = validate_module_with_handle_registry(&forged, &registry);
        assert!(is_forgery(&pinned, actual), "{actual}: {pinned:?}");
    }
}

/// Two routes around the return rule the first port does not exercise, found
/// in review:
///
/// * EDGE LAUNDERING — the pointer reaches the suspend through a block
///   parameter of a later block (`br bb1(%p)`, `bb1(%q: Ptr): coro_suspend
///   .., %q`), so the yielded value is not an entry parameter and its type
///   comes from the successor's own parameter list;
/// * a HANDLE AS THE FRAME — the honest `Nat` is used as the coroutine frame
///   (the suspend's macro-expanded `GEP` + `Store` would write through a
///   handle). A handle is one pointer word but NOT pointer-like, so the
///   frame rule must refuse it, independently of the transport rule;
///
/// and the remaining library entry points the proof program measured clean on
/// the original forgery (`validate_changed`, `validate_module_with_authority`).
#[test]
fn a_coroutine_suspend_cannot_launder_a_handle_through_an_edge_or_the_frame() {
    // Edge laundering: entry `br bb1(%1)`; `bb1(%2: Ptr): coro_suspend %0, 0, 1, %2`.
    let mut laundered = forge_module(Ty::Ptr, ForgeExit::CoroSuspend);
    let forge_id = {
        let forge = laundered
            .functions
            .iter_mut()
            .find(|f| f.name == "forge")
            .expect("forge");
        forge.blocks[0].body = vec![InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        })];
        let mut tail = Block::new(b(1)).with_param(v(2), Ty::Ptr);
        tail.body.push(InstrNode::new(Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(2),
        }));
        forge.blocks.push(tail);
        forge.id
    };
    let is_forgery = |errors: &[ValidationError]| {
        has(errors, |e| {
            matches!(
                e,
                ValidationError::ReturnTypeMismatch { block: 1, expected, actual }
                    if *expected == nat().to_string() && actual == "ptr"
            )
        })
    };
    let errors = validate_module(&laundered);
    assert!(is_forgery(&errors), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
    let changed = validate_changed(&laundered, &[forge_id]);
    assert!(is_forgery(&changed), "{changed:?}");
    let authority =
        validate_module_with_authority(&laundered, &trust_ir::proof::RejectingModuleProofAuthority);
    assert!(is_forgery(&authority), "{authority:?}");

    // A handle as the frame: `coro_suspend %h, 0, 1, %h` in `-> Nat`, where
    // `%h` is an honest `Nat`. The yield TYPE agrees; the frame does not
    // address memory.
    let mut framed = forge_module(nat(), ForgeExit::CoroSuspend);
    {
        let forge = framed
            .functions
            .iter_mut()
            .find(|f| f.name == "forge")
            .expect("forge");
        let Inst::CoroSuspend { frame, .. } = &mut forge.blocks[0].body[0].inst else {
            panic!("forge must end in a suspend");
        };
        *frame = v(1);
    }
    let errors = validate_module(&framed);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::OperandNotPointer { block: 0, op, ty }
                if op == "coro_suspend" && *ty == nat().to_string()
        )),
        "{errors:?}"
    );
    assert!(
        !has(&errors, |e| matches!(
            e,
            ValidationError::ReturnTypeMismatch { .. }
        )),
        "{errors:?}"
    );
}

// ───────────────────────────── the pins ─────────────────────────────

#[test]
fn the_trusted_runtime_table_is_well_formed_and_ratified() {
    let registry = HandleRegistry::from_pins(TRUSTED_HANDLE_RUNTIMES).unwrap();
    let mut symbols = std::collections::BTreeSet::new();
    for pin in registry.pins() {
        assert_eq!(pin.handle_identity().validate(), Ok(()));
        for entry in pin.entry_points {
            assert!(symbols.insert(entry.symbol), "{}", entry.symbol);
            let signature = pin.func_ty(entry);
            assert!(
                signature
                    .params
                    .iter()
                    .chain(&signature.returns)
                    .any(Ty::is_handle)
            );
            assert!(!signature.is_vararg);
            assert!(!entry.symbol.starts_with('_'));
            assert_eq!(
                registry
                    .entry_for_symbol(entry.symbol)
                    .map(|(p, e)| (p.runtime, e.role)),
                Some((pin.runtime, entry.role))
            );
        }
    }
    let nat = registry
        .pin_for(&HandleTy::new("Nat", "trust_bignum::Nat"))
        .unwrap();
    // The v1 five, then the Clean kernel's native `Nat` surface (WS3.2, the
    // kernel's closed `NAT_BINOPS` allowlist plus the two-pin projection and
    // `clone`), in table order.
    assert_eq!(
        nat.entry_points
            .iter()
            .map(|e| e.symbol)
            .collect::<Vec<_>>(),
        [
            "trust_bignum_nat_from_u64",
            "trust_bignum_nat_add",
            "trust_bignum_nat_sub",
            "trust_bignum_nat_is_zero",
            "trust_bignum_nat_drop",
            "trust_bignum_nat_mul",
            "trust_bignum_nat_div",
            "trust_bignum_nat_mod",
            "trust_bignum_nat_beq",
            "trust_bignum_nat_ble",
            "trust_bignum_nat_fits_u64",
            "trust_bignum_nat_to_u64",
            "trust_bignum_nat_clone",
            "trust_bignum_nat_land",
            "trust_bignum_nat_lor",
            "trust_bignum_nat_xor",
            "trust_bignum_nat_shift_left",
            "trust_bignum_nat_shift_right",
            "trust_bignum_nat_pow",
        ]
    );
    // `mod` is the one role whose Rust method has a different name: the role
    // is the Lean name, the `def_path` the item the shim wraps.
    let def_path = |role: &str| {
        nat.entry_points
            .iter()
            .find(|e| e.role == role)
            .map(|e| e.def_path)
    };
    assert_eq!(def_path("mod"), Some("trust_bignum::Nat::rem"));
    assert_eq!(def_path("beq"), Some("trust_bignum::Nat::beq"));
    assert_eq!(def_path("to_u64"), Some("trust_bignum::Nat::to_u64"));
    // The projection is two pins; neither a wrapping projection nor a
    // tri-state compare is a role.
    for absent in ["to_u64_wrapping", "cmp", "eq", "lt"] {
        assert_eq!(def_path(absent), None, "{absent}");
    }
    // The release entry point's ratified shape: it is the ONLY pinned entry
    // that consumes a handle without producing one, and its return list is
    // EMPTY (a `Unit` return would be a one-element list, a different `FuncTy`,
    // and would refuse the real `extern "C" fn(*mut Nat)` shim).
    let release = nat
        .entry_points
        .iter()
        .find(|entry| entry.role == "drop")
        .expect("the release entry point is pinned");
    assert_eq!(release.symbol, "trust_bignum_nat_drop");
    assert_eq!(release.def_path, "trust_bignum::Nat::drop");
    let signature = nat.func_ty(release);
    assert_eq!(signature.params, vec![nat.handle_ty()]);
    assert!(signature.returns.is_empty());
    assert!(!signature.is_vararg);
    // Exactly one consuming-only entry, and singular by CONSTRUCTION rather
    // than by convention: `HandleRegistry::from_pins` refuses a row with a
    // second consuming entry point (`HandlePinError::MultipleReleaseEntries`,
    // pinned by `validate::handle_registry_tests::from_pins_refuses_malformed_rows`),
    // so a future pin-row author cannot quietly add a second way out. §7's
    // "the pinned release symbol is the ONLY way out" and TRUST.md item 9's
    // single trusted at-most-once row both depend on it.
    assert_eq!(
        nat.entry_points
            .iter()
            .filter(|entry| !entry.returns.contains(&PinnedTy::Handle))
            .filter(|entry| entry.params.contains(&PinnedTy::Handle))
            .filter(|entry| nat.func_ty(entry).returns.is_empty())
            .count(),
        1
    );
    assert!(
        registry
            .pin_for(&HandleTy::new("Nat", "other::Nat"))
            .is_none()
    );
    assert!(registry.entry_for_symbol("_trust_bignum_nat_add").is_none());
}

// ─────────────────── THE RELEASE ENTRY POINT (`drop`) ───────────────────
//
// `TRUSTED_HANDLE_RUNTIMES` pins `trust_bignum_nat_drop: (H) -> ()` — the one
// pinned entry that CONSUMES a handle without producing one. Before it, §7's
// "deliberately not ratified" clause said v1 handles are never released, so
// recursion-shaped `Nat` code was correct-by-LEAK.
//
// No new validator rule was needed for the admission half, and these tests are
// what establishes that rather than assuming it: a call to the pinned release
// symbol is admitted by the SAME exact-typed transport rule as `add`, because
// that rule keys on the declaration being pinned and not on which direction
// the handle flows. What DID need pinning is the other half — that widening
// the pin table by a consuming entry point did not open the ARC/heap surface
// (see `no_comparison_or_reference_count_operation_accepts_a_handle` and
// `no_memory_operation_touches_a_handle`), and that an unpinned
// release-shaped symbol is still refused.

/// `nat_module()` plus `drop(x)` in the step block, i.e. the release the pin
/// now makes expressible.
fn releasing_module() -> Module {
    let mut module = nat_module();
    let release = module
        .functions
        .iter()
        .find(|function| function.name == "trust_bignum_nat_drop")
        .expect("the pinned release declaration is in the module")
        .id;
    insert_in_step(
        &mut module,
        Inst::Call {
            callee: release,
            args: vec![X],
        },
        None,
    );
    module
}

#[test]
fn the_pinned_release_entry_point_is_declarable_and_callable() {
    // The declaration half: `nat_module()` declares the whole pinned row, so
    // the positive module already carries `trust_bignum_nat_drop` and
    // validates — which is the statement that the fifth pin row is a legal
    // declaration and not a signature mismatch.
    let module = nat_module();
    assert!(
        module
            .functions
            .iter()
            .any(|function| function.name == "trust_bignum_nat_drop"),
        "the pinned row declares the release entry point"
    );
    assert_eq!(validate_module(&module), vec![]);

    // The call half: a handle flowing INTO the pinned release symbol and
    // nothing coming back out.
    let module = releasing_module();
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(validate_module_for_codegen(&module), vec![]);
}

#[test]
fn a_release_declaration_with_any_other_signature_is_refused() {
    // Each of these is the release symbol wearing a signature the pin does
    // not name. The pointer-typed one is the forgery that matters: it would
    // let the module hand the runtime an arbitrary word to free.
    for (label, params, returns) in [
        ("returns its handle", vec![nat()], vec![nat()]),
        ("pointer parameter", vec![Ty::Ptr], vec![]),
        ("no parameter", vec![], vec![]),
        ("unit return", vec![nat()], vec![Ty::Unit]),
    ] {
        let mut module = nat_module();
        let wrong = module
            .add_func_type(FuncTy {
                params,
                returns,
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        function_mut(&mut module, "trust_bignum_nat_drop").ty = wrong;
        assert!(
            signature_mismatch(&validate_module(&module), "trust_bignum_nat_drop"),
            "{label}: a release declaration off the pin must be refused"
        );
    }
}

#[test]
fn an_unpinned_release_shaped_declaration_is_still_refused() {
    // The release entry point is the ONLY way out, so a second `free`-shaped
    // symbol — the obvious way to smuggle one in — is refused as a foreign
    // declaration reaching a handle, exactly like any other unpinned callee.
    let mut module = nat_module();
    let ft = module
        .add_func_type(FuncTy {
            params: vec![nat()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(Function::declaration(
            EXTRA,
            "trust_bignum_nat_free",
            ft,
            Default::default(),
        ))
        .expect("Module::try_add_function: test fixture");
    assert!(foreign(&validate_module(&module), "trust_bignum_nat_free"));
}

// DOUBLE RELEASE AND USE-AFTER-RELEASE ARE NOT DETECTABLE HERE.
//
// These two tests PIN THE ABSENCE of a guarantee, so that nothing later reads
// the release entry point as ownership tracking. `validate_module` returns
// `[]` for both modules below, and that is correct rather than a hole: a
// handle is an opaque word with no IR provenance, and §7's ratified transport
// set admits `Copy` and `Select`, so handle values are deliberately
// NON-LINEAR — two SSA values may denote one runtime allocation. Deciding
// "released exactly once" would need a linear discipline over handle values
// (refusing `Copy`, treating block parameters as moves) plus a per-parameter
// "consumes" contract the format does not have, and even then a release
// inside a callee is invisible to an intraprocedural syntactic rule. The
// runtime owns this; `TRUST.md` item 9(c) discloses it.

#[test]
fn a_double_release_validates_and_that_is_the_documented_non_guarantee() {
    let mut module = releasing_module();
    let release = function_mut(&mut module, "trust_bignum_nat_drop").id;
    insert_in_step(
        &mut module,
        Inst::Call {
            callee: release,
            args: vec![X],
        },
        None,
    );
    assert_eq!(
        validate_module(&module),
        vec![],
        "trust-ir makes no liveness claim about a handle; a second release is          representable and unrefused, and the runtime owns it"
    );
}

#[test]
fn a_use_after_release_validates_and_that_is_the_documented_non_guarantee() {
    // `drop(x)` FIRST, then `sub(x, from_u64(1))` on the same handle. The
    // release goes at the head of the step block, not before the terminator,
    // so the later `sub` really is a use of a released handle.
    let mut module = nat_module();
    let release = function_mut(&mut module, "trust_bignum_nat_drop").id;
    pred_mut(&mut module).blocks[2].body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: release,
            args: vec![X],
        }),
    );
    let step = &module
        .functions
        .iter()
        .find(|function| function.name == "pred")
        .unwrap()
        .blocks[2];
    let released_at = step
        .body
        .iter()
        .position(|node| matches!(&node.inst, Inst::Call { args, .. } if args == &[X]))
        .expect("the release call is in the step block");
    let used_at = step
        .body
        .iter()
        .position(|node| matches!(&node.inst, Inst::Call { args, .. } if args == &[X, O]))
        .expect("`sub(X, O)` is in the step block");
    assert!(
        released_at < used_at,
        "the fixture must really use the handle after releasing it"
    );
    assert_eq!(
        validate_module(&module),
        vec![],
        "a use after release is a dataflow property over an opaque value; the          validator does not decide it"
    );
}

#[test]
fn a_producer_may_declare_the_roles_it_calls_and_no_others() {
    // The API the conformance fixture uses, and the reason adding the release
    // row left every golden byte-identical: a producer that never releases
    // declares four symbols, not five.
    let mut mb = ModuleBuilder::new_with_target_info("four", target());
    let decls = mb
        .declare_handle_runtime_roles(nat_pin(), &["from_u64", "add", "sub", "is_zero"])
        .unwrap();
    assert!(decls.entry("drop").is_none());
    assert_eq!(decls.entries().count(), 4);
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(module.functions.len(), 4);
    assert!(
        !module
            .functions
            .iter()
            .any(|function| function.name == "trust_bignum_nat_drop")
    );

    // Misspelling a role is named, not silently ignored.
    let mut mb = ModuleBuilder::new_with_target_info("typo", target());
    assert!(matches!(
        mb.declare_handle_runtime_roles(nat_pin(), &["dropp"]),
        Err(HandleDeclError::UnknownRole { role, .. }) if role == "dropp"
    ));
    // ...and nothing was declared by the failing call.
    assert_eq!(
        mb.build()
            .expect("ModuleBuilder::build: test fixture")
            .functions
            .len(),
        0
    );
}

// ─────────────── HandleEntryPointAddressTaken (SymbolAddr) ───────────────
//
// The pinned symbol namespace was guarded on `Function.name` / `Global.name`
// only. `Constant::SymbolAddr { symbol }` is a third spelling of a link-time
// symbol — admitted for `Ty::Ptr` and `Ty::Func(_)` — and a `CallIndirect`
// over one has no `FnDef` provenance, so its `sig` was trusted as declared.
// Measured before the fix: every module below returned `[]` from both
// `validate_module` and `validate_module_for_codegen`, and at link time the
// relocation resolves to the real runtime, which dereferences whatever word
// the module passed as a `Nat` handle.

fn address_taken(errors: &[ValidationError], symbol: &str) -> bool {
    has(
        errors,
        |e| matches!(e, ValidationError::HandleEntryPointAddressTaken { symbol: s, .. } if s == symbol),
    )
}

#[test]
fn a_call_indirect_over_a_symbol_address_of_a_pinned_entry_point_is_refused() {
    // `fn(Ptr) -> Bool`, the forged shape of `is_zero`.
    for callee_ty in [None, Some(Ty::Ptr)] {
        let mut module = nat_module();
        let forged = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let callee_ty = callee_ty.unwrap_or(Ty::Func(forged));
        insert_in_step(
            &mut module,
            Inst::Alloca {
                ty: Ty::U64,
                count: None,
                align: None,
            },
            Some(v(100)),
        );
        insert_in_step(
            &mut module,
            Inst::Const {
                ty: callee_ty,
                value: Constant::SymbolAddr {
                    symbol: "trust_bignum_nat_is_zero".into(),
                    addend: 0,
                },
            },
            Some(v(101)),
        );
        insert_in_step(
            &mut module,
            Inst::CallIndirect {
                callee: v(101),
                sig: forged,
                args: vec![v(100)],
                calling_conv: CallingConv::C,
            },
            Some(v(102)),
        );
        let errors = validate_module(&module);
        assert!(
            address_taken(&errors, "trust_bignum_nat_is_zero"),
            "{errors:?}"
        );
        assert!(address_taken(
            &validate_module_for_codegen(&module),
            "trust_bignum_nat_is_zero"
        ));
    }
}

#[test]
fn a_handle_free_module_cannot_drive_the_runtime_through_symbol_addresses() {
    // Never spells `Ty::Handle`, never declares a pinned symbol: `main` runs
    // from_u64 -> add(<handle>, <stack address>) -> is_zero entirely through
    // relocatable constants with pointer-typed signatures.
    let mut mb = ModuleBuilder::new_with_target_info("no_handles", target());
    let from_u64 = mb.add_func_type(vec![Ty::U64], vec![Ty::Ptr]);
    let add = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]);
    let is_zero = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("main", main_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let symbol = |symbol: &str| Constant::SymbolAddr {
        symbol: symbol.into(),
        addend: 0,
    };
    let seven = fb.iconst(Ty::U64, 7);
    let f = fb.const_value(Ty::Func(from_u64), symbol("trust_bignum_nat_from_u64"));
    let n = fb.call_indirect(f, from_u64, vec![seven]);
    let stack = fb.alloca(Ty::U64);
    let a = fb.const_value(Ty::Func(add), symbol("trust_bignum_nat_add"));
    let sum = fb.call_indirect(a, add, vec![n, stack]);
    let z = fb.const_value(Ty::Func(is_zero), symbol("trust_bignum_nat_is_zero"));
    let zero = fb.call_indirect(z, is_zero, vec![sum]);
    fb.ret(vec![zero]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = validate_module(&module);
    for symbol in [
        "trust_bignum_nat_from_u64",
        "trust_bignum_nat_add",
        "trust_bignum_nat_is_zero",
    ] {
        assert!(address_taken(&errors, symbol), "{symbol}: {errors:?}");
    }
    assert_eq!(
        errors
            .iter()
            .filter(|e| matches!(e, ValidationError::HandleEntryPointAddressTaken { .. }))
            .count(),
        3
    );
    assert!(address_taken(
        &validate_module_for_codegen(&module),
        "trust_bignum_nat_add"
    ));
    // The unpinned neighbour is not in the namespace and is untouched.
    let mut mb = ModuleBuilder::new_with_target_info("unrelated", target());
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::Bool]);
    let mut fb = mb.function("main", main_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let stack = fb.alloca(Ty::U64);
    let f = fb.const_value(Ty::Func(ft), symbol("some_other_runtime_is_zero"));
    let r = fb.call_indirect(f, ft, vec![stack]);
    fb.ret(vec![r]);
    fb.build();
    assert_eq!(
        validate_module(&mb.build().expect("ModuleBuilder::build: test fixture")),
        vec![]
    );
}

#[test]
fn a_symbol_address_of_a_pinned_entry_point_in_a_global_initializer_is_refused() {
    // Direct, and nested inside an aggregate initializer, where the enclosing
    // aggregate carries the type: a `Load` from either would mint a callee
    // with no provenance at all.
    let mut module = nat_module();
    let mut table = global("table", Ty::Ptr);
    table.initializer = Some(Constant::SymbolAddr {
        symbol: "trust_bignum_nat_add".into(),
        addend: 0,
    });
    module.globals.push(table);
    let errors = validate_module(&module);
    assert!(address_taken(&errors, "trust_bignum_nat_add"), "{errors:?}");
    assert!(has(&errors, |e| matches!(
        e,
        ValidationError::HandleEntryPointAddressTaken { location, .. } if location == "global 'table'"
    )));

    let mut module = nat_module();
    let mut table = global("vtable", Ty::Tuple(vec![Ty::U64, Ty::Ptr]));
    table.initializer = Some(Constant::Aggregate(vec![
        Constant::Int(0),
        Constant::SymbolAddr {
            symbol: "trust_bignum_nat_sub".into(),
            addend: 8,
        },
    ]));
    module.globals.push(table);
    let errors = validate_module(&module);
    assert!(address_taken(&errors, "trust_bignum_nat_sub"), "{errors:?}");
}

// ─────────────── Invoke normal edge (BranchArgTypeMismatch) ───────────────

/// `fn forge(p: Ptr) -> Nat` that retypes its parameter through an `Invoke`
/// normal edge: `bb0(%0: Ptr): invoke noop() to bb1(%0) unwind bb2`,
/// `bb1(%1: Nat): return %1`. The identical retyping through `Br bb1(%0)` is
/// refused with `BranchArgTypeMismatch`; the `Invoke` edge was never
/// arity- or type-checked, and the v43 transport rule admits `Invoke` on the
/// premise that edge types are checked elsewhere.
fn forge_through(module: &mut Module, terminator: Inst) {
    let void = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let noop = NOOP;
    let mut noop_fn = Function::new(noop, "noop", void, b(0));
    let mut entry = Block::new(b(0));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    noop_fn.blocks = vec![entry];
    module
        .try_add_function(noop_fn)
        .expect("Module::try_add_function: test fixture");

    let forge_sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut forge = Function::new(FORGE, "forge", forge_sig, b(0));
    let mut bb0 = Block::new(b(0)).with_param(v(0), Ty::Ptr);
    bb0.body.push(InstrNode::new(terminator));
    let mut bb1 = Block::new(b(1)).with_param(v(1), nat());
    bb1.body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    let mut bb2 = Block::new(b(2));
    bb2.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results([v(2), v(3)]),
    );
    bb2.body.push(InstrNode::new(Inst::Resume { exn: v(2) }));
    forge.blocks = vec![bb0, bb1, bb2];
    module
        .try_add_function(forge)
        .expect("Module::try_add_function: test fixture");
}

#[test]
fn an_invoke_normal_edge_cannot_retype_a_ptr_into_a_handle() {
    let retyped = |errors: &[ValidationError]| {
        has(errors, |e| {
            matches!(
                e,
                ValidationError::BranchArgTypeMismatch { block: 0, target: 1, arg_index: 0, expected, actual }
                    if expected == &nat().to_string() && actual == "ptr"
            )
        })
    };
    // Control: the branch edge.
    let mut module = nat_module();
    forge_through(
        &mut module,
        Inst::Br {
            target: b(1),
            args: vec![v(0)],
        },
    );
    let errors = validate_module(&module);
    assert!(retyped(&errors), "{errors:?}");

    // The invoke edge.
    let mut module = nat_module();
    forge_through(
        &mut module,
        Inst::Invoke {
            callee: NOOP,
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![v(0)],
            unwind_dest: b(2),
        },
    );
    let errors = validate_module(&module);
    assert!(retyped(&errors), "{errors:?}");
    assert!(retyped(&validate_module_for_codegen(&module)));

    // Arity on the same edge: no argument for the one parameter.
    let mut module = nat_module();
    forge_through(
        &mut module,
        Inst::Invoke {
            callee: NOOP,
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
    );
    let errors = validate_module(&module);
    assert!(
        has(&errors, |e| matches!(
            e,
            ValidationError::BranchArgCountMismatch {
                block: 0,
                target: 1,
                expected: 1,
                actual: 0
            }
        )),
        "{errors:?}"
    );
}

/// WS2.1 (F-028): the suspend exit of `forge_through`'s `forge(%0: Ptr) -> Nat`.
/// `coro_suspend %0, 0, 1, %0` hands the `Ptr` back to the resumer as the
/// function's `Nat` result — the `Return(value)` half of the suspend's
/// macro-expansion retyping a pointer into a handle, with no handle-typed
/// operand on the node for the transport rule to see. Refused by the SAME
/// named reason as the `Return` spelling, because both call
/// `check_return_values`.
#[test]
fn a_coro_suspend_yield_cannot_retype_a_ptr_into_a_handle() {
    let retyped = |errors: &[ValidationError]| {
        has(errors, |e| {
            matches!(
                e,
                ValidationError::ReturnTypeMismatch { block: 0, expected, actual }
                    if expected == &nat().to_string() && actual == "ptr"
            )
        })
    };
    let mut module = nat_module();
    forge_through(
        &mut module,
        Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(0),
        },
    );
    let errors = validate_module(&module);
    assert!(retyped(&errors), "{errors:?}");
    assert!(retyped(&validate_module_for_codegen(&module)));

    // Control: the `Return` spelling of the same exit reports the IDENTICAL
    // findings (including `forge_through`'s fixture-shape ones, e.g. the
    // unreachable continuation blocks), so the suspend spelling adds nothing
    // beyond the shared return rule — and nothing less.
    let mut via_return = nat_module();
    forge_through(&mut via_return, Inst::Return { values: vec![v(0)] });
    assert_eq!(validate_module(&via_return), errors);
}

/// WS2.1 positive: a well-typed coroutine suspend — a `-> u64` function
/// yielding a `u64` through a `Ptr` frame — validates, at the module, codegen
/// and function entry points. The return rule and the frame rule refuse only
/// what is mistyped.
#[test]
fn a_u64_coroutine_yielding_a_u64_through_a_ptr_frame_validates() {
    let mut module = Module::new("coro_ok");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "gen", sig, b(0));
    func.body_gate = Some(BodyGate::Gated {
        authority: "handle-types-test".into(),
        evidence: None,
    });
    let mut entry = Block::new(b(0))
        .with_param(v(0), Ty::Ptr)
        .with_param(v(1), Ty::U64);
    entry.body.push(InstrNode::new(Inst::CoroSuspend {
        frame: v(0),
        state_slot: 0,
        next_state: 1,
        value: v(1),
    }));
    func.blocks.push(entry);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    assert_eq!(
        trust_ir_build::validate_function(&module.functions[0]),
        Vec::new()
    );
}

// ─────────────── WS3.1: REGISTRY-PARAMETERIZED COMPOSED LANES ───────────────
//
// `ValidationConfig` threads ONE handle registry through the single-module,
// codegen, authority and linked lanes. Before it, only
// `validate_module_with_handle_registry` took a registry, so a pin-table row
// staged ahead of `TRUSTED_HANDLE_RUNTIMES` (F-052) had no codegen, authority
// or linked lane at all (F-009, registry half; proof-program rows
// `b5.gap.no_codegen_or_authority_entry_point_takes_a_handle_registry` and
// `b5.uf03`).
mod registry_config {
    use super::*;
    use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
    use trust_ir::dialect::DialectInst;
    use trust_ir::dialect::schema::{DialectSchema, DialectSchemaRegistry, OperationSchema};
    use trust_ir::proof::{
        ObligationKind, ProofCertificate, ProofFormula, ProofObligation, ProofStatus,
        RejectingModuleProofAuthority,
    };
    use trust_ir::{ExternRef, FunctionSummary, ModuleImport, Producer, ProofId};
    use trust_ir_build::{
        LinkedValidationReport, ModuleSet, ValidationConfig, validate_linked_module,
        validate_linked_module_with_config, validate_module_report,
        validate_module_report_with_authority, validate_module_with_config,
    };

    /// A STAGED role: one the pinned table does not carry. It was `mul`
    /// until WS3.2 pinned the Clean kernel's native `Nat` surface; Lean's
    /// `Nat.gcd` is outside that surface, so it stays unpinned.
    const GCD: HandleEntryPoint = HandleEntryPoint {
        role: "gcd",
        symbol: "trust_bignum_nat_gcd",
        def_path: "trust_bignum::Nat::gcd",
        params: &[PinnedTy::Handle, PinnedTy::Handle],
        returns: &[PinnedTy::Handle],
    };

    /// A ONE-row registry: the pinned Nat row with `entries` substituted.
    fn nat_row_with(entries: Vec<HandleEntryPoint>) -> HandleRegistry {
        let row = HandleRuntimePin {
            entry_points: Box::leak(entries.into_boxed_slice()),
            ..nat_pin().clone()
        };
        HandleRegistry::from_pins(&[row]).expect("well-formed one-row registry")
    }

    /// The pinned Nat row plus the staged `gcd` role.
    fn with_gcd() -> HandleRegistry {
        let mut entries = nat_pin().entry_points.to_vec();
        entries.push(GCD);
        nat_row_with(entries)
    }

    /// The pinned Nat row with `add` re-typed to `(Nat, Nat) -> U64`.
    fn add_returns_u64() -> HandleRegistry {
        let entries = nat_pin()
            .entry_points
            .iter()
            .map(|entry| {
                if entry.role == "add" {
                    HandleEntryPoint {
                        returns: &[PinnedTy::Scalar(Ty::U64)],
                        ..entry.clone()
                    }
                } else {
                    entry.clone()
                }
            })
            .collect();
        nat_row_with(entries)
    }

    /// A licensed body `self_gcd(x) = gcd(x, x)` over the extended row's
    /// declarations (the whole pinned row plus `gcd`).
    fn gcd_module(registry: &HandleRegistry) -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("nat_self_gcd", target());
        let decls = mb.declare_handle_runtime(&registry.pins()[0]).unwrap();
        let unop = mb.add_func_type(vec![nat()], vec![nat()]);
        let mut fb = mb.function("self_gcd", unop);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, nat());
        fb.switch_to_block(entry);
        let g = fb.call(decls.entry("gcd").unwrap(), vec![x, x]);
        fb.ret(vec![g]);
        fb.set_body_gate(BodyGate::Gated {
            authority: "handle-types-test".into(),
            evidence: None,
        });
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    fn only_foreign_gcd(errors: &[ValidationError]) -> bool {
        matches!(
            errors,
            [ValidationError::HandleForeignDeclaration { name, .. }]
                if name == "trust_bignum_nat_gcd"
        )
    }

    fn add_mismatch(errors: &[ValidationError]) -> bool {
        has(errors, |e| {
            matches!(
                e,
                ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                    if symbol == "trust_bignum_nat_add"
            )
        })
    }

    fn linked<'a>(module: &'a Module, config: &ValidationConfig<'_>) -> LinkedValidationReport<'a> {
        validate_linked_module_with_config(module, &ModuleSet::new([]), config)
    }

    /// Positive: a module declaring and calling `trust_bignum_nat_gcd`
    /// validates through the linked + codegen lane under a one-row registry
    /// that pins it, and the report says the registry was NOT the pinned one.
    #[test]
    fn a_staged_row_validates_through_the_linked_codegen_lane_under_its_registry() {
        let extended = with_gcd();
        let module = gcd_module(&extended);
        let config = ValidationConfig::pinned()
            .with_handle_registry(&extended)
            .with_codegen(true);
        assert!(!config.handle_registry_is_pinned());

        let report = linked(&module, &config);
        assert!(report.is_ok(), "{:?}", report.errors());
        assert!(!report.handle_registry_is_pinned());

        let report = validate_module_with_config(&module, &config);
        assert!(report.is_ok(), "{:?}", report.errors());
        assert!(!report.handle_registry_is_pinned());
    }

    /// Negative twin: the SAME module under `ValidationConfig::pinned()` is
    /// exactly one `HandleForeignDeclaration`, on every lane, and only the twin
    /// reports `handle_registry_is_pinned`.
    #[test]
    fn the_same_module_under_the_pinned_config_is_exactly_one_foreign_declaration() {
        let module = gcd_module(&with_gcd());
        let pinned = ValidationConfig::pinned();
        assert!(pinned.handle_registry_is_pinned());

        let report = validate_module_with_config(&module, &pinned);
        assert!(only_foreign_gcd(report.errors()), "{:?}", report.errors());
        assert!(report.handle_registry_is_pinned());

        let codegen = pinned.with_codegen(true);
        let report = validate_module_with_config(&module, &codegen);
        assert!(only_foreign_gcd(report.errors()), "{:?}", report.errors());
        assert!(report.handle_registry_is_pinned());
        assert!(only_foreign_gcd(&validate_module_for_codegen(&module)));

        let report = linked(&module, &codegen);
        assert!(only_foreign_gcd(report.errors()), "{:?}", report.errors());
        assert!(report.handle_registry_is_pinned());
        let report =
            validate_linked_module(&module, &ModuleSet::new([]), &RejectingModuleProofAuthority);
        assert!(only_foreign_gcd(report.errors()), "{:?}", report.errors());
        assert!(report.handle_registry_is_pinned());

        // A registry built from EXACTLY the pinned rows is the pinned table;
        // the extended one never is.
        let rebuilt = HandleRegistry::from_pins(TRUSTED_HANDLE_RUNTIMES).unwrap();
        assert!(
            ValidationConfig::pinned()
                .with_handle_registry(&rebuilt)
                .handle_registry_is_pinned()
        );
        assert!(validate_module_report(&module).handle_registry_is_pinned());
    }

    /// Mutation control: the registry is THREADED, not ignored. With the Nat
    /// row's `add` re-typed to `(Nat, Nat) -> U64`, the module that validates
    /// clean under the pinned table fails with
    /// `HandleEntryPointSignatureMismatch` on the codegen, authority and
    /// linked lanes — none of which could take a registry before WS3.1.
    #[test]
    fn a_mutated_registry_reaches_the_codegen_authority_and_linked_lanes() {
        let module = nat_module();
        let pinned_codegen = ValidationConfig::pinned().with_codegen(true);
        assert!(validate_module_with_config(&module, &pinned_codegen).is_ok());
        assert!(linked(&module, &pinned_codegen).is_ok());

        let mutated = add_returns_u64();
        let codegen = pinned_codegen.with_handle_registry(&mutated);
        let errors = validate_module_with_config(&module, &codegen).into_errors();
        assert!(add_mismatch(&errors), "{errors:?}");
        let report = linked(&module, &codegen);
        assert!(add_mismatch(report.errors()), "{:?}", report.errors());
        assert!(!report.handle_registry_is_pinned());
        let authority = ValidationConfig::pinned()
            .with_authority(&RejectingModuleProofAuthority)
            .with_handle_registry(&mutated);
        let errors = validate_module_with_config(&module, &authority).into_errors();
        assert!(add_mismatch(&errors), "{errors:?}");
    }

    /// The proof-program GAP row, flipped: the codegen and authority lanes
    /// (and the linked lane) now take a handle registry. PASS asserts the
    /// staged `gcd` row is admitted by each lane under the registry that pins
    /// it, with the right-reason twin: the hard-wired entry points still
    /// refuse it as exactly one foreign declaration.
    #[test]
    fn b5_gap_no_codegen_or_authority_entry_point_takes_a_handle_registry() {
        let extended = with_gcd();
        let module = gcd_module(&extended);
        let base = ValidationConfig::pinned().with_handle_registry(&extended);

        let codegen = validate_module_with_config(&module, &base.with_codegen(true));
        assert!(codegen.is_ok(), "{:?}", codegen.errors());
        let authority = validate_module_with_config(
            &module,
            &base.with_authority(&RejectingModuleProofAuthority),
        );
        assert!(authority.is_ok(), "{:?}", authority.errors());
        let linked_report = linked(&module, &base);
        assert!(linked_report.is_ok(), "{:?}", linked_report.errors());

        // Right-reason twin: the pinned wrappers are unchanged.
        assert!(only_foreign_gcd(&validate_module_for_codegen(&module)));
        assert!(only_foreign_gcd(
            validate_module_report_with_authority(&module, &RejectingModuleProofAuthority).errors()
        ));
    }

    // ── second mutation: no verdict leaks between walks ──

    fn clause() -> ProofFormula {
        ProofFormula::smtlib2("(= 1 1)", "Bool")
    }

    fn contract() -> FunctionSummary {
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause())
    }

    fn certified_postcondition(function: FuncId) -> (ProofObligation, ProofCertificate) {
        let obligation = ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures (= 1 1)",
        )
        .with_function(function)
        .with_formula(clause());
        let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
            .expect("(= 1 1) is genuinely kernel-provable");
        (obligation, certificate)
    }

    /// A dependency with a `proved`, kernel-certified `f(x: i64) -> i64`
    /// that ALSO declares the staged `gcd` row — valid only under a registry
    /// that pins `gcd`.
    fn permissive_only_dependency(registry: &HandleRegistry) -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("dep", target());
        mb.set_default_producer(Producer::TRust);
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let r = fb.add(Ty::I64, x, one);
        fb.ret(vec![r]);
        let f = fb.build();
        mb.declare_handle_runtime_roles(&registry.pins()[0], &["gcd"])
            .unwrap();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        let (obligation, certificate) = certified_postcondition(f);
        function_mut(&mut module, "f").summary = Some(contract().proved());
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
        module
    }

    /// A root whose `proved` contract on `f` is backed by `dep`'s #0, so the
    /// linked walk must validate `dep`.
    fn backed_root(dep: &Module) -> Module {
        let mut m = Module::new("root");
        m.target_info = Some(target());
        let id = m
            .intern_import(
                ModuleImport::new(dep.name.clone(), dep.stable_digest())
                    .with_producer(Producer::TRust),
            )
            .expect("Module::intern_import: test fixture");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let summary = contract()
            .proved()
            .backed_by(ExternRef::new(id, "f").relying_on(ProofId::new(0)));
        let mut f = Function::declaration(FuncId::new(0), "f", ft, summary);
        f.producer = Some(Producer::TRust);
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        m
    }

    fn dependency_refused_for_gcd(report: &LinkedValidationReport<'_>) -> bool {
        has(report.errors(), |e| {
            matches!(
                e,
                ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                    if first.contains("trust_bignum_nat_gcd")
            )
        })
    }

    /// A dependency that validates ONLY under the permissive registry is
    /// admitted by a walk under that registry, then REFUSED by a walk under
    /// `pinned()` over the very same closure — and admitted again by a third
    /// permissive walk. The per-digest memo is local to one call: no verdict
    /// leaks from one walk into the next, in either direction.
    #[test]
    fn a_pinned_linked_walk_never_inherits_a_permissive_dependency_verdict() {
        let extended = with_gcd();
        let dep = permissive_only_dependency(&extended);
        assert!(only_foreign_gcd(&validate_module(&dep)));
        assert!(validate_module_with_handle_registry(&dep, &extended).is_empty());
        let root = backed_root(&dep);
        // The root itself names no handle at all.
        assert!(
            validate_module(&root).is_empty(),
            "{:?}",
            validate_module(&root)
        );
        let set = ModuleSet::new([&dep]);

        let permissive = ValidationConfig::pinned().with_handle_registry(&extended);
        let first = validate_linked_module_with_config(&root, &set, &permissive);
        assert!(first.is_ok(), "{:?}", first.errors());
        assert!(!first.handle_registry_is_pinned());

        let pinned = validate_linked_module_with_config(&root, &set, &ValidationConfig::pinned());
        assert!(dependency_refused_for_gcd(&pinned), "{:?}", pinned.errors());
        assert!(pinned.handle_registry_is_pinned());
        assert!(pinned.validated_root().is_none());
        // The pinned wrapper is the same walk.
        let wrapper = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
        assert!(
            dependency_refused_for_gcd(&wrapper),
            "{:?}",
            wrapper.errors()
        );

        let again = validate_linked_module_with_config(&root, &set, &permissive);
        assert!(again.is_ok(), "{:?}", again.errors());
    }

    // ── adversarial review: inputs the implementation did not test ──

    /// A dependency with a `proved`, kernel-certified `f(x: i64) -> i64` and
    /// NO handle at all; `shape` edits it before the certificate is minted.
    fn plain_dependency(shape: impl FnOnce(&mut FunctionBuilderShim)) -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("dep", target());
        mb.set_default_producer(Producer::TRust);
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let mut shim = FunctionBuilderShim {
            dialect: None,
            gate: None,
        };
        shape(&mut shim);
        if let Some(op) = shim.dialect.take() {
            fb.dialect_op(op);
        }
        if let Some(gate) = shim.gate.take() {
            fb.set_body_gate(gate);
        }
        let one = fb.iconst(Ty::I64, 1);
        let r = fb.add(Ty::I64, x, one);
        fb.ret(vec![r]);
        let f = fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        let (obligation, certificate) = certified_postcondition(f);
        function_mut(&mut module, "f").summary = Some(contract().proved());
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
        module
    }

    /// What `plain_dependency` adds to `f`'s body.
    struct FunctionBuilderShim {
        dialect: Option<DialectInst>,
        gate: Option<BodyGate>,
    }

    fn dependency_refused_with(report: &LinkedValidationReport<'_>, needle: &str) -> bool {
        has(report.errors(), |e| {
            matches!(
                e,
                ValidationError::ImportedModuleInvalid { import: 0, first, .. }
                    if first.contains(needle)
            )
        })
    }

    /// Adversarial 1: the extended registry is an EXACT pin table, not a
    /// namespace wildcard, on the composed lanes. Under the registry that pins
    /// `gcd`, a `Ptr`-typed `gcd` is still the named signature forgery, and an
    /// `lcm` the registry does not pin is still a foreign declaration — on the
    /// codegen config lane and the linked codegen lane alike.
    #[test]
    fn an_extended_registry_is_not_a_wildcard_on_the_codegen_and_linked_lanes() {
        let extended = with_gcd();
        let config = ValidationConfig::pinned()
            .with_handle_registry(&extended)
            .with_codegen(true);

        let mut forged = gcd_module(&extended);
        let ptr_sig = forged
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        function_mut(&mut forged, "trust_bignum_nat_gcd").ty = ptr_sig;
        let gcd_mismatch = |errors: &[ValidationError]| {
            has(errors, |e| {
                matches!(
                    e,
                    ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                        if symbol == "trust_bignum_nat_gcd"
                )
            })
        };
        let errors = validate_module_with_config(&forged, &config).into_errors();
        assert!(gcd_mismatch(&errors), "{errors:?}");
        let report = linked(&forged, &config);
        assert!(gcd_mismatch(report.errors()), "{:?}", report.errors());

        let mut unpinned = gcd_module(&extended);
        let sig = unpinned
            .add_func_type(FuncTy {
                params: vec![nat(), nat()],
                returns: vec![nat()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let next = u32::try_from(unpinned.functions.len()).unwrap();
        let mut lcm = Function::new(FuncId::new(next), "trust_bignum_nat_lcm", sig, b(0));
        lcm.calling_conv = CallingConv::C;
        unpinned
            .try_add_function(lcm)
            .expect("Module::try_add_function: test fixture");
        let errors = validate_module_with_config(&unpinned, &config).into_errors();
        assert!(foreign(&errors, "trust_bignum_nat_lcm"), "{errors:?}");
        let report = linked(&unpinned, &config);
        assert!(
            foreign(report.errors(), "trust_bignum_nat_lcm"),
            "{:?}",
            report.errors()
        );
    }

    /// Adversarial 2: the linked walk's codegen intent actually RUNS the
    /// codegen layers — on the root (a `global_asm!` block is refused only
    /// with codegen intent) and on every dependency (an unlicensed dependency
    /// body is folded into `ImportedModuleInvalid`, and licensing it clears
    /// the refusal, so the lane is not a blanket refusal).
    #[test]
    fn the_linked_codegen_lane_runs_the_codegen_layers_on_root_and_dependencies() {
        let unlicensed = plain_dependency(|_| {});
        let root = backed_root(&unlicensed);
        let set = ModuleSet::new([&unlicensed]);
        let structural = ValidationConfig::pinned();
        let codegen = structural.with_codegen(true);
        let plain = validate_linked_module_with_config(&root, &set, &structural);
        assert!(plain.is_ok(), "{:?}", plain.errors());
        let report = validate_linked_module_with_config(&root, &set, &codegen);
        assert!(
            dependency_refused_with(&report, "carries NO codegen license"),
            "{:?}",
            report.errors()
        );

        let licensed = plain_dependency(|shim| {
            shim.gate = Some(BodyGate::Gated {
                authority: "handle-types-test".into(),
                evidence: None,
            });
        });
        let mut root = backed_root(&licensed);
        let set = ModuleSet::new([&licensed]);
        let report = validate_linked_module_with_config(&root, &set, &codegen);
        assert!(report.is_ok(), "{:?}", report.errors());

        root.global_asm.push(".globl evil\nevil: ret".into());
        let plain = validate_linked_module_with_config(&root, &set, &structural);
        assert!(plain.is_ok(), "{:?}", plain.errors());
        let report = validate_linked_module_with_config(&root, &set, &codegen);
        assert!(
            matches!(
                report.errors(),
                [ValidationError::GlobalAsmNotConsumable { blocks: 1 }]
            ),
            "{:?}",
            report.errors()
        );
        assert!(report.validated_root().is_none());
    }

    /// Adversarial 3: the closed dialect-schema registry reaches every
    /// DEPENDENCY of the linked walk, not only the root. Before WS3.1 the walk
    /// passed `None`, so a dependency's unknown dialect operation was admitted
    /// by any closed-schema consumer that went through the linked lane.
    #[test]
    fn the_linked_lane_threads_the_dialect_schemas_into_every_dependency() {
        let dep = plain_dependency(|shim| {
            shim.dialect = Some(DialectInst::new("example", "unknown"));
        });
        let root = backed_root(&dep);
        let set = ModuleSet::new([&dep]);
        let schemas = DialectSchemaRegistry::new([DialectSchema {
            namespace: "example".into(),
            version: 1,
            operations: vec![OperationSchema {
                name: "known".into(),
                operands: vec![],
                results: vec![],
                attributes: vec![],
            }],
        }])
        .unwrap();

        let open = validate_linked_module_with_config(&root, &set, &ValidationConfig::pinned());
        assert!(open.is_ok(), "{:?}", open.errors());
        let closed = validate_linked_module_with_config(
            &root,
            &set,
            &ValidationConfig::pinned().with_dialect_schemas(&schemas),
        );
        assert!(
            dependency_refused_with(&closed, "violates the closed dialect schema"),
            "{:?}",
            closed.errors()
        );
        assert!(closed.validated_root().is_none());
    }

    /// Adversarial 4: composing knobs never drops the authority tier's
    /// refusal. With an authority supplied, a proof-bearing cross-crate row is
    /// `UnauthenticatedImport` on the single-module config lane whatever the
    /// registry, codegen intent or builder-call order; without one it keeps
    /// the structural faith floor of `validate_module`.
    #[test]
    fn composing_knobs_never_drops_the_unauthenticated_import_refusal() {
        let extended = with_gcd();
        let dep = plain_dependency(|_| {});
        let root = backed_root(&dep);
        let unauthenticated = |errors: &[ValidationError]| {
            has(errors, |e| {
                matches!(e, ValidationError::UnauthenticatedImport { import: 0, .. })
            })
        };

        let authority_first = ValidationConfig::pinned()
            .with_authority(&RejectingModuleProofAuthority)
            .with_handle_registry(&extended)
            .with_codegen(true);
        let registry_first = ValidationConfig::pinned()
            .with_handle_registry(&extended)
            .with_codegen(true)
            .with_authority(&RejectingModuleProofAuthority);
        for config in [authority_first, registry_first] {
            let report = validate_module_with_config(&root, &config);
            assert!(unauthenticated(report.errors()), "{:?}", report.errors());
            assert!(report.validated_module().is_none());
            assert!(!report.handle_registry_is_pinned());
        }

        let structural = ValidationConfig::pinned().with_handle_registry(&extended);
        assert!(validate_module_with_config(&root, &structural).is_ok());
        assert_eq!(
            validate_module_with_config(&root, &ValidationConfig::pinned()).into_errors(),
            validate_module(&root)
        );
    }

    /// Adversarial 5: `handle_registry_is_pinned` is conservative. A
    /// STRICTER registry (empty, so it admits nothing) and a reordered-entry
    /// row both report `false` even though neither extends the trusted base,
    /// and the empty one refuses the pinned Nat module on the linked codegen
    /// lane.
    #[test]
    fn the_pinned_bit_is_false_for_every_registry_that_is_not_the_pinned_table() {
        let empty = HandleRegistry::from_pins(&[]).unwrap();
        let config = ValidationConfig::pinned()
            .with_handle_registry(&empty)
            .with_codegen(true);
        assert!(!config.handle_registry_is_pinned());
        let module = nat_module();
        let report = linked(&module, &config);
        assert!(!report.is_ok());
        assert!(!report.handle_registry_is_pinned());

        let mut reversed = nat_pin().entry_points.to_vec();
        reversed.reverse();
        let reversed = nat_row_with(reversed);
        assert!(
            !ValidationConfig::pinned()
                .with_handle_registry(&reversed)
                .handle_registry_is_pinned()
        );
        assert!(
            ValidationConfig::pinned()
                .with_handle_registry(HandleRegistry::pinned())
                .handle_registry_is_pinned()
        );
    }
}
