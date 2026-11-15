// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.21 (F-061): the pinned reference-counting runtime for the Clean heap.
//
// `Retain` / `Release` / `IsUnique` carry only a pointer, and a backend routes
// them to Clean's `clean_inc` / `clean_dec` / `clean_is_exclusive`. Before
// `TRUSTED_RC_RUNTIMES` that identity was a CONVENTION: every forgery below —
// an off-pin signature, a local body, a global wearing the symbol, a
// relocatable address of it — passed the validator without any error naming
// the runtime. Each is now a NAMED refusal; the positive module is the shape
// the Clean emitter declares (`emit_trust_ir_runtime.rs`,
// `RuntimeAbi::declare`). Mutation control, measured at landing: with
// `validate_rc_entry_points` disabled, every refusal test below fails and the
// two positive tests still pass.

use trust_ir::inst::AllocOrigin;
use trust_ir::{
    Block, BlockId, BodyGate, CallingConv, Constant, Endianness, FuncTy, Global, Inst, InstrNode,
    Linkage, Module, StructPassingPolicy, TargetInfo, Ty, ValueId, Visibility,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    ModuleBuilder, RcRuntimePin, TRUSTED_HANDLE_RUNTIMES, TRUSTED_RC_RUNTIMES, rc_entry_for_symbol,
    validate_module, validate_module_for_codegen,
};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn clean_pin() -> &'static RcRuntimePin {
    TRUSTED_RC_RUNTIMES
        .iter()
        .find(|pin| pin.origin == AllocOrigin::CleanHeap)
        .expect("v1 pins the Clean heap")
}

/// The positive module: the three pinned declarations, exactly as Clean
/// declares them (plus one unpinned Clean runtime import, which stays
/// convention), and a body that uses the native ARC ops on a Clean cell and
/// calls the pinned `clean_dec` directly.
///
/// `share(p) = { retain p; u = is_unique p; release p; clean_dec(p); ret u }`
fn clean_module() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("clean_rc", target());
    let mut dec = None;
    for entry in clean_pin().entry_points {
        let ty = mb.add_func_type(entry.params.to_vec(), entry.returns.to_vec());
        let id = mb.declare_function(entry.symbol, ty);
        if entry.role == "release" {
            dec = Some(id);
        }
    }
    // Unpinned: the rest of Clean's runtime ABI is not in the table.
    let box_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::Ptr]);
    mb.declare_function("clean_box", box_ty);

    let share_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let mut fb = mb.function("share", share_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.retain(p);
    let unique = fb.is_unique(p);
    fb.release(p);
    fb.call_void(dec.expect("the row pins a release entry"), vec![p]);
    fb.ret(vec![unique]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut module.functions {
        if !function.is_declaration() {
            function.body_gate = Some(BodyGate::Gated {
                authority: "rc-runtime-pins-test".into(),
                evidence: None,
            });
        }
    }
    module
}

fn function_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut trust_ir::Function {
    module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
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

/// Retype the declaration named `symbol` to `signature`.
fn retype(module: &mut Module, symbol: &str, signature: FuncTy) {
    let ty = module
        .add_func_type(signature)
        .expect("Module::add_func_type: test fixture");
    function_mut(module, symbol).ty = ty;
}

fn only_signature_mismatch(errors: &[ValidationError], symbol: &str) -> bool {
    matches!(
        errors,
        [ValidationError::RcEntryPointSignatureMismatch { symbol: s, .. }] if s == symbol
    )
}

// ───────────────────────────── POSITIVE ─────────────────────────────

/// Row `consumer-trust-cg/19-clean-rc-runtime`: the RC runtime a backend routes
/// `Retain` / `Release` / `IsUnique` to is a pinned table, not a convention,
/// and a Clean module declaring it exactly validates, for codegen too.
#[test]
fn consumer_trust_cg_19_clean_rc_runtime_pinned_triple_with_retain_release_validates() {
    let module = clean_module();
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(validate_module_for_codegen(&module), vec![]);
    // The routing a backend reads: one entry per ARC role.
    let pin = clean_pin();
    assert_eq!(pin.calling_conv, CallingConv::C);
    for (role, symbol) in [
        ("retain", "clean_inc"),
        ("release", "clean_dec"),
        ("is_unique", "clean_is_exclusive"),
    ] {
        assert_eq!(pin.entry(role).map(|entry| entry.symbol), Some(symbol));
        let (row, entry) = rc_entry_for_symbol(symbol).unwrap();
        assert_eq!(row.origin, AllocOrigin::CleanHeap);
        assert_eq!(entry.role, role);
        let decl = module.functions.iter().find(|f| f.name == symbol).unwrap();
        assert!(decl.is_declaration());
        assert_eq!(decl.linkage, Linkage::External);
        assert_eq!(module.func_type(decl.ty), Some(&entry.func_ty()));
    }
    // A `display_path` equal to the symbol is the one other admitted spelling.
    let mut module = clean_module();
    function_mut(&mut module, "clean_inc").display_path = Some("clean_inc".into());
    assert_eq!(validate_module(&module), vec![]);
}

/// Row `small-designs/OMET-10-abi-manifest` (the RC-identity fact only): the
/// runtime identity of a `CleanHeap` cell is stated in-tree, and it is
/// disjoint from every handle runtime. The rest of OMET-10 stays open.
#[test]
fn small_designs_omet_10_rc_runtime_identity_is_a_pinned_fact() {
    assert_eq!(TRUSTED_RC_RUNTIMES.len(), 1);
    assert_eq!(clean_pin().runtime, "clean_runtime");
    for entry in clean_pin().entry_points {
        assert_eq!(entry.params, &[Ty::Ptr]);
        assert!(
            TRUSTED_HANDLE_RUNTIMES
                .iter()
                .flat_map(|pin| pin.entry_points)
                .all(|handle| handle.symbol != entry.symbol)
        );
    }
    // Residue, stated: the allocation entry points are NOT pinned.
    for unpinned in [
        "clean_alloc_ctor",
        "clean_ctor_get",
        "clean_ctor_set",
        "clean_box",
        "clean_apply_n",
        "clean_nat_big",
        "clean_inc_n",
    ] {
        assert!(rc_entry_for_symbol(unpinned).is_none(), "{unpinned}");
    }
}

// ───────────────────── RcEntryPointSignatureMismatch ─────────────────────

/// The negative twin: `clean_dec(Ptr) -> I32` is refused by name, and it is
/// the ONLY error — the body's direct call binds the forged `I32` result, so
/// the module is otherwise consistent with the forged declaration.
#[test]
fn clean_dec_returning_i32_is_refused_as_signature_mismatch() {
    let mut module = clean_module();
    retype(
        &mut module,
        "clean_dec",
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        },
    );
    let call = function_mut(&mut module, "share").blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Call { .. }))
        .expect("share calls clean_dec");
    call.results = vec![ValueId::new(1000)];
    let errors = validate_module(&module);
    assert!(only_signature_mismatch(&errors, "clean_dec"), "{errors:?}");
    assert!(
        errors[0]
            .to_string()
            .contains("found signature (ptr) -> (i32)"),
        "{}",
        errors[0]
    );
}

#[test]
fn every_off_pin_declaration_shape_is_refused_as_signature_mismatch() {
    // `clean_is_exclusive` returning the Rust `bool` instead of the C `bool`
    // spelled `U8`.
    let mut module = clean_module();
    retype(
        &mut module,
        "clean_is_exclusive",
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        },
    );
    let errors = validate_module(&module);
    assert!(
        only_signature_mismatch(&errors, "clean_is_exclusive"),
        "{errors:?}"
    );

    // A variadic tail.
    let mut module = clean_module();
    retype(
        &mut module,
        "clean_inc",
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: true,
        },
    );
    let errors = validate_module(&module);
    assert!(only_signature_mismatch(&errors, "clean_inc"), "{errors:?}");

    // A `Unit` return is a one-element return list: a DIFFERENT `FuncTy`.
    let mut module = clean_module();
    retype(
        &mut module,
        "clean_inc",
        FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Unit],
            abi: None,
            is_vararg: false,
        },
    );
    assert!(only_signature_mismatch(
        &validate_module(&module),
        "clean_inc"
    ));

    // The wrong calling convention, `naked`, a foreign display path.
    for mutate in [
        (|f: &mut trust_ir::Function| f.calling_conv = CallingConv::Fast)
            as fn(&mut trust_ir::Function),
        |f| f.attrs.naked = true,
        |f| f.display_path = Some("my_crate::clean_dec".into()),
    ] {
        let mut module = clean_module();
        mutate(function_mut(&mut module, "clean_dec"));
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::RcEntryPointSignatureMismatch { symbol, .. } if symbol == "clean_dec"
            )),
            "{errors:?}"
        );
    }
}

// ────────────────────── RcEntryPointDefinedLocally ──────────────────────

/// Mutation: a local body for `clean_inc` is refused — the module would
/// substitute the count every `Retain` routed to it maintains.
#[test]
fn a_local_body_for_clean_inc_is_refused_as_defined_locally() {
    let mut module = clean_module();
    let inc = function_mut(&mut module, "clean_inc");
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    inc.blocks = vec![entry];
    inc.body_gate = Some(BodyGate::Gated {
        authority: "rc-runtime-pins-test".into(),
        evidence: None,
    });
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::RcEntryPointDefinedLocally { symbol, .. } if symbol == "clean_inc"
        )),
        "{errors:?}"
    );
    assert!(
        validate_module_for_codegen(&module)
            .iter()
            .any(|e| matches!(e, ValidationError::RcEntryPointDefinedLocally { .. }))
    );
}

#[test]
fn a_non_external_rc_declaration_is_refused_as_defined_locally() {
    for linkage in [Linkage::Internal, Linkage::Weak, Linkage::ExternalWeak] {
        let mut module = clean_module();
        function_mut(&mut module, "clean_dec").linkage = linkage;
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::RcEntryPointDefinedLocally { symbol, .. } if symbol == "clean_dec"
            )),
            "{linkage:?}: {errors:?}"
        );
    }
}

// ───────────────────── RcEntryPointShadowedByGlobal ─────────────────────

/// Mutation: a `Global` named `clean_is_exclusive` is refused.
#[test]
fn a_global_named_clean_is_exclusive_is_refused() {
    let mut module = clean_module();
    module.globals.push(global("clean_is_exclusive", Ty::U8));
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::RcEntryPointShadowedByGlobal { global, symbol }
                if global == "clean_is_exclusive" && symbol == "clean_is_exclusive"
        )),
        "{errors:?}"
    );
}

// ─────────────────────── RcEntryPointAddressTaken ───────────────────────

fn address_taken(errors: &[ValidationError], symbol: &str) -> bool {
    errors.iter().any(
        |e| matches!(e, ValidationError::RcEntryPointAddressTaken { symbol: s, .. } if s == symbol),
    )
}

/// Mutation: a `SymbolAddr("clean_dec")` inside a global initializer is
/// refused, directly and nested in an aggregate.
#[test]
fn a_symbol_address_of_clean_dec_in_a_global_initializer_is_refused() {
    let mut module = clean_module();
    let mut table = global("rc_table", Ty::Ptr);
    table.initializer = Some(Constant::SymbolAddr {
        symbol: "clean_dec".into(),
        addend: 0,
    });
    module.globals.push(table);
    let errors = validate_module(&module);
    assert!(address_taken(&errors, "clean_dec"), "{errors:?}");
    assert!(errors.iter().any(|e| matches!(
        e,
        ValidationError::RcEntryPointAddressTaken { location, .. } if location == "global 'rc_table'"
    )));

    let mut module = clean_module();
    let mut table = global("vtable", Ty::Tuple(vec![Ty::U64, Ty::Ptr]));
    table.initializer = Some(Constant::Aggregate(vec![
        Constant::Int(0),
        Constant::SymbolAddr {
            symbol: "clean_dec".into(),
            addend: 8,
        },
    ]));
    module.globals.push(table);
    let errors = validate_module(&module);
    assert!(address_taken(&errors, "clean_dec"), "{errors:?}");
}

/// A `CallIndirect` through `SymbolAddr("clean_dec")` at a forged `sig`, in a
/// module that never declares the runtime: refused, while an unpinned
/// neighbour symbol is untouched.
#[test]
fn a_call_indirect_over_a_symbol_address_of_clean_dec_is_refused() {
    let build = |symbol: &str| {
        let mut mb = ModuleBuilder::new_with_target_info("forged_rc", target());
        let forged = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
        let main_ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("main", main_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let cell = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::CleanHeap);
        let f = fb.const_value(
            Ty::Func(forged),
            Constant::SymbolAddr {
                symbol: symbol.into(),
                addend: 0,
            },
        );
        let r = fb.call_indirect(f, forged, vec![cell]);
        fb.ret(vec![r]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let errors = validate_module(&build("clean_dec"));
    assert!(address_taken(&errors, "clean_dec"), "{errors:?}");
    assert!(address_taken(
        &validate_module_for_codegen(&build("clean_dec")),
        "clean_dec"
    ));
    assert!(!address_taken(
        &validate_module(&build("clean_alloc_ctor")),
        "clean_alloc_ctor"
    ));
}

// ─────────── REVIEW: claims a pinned declaration may not carry ───────────
//
// The pin fixes the runtime's ABI, and its EFFECTS are part of that ABI: the
// entry points write (`clean_inc` / `clean_dec`) or read (`clean_is_exclusive`)
// the refcount through their pointer argument. A memory-effect attribute, a
// parameter attribute or a `Pure` annotation on the pinned declaration is a
// false claim about the trusted runtime — and a claim a backend acts on (a
// `readnone` `clean_is_exclusive` is CSE-able across a `retain`; a `readnone`
// `clean_dec` with no result is dead code) — so each is refused as a
// signature mismatch. Before the review every one of them validated.

fn only_mismatch_on(module: &Module, symbol: &str) {
    let errors = validate_module(module);
    assert!(only_signature_mismatch(&errors, symbol), "{errors:?}");
}

/// REVIEW adversarial 1: a `readnone` / `readonly` pinned declaration.
#[test]
fn a_memory_effect_attribute_on_a_pinned_rc_declaration_is_refused() {
    for symbol in ["clean_inc", "clean_dec", "clean_is_exclusive"] {
        let mut module = clean_module();
        function_mut(&mut module, symbol).attrs.readnone = true;
        only_mismatch_on(&module, symbol);
        let mut module = clean_module();
        function_mut(&mut module, symbol).attrs.readonly = true;
        only_mismatch_on(&module, symbol);
    }
}

/// REVIEW adversarial 2: the WS2.7 `readnone` check admits a direct callee
/// carrying the same claim, so a `readnone` pinned `clean_dec` laundered a
/// FALSE `readnone` claim onto a defined caller that frees a Clean cell.
#[test]
fn a_readnone_caller_cannot_launder_a_release_through_a_readnone_clean_dec() {
    let mut module = clean_module();
    function_mut(&mut module, "clean_dec").attrs.readnone = true;
    let dec = function_mut(&mut module, "clean_dec").id;
    let drop_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Ptr);
    entry.body.push(InstrNode::new(Inst::Call {
        callee: dec,
        args: vec![ValueId::new(0)],
    }));
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut drop = trust_ir::Function::new(
        trust_ir::FuncId::new(module.functions.len() as u32),
        "drop_cell",
        drop_ty,
        BlockId::new(0),
    );
    drop.blocks = vec![entry];
    drop.attrs.readnone = true;
    drop.body_gate = Some(BodyGate::Gated {
        authority: "rc-runtime-pins-test".into(),
        evidence: None,
    });
    module.functions.push(drop);
    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::RcEntryPointSignatureMismatch { symbol, .. } if symbol == "clean_dec"
        )),
        "{errors:?}"
    );
}

/// REVIEW adversarial 3: parameter attributes on the pinned pointer — a
/// `byval` changes the call's byte-level ABI; `readonly` / `nonnull` /
/// `dereferenceable` / `noalias` / `align` are claims about the runtime's
/// argument the pin does not make.
#[test]
fn a_parameter_attribute_on_a_pinned_rc_declaration_is_refused() {
    let mutations: [fn(&mut trust_ir::ParamAttrs); 6] = [
        |p| p.byval = true,
        |p| p.readonly = true,
        |p| p.nonnull = true,
        |p| p.dereferenceable = Some(16),
        |p| p.noalias = true,
        |p| p.align = Some(8),
    ];
    for mutate in mutations {
        let mut module = clean_module();
        let mut attrs = trust_ir::ParamAttrs::default();
        mutate(&mut attrs);
        function_mut(&mut module, "clean_inc").attrs.params = vec![attrs];
        only_mismatch_on(&module, "clean_inc");
    }
    // An explicitly EMPTY parameter record is the default spelled out: admitted.
    let mut module = clean_module();
    function_mut(&mut module, "clean_inc").attrs.params = vec![trust_ir::ParamAttrs::default()];
    assert_eq!(validate_module(&module), vec![]);
}

/// REVIEW adversarial 4: a `Pure` claim on an entry point that writes the
/// refcount.
#[test]
fn a_pure_annotation_on_a_pinned_rc_declaration_is_refused() {
    for symbol in ["clean_inc", "clean_dec", "clean_is_exclusive"] {
        let mut module = clean_module();
        function_mut(&mut module, symbol)
            .proofs
            .push(trust_ir::proof::ProofAnnotation::Pure);
        only_mismatch_on(&module, symbol);
    }
}

/// REVIEW legitimate twin: pure codegen HINTS (`cold`, `inlinehint`) state
/// nothing about the runtime's effects or ABI and stay admitted, so a producer
/// marking the release path cold is not refused.
#[test]
fn codegen_hints_on_a_pinned_rc_declaration_are_admitted() {
    let mut module = clean_module();
    function_mut(&mut module, "clean_dec").attrs.cold = true;
    function_mut(&mut module, "clean_inc").attrs.inlinehint = true;
    assert_eq!(validate_module(&module), vec![]);
    assert_eq!(validate_module_for_codegen(&module), vec![]);
}
