// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.13 — `Module.closure_layouts`, the declared environment frame of a
//! first-class closure (wire v58, F-055).
//!
//! What the table IS: the producer's byte image for a `Ty::Closure`
//! environment, offsets in CAPTURE order, with exactly the v42 tuple-table
//! rules. It exists because `repr(Rust)` REORDERS upvars, and a backend that
//! lays the environment out as a declaration-order C struct writes the wrong
//! image.
//!
//! What it is NOT: a claim that any backend implements the closure
//! application ABI, and not a change to the application semantics. Application
//! stays BY VALUE (`lowering-target-subset.md` §G18-2(b)): captures are spread
//! as leading arguments, so a stateful `Fn`/`FnMut` whose state must persist
//! across calls still uses the explicit environment-aggregate spelling.
//!
//! The codegen refusal is therefore LIFTED, not deleted: a closure type with
//! no row keeps the refusal in its exact previous shape, which is the
//! right-reason twin under every positive below.

use trust_ir::constant::Constant;
use trust_ir::shape::{LayoutError, TyLayoutKind};
use trust_ir::ty::{ClosureTy, FuncTy, Ty};
use trust_ir::value::ClosureTyId;
use trust_ir::{
    BodyGate, ClosureLayoutDescriptor, Endianness, Interpreter, Module, Producer, TargetInfo,
};
use trust_ir_build::validate::CLOSURE_LAYOUT_TABLE_REASON_PREFIX;
use trust_ir_build::{
    ModuleBuilder, ValidationError, validate_module, validate_module_for_codegen,
};

#[path = "../../trust-ir-conformance/tests/generate/signature_abi_descriptor.rs"]
mod abi_fixture;

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

/// `move |x| lo as u64 + hi + x` with `lo: U8 = 3`, `hi: U64 = 5`, applied at
/// `x = 16`, so `program()` is 24.
///
/// The captures are declared `[U8, U64]` — a shape rustc lays out with the
/// WIDE capture FIRST, which is exactly the reordering this table exists to
/// carry.
fn two_capture_closure() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("closure_layout", target());
    mb.set_default_producer(Producer::TRust);
    let physical = mb.add_func_type(vec![Ty::U8, Ty::U64, Ty::U64], vec![Ty::U64]);
    let apparent = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let closure_ty = Ty::Closure(ClosureTyId::new(0));

    let body = {
        let mut fb = mb.function("add_lo_hi", physical);
        let e = fb.create_block();
        let lo = fb.add_block_param(e, Ty::U8);
        let hi = fb.add_block_param(e, Ty::U64);
        let x = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let lo_wide = fb.zext(Ty::U8, Ty::U64, lo);
        let s = fb.add(Ty::U64, lo_wide, hi);
        let s = fb.add(Ty::U64, s, x);
        fb.ret(vec![s]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let lit = fb.const_value(
            closure_ty.clone(),
            Constant::Closure {
                func: body,
                captures: vec![Constant::Int(3), Constant::Int(5)],
            },
        );
        let x = fb.uconst(Ty::U64, 16);
        let r = fb.call_indirect(lit, apparent, vec![x]);
        fb.ret(vec![r]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U8, Ty::U64],
    })
    .expect("Module::add_closure_type: test fixture");
    m
}

/// rustc's reordered frame: the `U64` capture at offset 0, the `U8` after it.
fn reordered_frame() -> ClosureLayoutDescriptor {
    ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    }
}

fn closure_ty() -> Ty {
    Ty::Closure(ClosureTyId::new(0))
}

/// Every function licensed for codegen, so `validate_module_for_codegen`
/// reaches the lowerability rules instead of stopping at the gate.
fn licensed(module: &Module) -> Module {
    let mut licensed = module.clone();
    for func in &mut licensed.functions {
        func.body_gate = Some(BodyGate::Ungated);
    }
    licensed
}

fn closure_refusals(module: &Module) -> usize {
    validate_module_for_codegen(&licensed(module))
        .iter()
        .filter(|error| {
            matches!(
                error,
                ValidationError::UnlowerableForCodegen { inst: "CallIndirect", detail, .. }
                    if detail.contains("Ty::Closure")
            )
        })
        .count()
}

fn run_program(module: &Module) -> Result<u128, String> {
    let id = module.function_by_name("program").ok_or("no @program")?.id;
    Interpreter::with_module(module)
        .execute_func(id, Vec::new())
        .map_err(|error| format!("{error:?}"))
        .and_then(|outcome| {
            outcome
                .returns
                .first()
                .and_then(|value| value.as_int())
                .map(|int| int.as_unsigned())
                .ok_or_else(|| format!("no scalar result: {:?}", outcome.returns))
        })
}

// ---------------------------------------------------------------------------
// positive + negative twin
// ---------------------------------------------------------------------------

/// POSITIVE. A two-capture closure whose declared frame is rustc-REORDERED
/// (capture 1 at offset 0) has a byte image, validates, and is lowerable.
/// The interpreter's result is unchanged, because the table declares a
/// LAYOUT and not a semantics: application is still by value, captures spread
/// in capture order.
#[test]
fn a_declared_reordered_frame_is_lowerable_and_changes_no_result() {
    let undeclared = two_capture_closure();
    let mut declared = two_capture_closure();
    declared.closure_layouts.push(reordered_frame());

    assert!(
        validate_module(&declared).is_empty(),
        "{:?}",
        validate_module(&declared)
    );
    assert_eq!(closure_refusals(&declared), 0);

    let shape = declared
        .ty_layout_shape(&closure_ty())
        .expect("a declared frame has a byte image");
    assert_eq!(shape.size_bits, 128);
    assert_eq!(shape.align_bits, Some(64));
    let TyLayoutKind::Closure { id, captures } = &shape.kind else {
        panic!("expected a closure layout, got {:?}", shape.kind);
    };
    assert_eq!(*id, ClosureTyId::new(0));
    // Capture ORDER is the field order; the OFFSETS are the physical image.
    assert_eq!(
        captures
            .iter()
            .map(|capture| capture.offset_bits)
            .collect::<Vec<_>>(),
        vec![Some(64), Some(0)]
    );

    assert_eq!(run_program(&undeclared), Ok(24));
    assert_eq!(
        run_program(&declared),
        Ok(24),
        "a layout declaration must not move a value"
    );
}

/// NEGATIVE TWIN. The SAME module without the row keeps the refusal in its
/// exact previous shape — so the rule reads the declaration rather than
/// having simply stopped refusing.
#[test]
fn the_same_closure_without_a_row_stays_unlowerable() {
    let undeclared = two_capture_closure();
    assert!(
        validate_module(&undeclared).is_empty(),
        "an undeclared frame is not a well-formedness error, only a codegen one"
    );
    assert_eq!(closure_refusals(&undeclared), 1);
    assert!(matches!(
        undeclared.ty_layout_shape(&closure_ty()),
        Err(LayoutError::UnsupportedTyShape(_))
    ));
}

#[test]
fn declared_frame_cannot_lift_an_apparent_signature_abi_claim() {
    use trust_ir::signature_abi::{
        AbiArgument, AbiAttributes, AbiBinding, AbiBindingPlace, AbiPassMode, AbiRegister,
        AbiRegisterClass, AbiScalar,
    };

    let mut unclaimed = two_capture_closure();
    unclaimed.closure_layouts.push(reordered_frame());
    assert!(validate_module(&unclaimed).is_empty());
    assert_eq!(closure_refusals(&unclaimed), 0);

    let lane = |place| AbiArgument {
        size: 8,
        align: 8,
        mode: AbiPassMode::Direct(AbiScalar {
            register: AbiRegister {
                class: AbiRegisterClass::Integer,
                bytes: 8,
            },
            source_offset: 0,
            source_bytes: 8,
            value_bits: 64,
            attributes: AbiAttributes::default(),
        }),
        bindings: vec![AbiBinding {
            place,
            carrier_offset: 0,
            carrier_bytes: 8,
            source_offset: 0,
            source_bytes: 8,
        }],
    };
    let mut descriptor = abi_fixture::descriptor();
    descriptor.fixed_count = 1;
    descriptor.arguments = vec![lane(AbiBindingPlace::Parameter(0))];
    descriptor.result = lane(AbiBindingPlace::Result(0));
    let mut claimed = unclaimed.clone();
    let apparent = claimed.closure_types[0].func;
    claimed.func_types[apparent.as_usize()].abi = Some(descriptor);
    assert!(
        validate_module(&claimed).is_empty(),
        "{:?}",
        validate_module(&claimed)
    );
    assert!(claimed.ty_layout_shape(&closure_ty()).is_ok());
    let errors = validate_module_for_codegen(&licensed(&claimed));
    let reasons: Vec<_> = errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::UnlowerableForCodegen {
                inst: "CallIndirect",
                detail,
                ..
            } => Some(detail),
            _ => None,
        })
        .collect();
    assert_eq!(reasons.len(), 1, "{errors:?}");
    assert!(reasons[0].contains("apparent signature carries typed ABI placement"));
    assert!(!reasons[0].contains("no such row"));
    assert_eq!(run_program(&unclaimed), Ok(24));
    let unsupported = run_program(&claimed).expect_err("typed ABI execution is unsupported");
    assert!(unsupported.contains("UnsupportedCall"));
    assert!(unsupported.contains("typed signature ABI transport is not implemented"));
}

// ---------------------------------------------------------------------------
// mutation controls — the row is READ, not counted
// ---------------------------------------------------------------------------

/// (a) Two captures occupying the same bytes.
#[test]
fn overlapping_capture_offsets_are_refused() {
    let mut m = two_capture_closure();
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![0, 0],
    });
    assert!(matches!(
        m.ty_layout_shape(&closure_ty()),
        Err(LayoutError::ClosureLayoutIncoherent(_))
    ));
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX))),
        "{:?}",
        validate_module(&m)
    );
    // And the codegen refusal is NOT silently lifted by an incoherent row.
    assert_eq!(closure_refusals(&m), 1);
}

/// (b) A frame too small for its last capture.
#[test]
fn a_frame_shorter_than_its_last_capture_is_refused() {
    let mut m = two_capture_closure();
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    assert!(matches!(
        m.ty_layout_shape(&closure_ty()),
        Err(LayoutError::ClosureLayoutIncoherent(_))
    ));
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX)))
    );
}

/// (c) A row naming a closure type the module does not define.
#[test]
fn a_row_naming_no_closure_type_is_refused() {
    let mut m = two_capture_closure();
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(7),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX)))
    );
}

/// Two rows for ONE closure type: never resolve to the first.
#[test]
fn two_rows_for_one_closure_type_are_refused() {
    let mut m = two_capture_closure();
    m.closure_layouts.push(reordered_frame());
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![0, 8],
    });
    assert!(matches!(
        m.closure_layout_descriptor(ClosureTyId::new(0)),
        Err(LayoutError::ClosureLayoutIncoherent(_))
    ));
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX)))
    );
}

/// A capture at an offset its own alignment does not divide.
#[test]
fn a_misaligned_capture_is_refused() {
    let mut m = two_capture_closure();
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![0, 1],
    });
    assert!(matches!(
        m.ty_layout_shape(&closure_ty()),
        Err(LayoutError::ClosureLayoutIncoherent(_))
    ));
}

/// A closure that captures a value of its OWN type (by value, no pointer in
/// between) has no finite frame. The reader runs the coherence check on
/// every decoded blob, so the cycle must fail closed by name rather than
/// recurse without bound — the guard the v42 tuple table already has.
#[test]
fn a_self_capturing_closure_fails_closed() {
    let mut m = Module::new("self_capture");
    m.target_info = Some(target());
    let apparent = m
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = m
        .add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![Ty::Closure(ClosureTyId::new(0))],
        })
        .expect("Module::add_closure_type: test fixture");
    assert_eq!(id, ClosureTyId::new(0));
    m.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: id,
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    });
    assert!(matches!(
        m.ty_layout_shape(&Ty::Closure(id)),
        Err(LayoutError::ClosureLayoutIncoherent(_))
    ));
    assert!(
        validate_module(&m)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX)))
    );
    // Through a tuple with no declared layout too: the canonical tuple
    // recomputation recurses into the capture, and the closure guard is what
    // stops it.
    let mut via_tuple = Module::new("self_capture_tuple");
    via_tuple.target_info = Some(target());
    let apparent = via_tuple
        .add_func_type(FuncTy {
            abi: None,
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = via_tuple
        .add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![Ty::Tuple(vec![Ty::U8, Ty::Closure(ClosureTyId::new(0))])],
        })
        .expect("Module::add_closure_type: test fixture");
    via_tuple.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: id,
        size: 16,
        align: 8,
        capture_offsets: vec![0],
    });
    let via_tuple_shape = via_tuple.ty_layout_shape(&Ty::Closure(id));
    assert!(
        matches!(
            via_tuple_shape,
            Err(LayoutError::ClosureLayoutIncoherent(_) | LayoutError::UnsupportedTyShape(_))
        ),
        "an undeclared tuple over a self-capture must fail closed by name: {via_tuple_shape:?}"
    );
}

/// A DECLARED FRAME DOES NOT REOPEN THE LAUNDERING ROUTE. The by-value
/// application ruling (`lowering-target-subset.md` G18-2, pinned by
/// `closure_application_by_value`) refuses `Bitcast` / `Transmute` of a
/// closure to a pointer or an integer while the closure has NO layout — and
/// names this table as the thing that must keep that true once it gives the
/// closure a size. It does: a closure's bits are its captured environment,
/// never a code address, so the cast is refused BEFORE any width is compared
/// (`LayoutError::ClosureCast`), and the interpreter never reaches the
/// laundered call. Pinned with the frame declared, which is the only case a
/// pure same-size rule would have admitted.
#[test]
fn a_declared_frame_does_not_admit_casting_the_closure_to_a_callable() {
    use trust_ir::inst::CastOp;
    use trust_ir::ty::{FieldDef, StructDef, StructRepr};
    use trust_ir::value::StructId;

    // An 8-byte frame: exactly `Ptr`'s and `U64`'s width, so the same-size
    // rule alone would say yes.
    let frame = ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 8,
        align: 8,
        capture_offsets: vec![0],
    };
    for (op, dst) in [
        (CastOp::Bitcast, Ty::Ptr),
        (CastOp::Transmute, Ty::Ptr),
        (CastOp::Transmute, Ty::U64),
    ] {
        let mut mb = ModuleBuilder::new_with_target_info("closure_cast_laundering", target());
        mb.set_default_producer(Producer::TRust);
        let physical = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let apparent = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
        let body = {
            let mut fb = mb.function("bump", physical);
            let e = fb.create_block();
            let seed = fb.add_block_param(e, Ty::U64);
            let x = fb.add_block_param(e, Ty::U64);
            fb.switch_to_block(e);
            let s = fb.add(Ty::U64, seed, x);
            fb.ret(vec![s]);
            fb.build()
        };
        {
            let mut fb = mb.function("program", nullary);
            let e = fb.create_block();
            fb.switch_to_block(e);
            let c = fb.const_value(
                closure_ty(),
                Constant::Closure {
                    func: body,
                    captures: vec![Constant::Int(7)],
                },
            );
            let laundered = fb.cast(op, closure_ty(), dst.clone(), c);
            let zero = fb.uconst(Ty::U64, 0);
            let r = fb.call_indirect(laundered, physical, vec![zero]);
            fb.ret(vec![r]);
            fb.build();
        }
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        m.add_closure_type(ClosureTy {
            func: apparent,
            captures: vec![Ty::U64],
        })
        .expect("Module::add_closure_type: test fixture");
        m.closure_layouts.push(frame.clone());
        // The frame itself is coherent: the refusal below is the cast's, not
        // the table's.
        assert!(
            m.ty_layout_shape(&closure_ty()).is_ok(),
            "{op:?}: {:?}",
            m.ty_layout_shape(&closure_ty())
        );
        assert!(matches!(
            m.layout_sensitive_cast_evidence(op, &closure_ty(), &dst),
            Err(LayoutError::ClosureCast { .. })
        ));
        let errors = validate_module(&m);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::CastLayoutUnsupported { src, .. } if src.starts_with("closure.")
            )),
            "{op:?} closure -> {dst}: a declared frame must not make the closure castable, got {errors:?}"
        );
        assert!(
            run_program(&m).is_err(),
            "{op:?}: the interpreter must never reach the laundered call"
        );
    }

    // Through an AGGREGATE that holds the closure by value: the environment
    // bytes are the same bytes, so a struct wrapper is refused too — and a
    // pointer TO the closure is not (its bits are an address).
    let mut m = two_capture_closure();
    m.closure_layouts.push(reordered_frame());
    let wrapper = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Wrapper".into(),
        fields: vec![FieldDef {
            name: "f".into(),
            ty: closure_ty(),
            offset: Some(0),
        }],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    assert!(m.type_holds_closure_by_value(&Ty::Struct(wrapper)));
    assert!(matches!(
        m.layout_sensitive_cast_evidence(CastOp::Transmute, &Ty::Struct(wrapper), &Ty::U128),
        Err(LayoutError::ClosureCast { .. })
    ));
    assert!(!m.type_holds_closure_by_value(&Ty::Ref(Box::new(closure_ty()))));
    assert!(!matches!(
        m.layout_sensitive_cast_evidence(
            CastOp::Bitcast,
            &Ty::Ref(Box::new(closure_ty())),
            &Ty::Ptr
        ),
        Err(LayoutError::ClosureCast { .. })
    ));
}

/// (d) The table is IDENTITY. Swapping two capture offsets is a different
/// byte image and must be a different module — a digest that ignored the
/// table would let a producer swap a frame under a pinned hash.
#[test]
fn swapping_two_capture_offsets_changes_the_stable_digest() {
    let mut declared = two_capture_closure();
    declared.closure_layouts.push(reordered_frame());

    let mut swapped = two_capture_closure();
    swapped.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![0, 8],
    });
    assert!(validate_module(&swapped).is_empty());

    assert_ne!(declared.stable_digest(), swapped.stable_digest());
    // And an absent table is a third identity, not silently equal to either.
    assert_ne!(
        two_capture_closure().stable_digest(),
        declared.stable_digest()
    );
}

// ---------------------------------------------------------------------------
// review — a frame inside a frame, and a frame's total that lies
// ---------------------------------------------------------------------------

/// REVIEW. A closure CAPTURED BY VALUE inside another closure sizes the outer
/// frame by its OWN declared frame — a legitimate two-level environment is
/// admitted with the inner image at the declared offset — and the outer row
/// fails closed by name the moment the inner frame is undeclared, since an
/// outer total nothing can size is not evidence. Mutation control: a total
/// one byte short of the nested capture's end is refused as incoherent, not
/// rounded up.
#[test]
fn a_nested_closure_frame_is_sized_by_its_own_declared_row() {
    fn module(inner_row: bool, outer_size: u64) -> Module {
        let mut m = Module::new("nested_frames");
        m.target_info = Some(target());
        let apparent = m
            .add_func_type(FuncTy {
                abi: None,
                params: vec![],
                returns: vec![Ty::U64],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let inner = m
            .add_closure_type(ClosureTy {
                func: apparent,
                captures: vec![Ty::U8, Ty::U64],
            })
            .expect("Module::add_closure_type: test fixture");
        let outer = m
            .add_closure_type(ClosureTy {
                func: apparent,
                captures: vec![Ty::U8, Ty::Closure(inner)],
            })
            .expect("Module::add_closure_type: test fixture");
        if inner_row {
            m.closure_layouts.push(ClosureLayoutDescriptor {
                origin: None,
                closure: inner,
                size: 16,
                align: 8,
                capture_offsets: vec![8, 0],
            });
        }
        m.closure_layouts.push(ClosureLayoutDescriptor {
            origin: None,
            closure: outer,
            size: outer_size,
            align: 8,
            capture_offsets: vec![0, 8],
        });
        m
    }
    let outer = Ty::Closure(ClosureTyId::new(1));

    let nested = module(true, 24);
    let shape = nested
        .ty_layout_shape(&outer)
        .expect("both frames declared");
    assert_eq!(shape.size_bits, 24 * 8);
    let TyLayoutKind::Closure { captures, .. } = &shape.kind else {
        panic!("{shape:?}");
    };
    assert_eq!(captures[1].offset_bits, Some(64));
    assert_eq!(validate_module(&nested), vec![]);

    let undeclared_inner = module(false, 24);
    assert!(
        matches!(
            undeclared_inner.ty_layout_shape(&outer),
            Err(LayoutError::UnsupportedTyShape(_))
        ),
        "the outer frame cannot be sized without the inner one"
    );
    assert!(
        validate_module(&undeclared_inner)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX))),
        "an outer row over an undeclared inner frame is refused by name"
    );

    let short = module(true, 23);
    assert!(matches!(
        short.ty_layout_shape(&outer),
        Err(LayoutError::ClosureLayoutIncoherent(id)) if id == ClosureTyId::new(1)
    ));
    assert!(
        validate_module(&short)
            .iter()
            .any(|e| matches!(e, ValidationError::TupleLayoutInconsistent { reason } if reason.starts_with(CLOSURE_LAYOUT_TABLE_REASON_PREFIX)))
    );
}
