// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Amendment P (wire v54, `docs/SPEC_RATIFICATIONS.md` §19.1): what the
// validator does with a panic site — the entry a failed check calls and the
// location it reports — and with `Inst::AssertInvoke`.
//
//   * V1: the entry resolves as a callee does (`CalleeNotFound`);
//   * V2: the entry takes the kind's operands as `usize`, then the location
//     as a `Ptr` / `Ref` / `PtrConst`, is not variadic and returns nothing
//     (`PanicEntrySignatureMismatch`);
//   * V3: a static location is an existing, immutable, non-thread-local
//     global (`GlobalNotFound`, `PanicLocationGlobalInvalid`);
//   * V4: a run-time location has the entry's location parameter type
//     (`OperandTypeMismatch { op: "assert", role: "location" }`) and is an
//     ordinary SSA use;
//   * V5: a run-time location is never directly a module global's address
//     (`NonCanonicalPanicLocation`): that location's one spelling is static;
//   * V6: `AssertInvoke` has `Invoke`'s unwind discipline and joins the
//     unwind surface.

use trust_ir::{
    AssertKind, Constant, Endianness, FuncId, Global, Inst, Linkage, Module, PanicLocation,
    PanicSite, TargetInfo, Ty, ValueId,
};
use trust_ir_build::validate::{ValidationError, validate_module_report};
use trust_ir_build::{ModuleBuilder, validate_module};

/// How the check's location is spelled.
#[derive(Clone, Copy)]
enum Loc {
    /// `PanicLocation::Global(global)`.
    Static(u32),
    /// `PanicLocation::Value(%p)`, the function's location parameter.
    Param,
    /// `PanicLocation::Value(%v)`, `%v = global_addr @global.0`.
    GlobalAddr,
    /// `PanicLocation::Value(%v)`, `%v = const ptr symaddr<loc>`.
    SymbolAddr,
}

struct Shape {
    /// The entry's parameters, returns and variadicity.
    entry_params: Vec<Ty>,
    entry_returns: Vec<Ty>,
    vararg: bool,
    /// The type of the check function's location parameter `%p`.
    param_ty: Ty,
    loc: Loc,
    /// The location global's mutability and thread-locality.
    global_mutable: bool,
    global_tls: bool,
}

impl Shape {
    /// A bounds check sited on `panic_bounds_check(usize, usize, ptr)` with
    /// the static location `@global.0`: well-formed.
    fn bounds() -> Self {
        Shape {
            entry_params: vec![Ty::Usize, Ty::Usize, Ty::Ptr],
            entry_returns: vec![],
            vararg: false,
            param_ty: Ty::Ptr,
            loc: Loc::Static(0),
            global_mutable: false,
            global_tls: false,
        }
    }
}

/// The canonical 64-bit target: a bodyless C declaration (the entry) is an
/// FFI boundary, which the validator admits only on a known target.
fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn loc_global(mutable: bool, tls: bool) -> Global {
    Global {
        name: "loc".to_string(),
        ty: Ty::U64,
        mutable,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::Internal,
        tls: tls.then_some(trust_ir::TlsModel::LocalExec),
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

/// Function 0 is the entry declaration; function 1, `check(i: usize, n:
/// usize, p: P)`, asserts `i < n` with `kind(i, n)` and the shape's site,
/// then returns `i`.
fn module(shape: &Shape, kind: impl FnOnce(ValueId, ValueId) -> AssertKind) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("assert_panic_site", target());
    let entry_ty = if shape.vararg {
        mb.add_vararg_func_type(shape.entry_params.clone(), shape.entry_returns.clone())
    } else {
        mb.add_func_type(shape.entry_params.clone(), shape.entry_returns.clone())
    };
    let entry = mb.declare_function("panic_entry", entry_ty);
    mb.add_global(loc_global(shape.global_mutable, shape.global_tls));
    let ft = mb.add_func_type(
        vec![Ty::Usize, Ty::Usize, shape.param_ty.clone()],
        vec![Ty::Usize],
    );
    let mut fb = mb.function("check", ft);
    let bb = fb.create_block();
    let i = fb.add_block_param(bb, Ty::Usize);
    let n = fb.add_block_param(bb, Ty::Usize);
    let p = fb.add_block_param(bb, shape.param_ty.clone());
    fb.switch_to_block(bb);
    let location = match shape.loc {
        Loc::Static(global) => PanicLocation::Global(trust_ir::value::GlobalId::new(global)),
        Loc::Param => PanicLocation::Value(p),
        Loc::GlobalAddr => PanicLocation::Value(fb.global_addr(trust_ir::value::GlobalId::new(0))),
        Loc::SymbolAddr => PanicLocation::Value(fb.const_value(
            Ty::Ptr,
            Constant::SymbolAddr {
                symbol: "loc".to_string(),
                addend: 0,
            },
        )),
    };
    let in_range = fb.icmp(trust_ir::ICmpOp::Ult, Ty::Usize, i, n);
    fb.assert_sited(in_range, kind(i, n), PanicSite { entry, location });
    fb.ret(vec![i]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn bounds(i: ValueId, n: ValueId) -> AssertKind {
    AssertKind::BoundsCheck { index: i, len: n }
}

fn site_errors(errors: &[ValidationError]) -> Vec<&ValidationError> {
    errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::PanicEntrySignatureMismatch { .. }
                    | ValidationError::PanicLocationGlobalInvalid { .. }
                    | ValidationError::NonCanonicalPanicLocation { .. }
                    | ValidationError::CalleeNotFound { .. }
                    | ValidationError::GlobalNotFound { .. }
                    | ValidationError::OperandTypeMismatch { .. }
            )
        })
        .collect()
}

/// The control every refusal below is measured against: a sited bounds
/// check, a sited location-only check and a forwarded run-time location all
/// validate clean.
#[test]
fn a_well_formed_panic_site_validates() {
    let errors = validate_module(&module(&Shape::bounds(), bounds));
    assert!(errors.is_empty(), "{errors:?}");
    let forwarded = Shape {
        loc: Loc::Param,
        ..Shape::bounds()
    };
    let errors = validate_module(&module(&forwarded, bounds));
    assert!(errors.is_empty(), "{errors:?}");
    let location_only = Shape {
        entry_params: vec![Ty::Ptr],
        ..Shape::bounds()
    };
    let errors = validate_module(&module(&location_only, |_, _| AssertKind::Unspecified));
    assert!(errors.is_empty(), "{errors:?}");
}

#[test]
fn a_site_entry_that_is_no_module_function_is_refused() {
    let mut m = module(&Shape::bounds(), bounds);
    for node in &mut m.functions[1].blocks[0].body {
        if let Inst::Assert {
            site: Some(site), ..
        } = &mut node.inst
        {
            site.entry = FuncId::new(77);
        }
    }
    let errors = validate_module(&m);
    assert!(
        errors.contains(&ValidationError::CalleeNotFound {
            block: 0,
            callee_id: 77
        }),
        "{errors:?}"
    );
}

/// V2, one refusal per broken axis: arity, an operand that is not `usize`,
/// a location that is not a pointer, a variadic entry, and a returning one
/// (`Never` included: a diverging entry has ONE spelling, `returns == []`).
#[test]
fn a_site_entry_must_take_the_kind_operands_then_the_location_and_return_nothing() {
    let cases: Vec<(&str, Shape)> = vec![
        (
            "missing the location",
            Shape {
                entry_params: vec![Ty::Usize, Ty::Usize],
                ..Shape::bounds()
            },
        ),
        (
            "a u32 operand",
            Shape {
                entry_params: vec![Ty::U32, Ty::Usize, Ty::Ptr],
                ..Shape::bounds()
            },
        ),
        (
            "a non-pointer location",
            Shape {
                entry_params: vec![Ty::Usize, Ty::Usize, Ty::Usize],
                ..Shape::bounds()
            },
        ),
        (
            "variadic",
            Shape {
                vararg: true,
                ..Shape::bounds()
            },
        ),
        (
            "returns a value",
            Shape {
                entry_returns: vec![Ty::Usize],
                ..Shape::bounds()
            },
        ),
        (
            "returns Never",
            Shape {
                entry_returns: vec![Ty::Never],
                ..Shape::bounds()
            },
        ),
    ];
    for (why, shape) in cases {
        let errors = validate_module(&module(&shape, bounds));
        let refused: Vec<_> = errors
            .iter()
            .filter(|e| matches!(e, ValidationError::PanicEntrySignatureMismatch { .. }))
            .collect();
        assert_eq!(refused.len(), 1, "{why}: {errors:?}");
        let ValidationError::PanicEntrySignatureMismatch {
            function,
            entry,
            expected,
            ..
        } = refused[0]
        else {
            unreachable!()
        };
        assert_eq!((function.as_str(), *entry), ("check", 0), "{why}");
        assert!(expected.contains("usize, usize"), "{why}: {expected}");
    }
    // Every admitted location type: `Ptr`, `Ref(_)`, `PtrConst(_)`.
    for location_ty in [
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::U8)),
        Ty::PtrConst(Box::new(Ty::U8)),
    ] {
        let shape = Shape {
            entry_params: vec![Ty::Usize, Ty::Usize, location_ty.clone()],
            ..Shape::bounds()
        };
        let errors = validate_module(&module(&shape, bounds));
        assert!(errors.is_empty(), "{location_ty}: {errors:?}");
    }
}

/// On an `Unspecified` (or any operand-free) kind the entry takes the
/// location ALONE: an entry shaped for a bounds check is refused there.
#[test]
fn an_unkinded_site_entry_takes_only_the_location() {
    let location_only = Shape {
        entry_params: vec![Ty::Ptr],
        ..Shape::bounds()
    };
    for kind in [AssertKind::Unspecified, AssertKind::DivByZero] {
        let errors = validate_module(&module(&location_only, |_, _| kind));
        assert!(errors.is_empty(), "{kind:?}: {errors:?}");
        let errors = validate_module(&module(&Shape::bounds(), |_, _| kind));
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::PanicEntrySignatureMismatch { .. })),
            "{kind:?}: {errors:?}"
        );
    }
    // And a bounds check on the location-only entry is refused too.
    let errors = validate_module(&module(&location_only, bounds));
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::PanicEntrySignatureMismatch { .. })),
        "{errors:?}"
    );
}

/// V3: a static location names an existing, immutable, non-TLS global.
#[test]
fn a_static_location_must_be_an_immutable_non_tls_global() {
    for (shape, reason) in [
        (
            Shape {
                global_mutable: true,
                ..Shape::bounds()
            },
            "the global is mutable",
        ),
        (
            Shape {
                global_tls: true,
                ..Shape::bounds()
            },
            "the global is thread-local",
        ),
    ] {
        let errors = validate_module(&module(&shape, bounds));
        assert_eq!(
            site_errors(&errors),
            vec![&ValidationError::PanicLocationGlobalInvalid {
                function: "check".to_string(),
                block: 0,
                inst_index: 1,
                global: 0,
                reason,
            }],
            "{errors:?}"
        );
    }
    let dangling = Shape {
        loc: Loc::Static(9),
        ..Shape::bounds()
    };
    let errors = validate_module(&module(&dangling, bounds));
    assert!(
        errors.contains(&ValidationError::GlobalNotFound {
            block: 0,
            global_id: 9
        }),
        "{errors:?}"
    );
}

/// V4: a run-time location has EXACTLY the entry's location parameter type.
#[test]
fn a_value_location_must_have_the_entry_location_parameter_type() {
    let mismatched = Shape {
        loc: Loc::Param,
        param_ty: Ty::Ref(Box::new(Ty::U8)),
        ..Shape::bounds()
    };
    let errors = validate_module(&module(&mismatched, bounds));
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::OperandTypeMismatch { op, role, expected, .. }
                if op == "assert" && role == "location" && expected == "ptr"
        )),
        "{errors:?}"
    );
    // The twin: the entry declares the same `&u8` the caller forwards.
    let matched = Shape {
        entry_params: vec![Ty::Usize, Ty::Usize, Ty::Ref(Box::new(Ty::U8))],
        ..mismatched
    };
    let errors = validate_module(&module(&matched, bounds));
    assert!(errors.is_empty(), "{errors:?}");
    // A run-time location is an SSA use: an undefined one is refused.
    let mut m = module(
        &Shape {
            loc: Loc::Param,
            ..Shape::bounds()
        },
        bounds,
    );
    for node in &mut m.functions[1].blocks[0].body {
        if let Inst::Assert {
            site: Some(site), ..
        } = &mut node.inst
        {
            site.location = PanicLocation::Value(ValueId::new(999));
        }
    }
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| format!("{e:?}").contains("999")),
        "the undefined %999 must be named: {errors:?}"
    );
}

/// V5: a location known at compile time has ONE spelling, the static one. A
/// run-time location defined directly by `global_addr` or by a zero-addend
/// `symaddr` of a module global is refused; forwarded through a parameter it
/// is admitted (the producer rule, prose-only).
#[test]
fn a_value_location_defined_by_global_addr_or_symbol_addr_is_non_canonical() {
    for loc in [Loc::GlobalAddr, Loc::SymbolAddr] {
        let shape = Shape {
            loc,
            ..Shape::bounds()
        };
        let errors = validate_module(&module(&shape, bounds));
        assert!(
            errors.contains(&ValidationError::NonCanonicalPanicLocation {
                function: "check".to_string(),
                block: 0,
                inst_index: 2,
            }),
            "{errors:?}"
        );
    }
}

/// Function 1, `guarded(c: bool, x: usize) -> usize`: `assert_invoke %c,
/// div_by_zero, panic @func.0 at @global.0 to bb1(%x) unwind bb2`; bb1
/// returns its parameter; bb2 is `pad` (a cleanup landing pad that
/// resumes, unless `pad` is false: then a plain `unreachable`).
fn assert_invoke_module(pad: bool, unwind_is_normal: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("assert_invoke", target());
    let entry_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let entry = mb.declare_function("panic_const_div_by_zero", entry_ty);
    mb.add_global(loc_global(false, false));
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::Usize], vec![Ty::Usize]);
    let mut fb = mb.function("guarded", ft);
    let bb0 = fb.create_block();
    let bb1 = fb.create_block();
    let bb2 = fb.create_block();
    let c = fb.add_block_param(bb0, Ty::Bool);
    let x = fb.add_block_param(bb0, Ty::Usize);
    let y = fb.add_block_param(bb1, Ty::Usize);
    fb.switch_to_block(bb0);
    fb.assert_invoke(
        c,
        AssertKind::DivByZero,
        PanicSite {
            entry,
            location: PanicLocation::Global(trust_ir::value::GlobalId::new(0)),
        },
        bb1,
        vec![x],
        if unwind_is_normal { bb1 } else { bb2 },
    );
    fb.switch_to_block(bb1);
    fb.ret(vec![y]);
    fb.switch_to_block(bb2);
    if pad {
        let (exn, _) = fb.landingpad(true, vec![]);
        fb.resume(exn);
    } else {
        fb.unreachable();
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// V6: `AssertInvoke` has `Invoke`'s unwind structure: its unwind
/// destination begins with a landing pad and differs from its normal one,
/// and that pad counts as entered by an unwind edge.
#[test]
fn assert_invoke_unwind_structure_is_validated() {
    let errors = validate_module(&assert_invoke_module(true, false));
    assert!(errors.is_empty(), "{errors:?}");
    let errors = validate_module(&assert_invoke_module(false, false));
    assert!(
        errors.contains(&ValidationError::UnwindDestWithoutLandingPad {
            block: 0,
            target: 2
        }),
        "{errors:?}"
    );
    let errors = validate_module(&assert_invoke_module(true, true));
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::UnwindDestWithoutLandingPad { .. })),
        "{errors:?}"
    );
    // Its site is checked like a sited `Assert`'s: a signature that takes
    // an operand the kind does not have is refused.
    let mut m = assert_invoke_module(true, false);
    m.func_types[0].params = vec![Ty::Usize, Ty::Ptr];
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::PanicEntrySignatureMismatch { .. })),
        "{errors:?}"
    );
}

/// A verdict about a function carrying an `AssertInvoke` covers the
/// panic=abort projection only, so the report lists it — on its own: the
/// surface is reported regardless of the verdict, so the pad-less variant
/// (no `LandingPad`, no `Resume`) is listed for its `AssertInvoke` alone.
#[test]
fn the_unwind_surface_includes_assert_invoke() {
    for pad in [true, false] {
        let m = assert_invoke_module(pad, false);
        let report = validate_module_report(&m);
        assert_eq!(report.unwind_surface(), vec![FuncId::new(1)], "pad: {pad}");
    }
    let plain = module(&Shape::bounds(), bounds);
    assert_eq!(validate_module_report(&plain).unwind_surface(), vec![]);
}

/// Amendment P (§19.1 rule 7): the FAITHFULNESS knob. The default codegen
/// gate accepts a siteless assert (every pre-v54 assert is one); the knob
/// refuses each siteless assert by position, whatever its kind, and admits
/// the same check once it carries a site. The IDENTITY knob is independent:
/// it refuses an `Unspecified` assert even when it is sited.
#[test]
fn the_codegen_admission_requires_a_site_only_when_asked() {
    use trust_ir_build::validate::{CodegenAdmission, missing_panic_site_errors};
    use trust_ir_build::validate_module_for_codegen_with;

    let licensed = |mut m: Module| {
        for function in &mut m.functions {
            if !function.blocks.is_empty() {
                function.body_gate = Some(trust_ir::BodyGate::Gated {
                    authority: "trust-direct-lane-structural".into(),
                    evidence: None,
                });
            }
        }
        m
    };
    let sited = licensed(module(&Shape::bounds(), bounds));
    let mut siteless = sited.clone();
    for node in &mut siteless.functions[1].blocks[0].body {
        if let Inst::Assert { site, .. } = &mut node.inst {
            *site = None;
        }
    }
    let pinned = CodegenAdmission::pinned();
    let faithful = CodegenAdmission::pinned().with_require_assert_panic_sites(true);
    assert!(!pinned.require_assert_panic_sites());
    assert!(faithful.require_assert_panic_sites());
    assert_eq!(validate_module_for_codegen_with(&siteless, &pinned), vec![]);
    assert_eq!(validate_module_for_codegen_with(&sited, &pinned), vec![]);
    let errors = validate_module_for_codegen_with(&siteless, &faithful);
    assert_eq!(
        errors,
        vec![ValidationError::AssertPanicSiteMissing {
            function: "check".to_string(),
            block: 0,
            inst_index: 1,
        }]
    );
    assert!(format!("{}", errors[0]).contains("require_assert_panic_sites"));
    assert_eq!(validate_module_for_codegen_with(&sited, &faithful), vec![]);
    assert_eq!(missing_panic_site_errors(&sited), vec![]);
    // An `AssertInvoke` always carries its site.
    assert_eq!(
        missing_panic_site_errors(&assert_invoke_module(true, false)),
        vec![]
    );
    // The identity knob still refuses a SITED `Unspecified` assert, which
    // the faithfulness knob admits.
    let location_only = Shape {
        entry_params: vec![Ty::Ptr],
        ..Shape::bounds()
    };
    let unspecified = licensed(module(&location_only, |_, _| AssertKind::Unspecified));
    let identity = CodegenAdmission::pinned().with_require_assert_panic_kinds(true);
    assert!(
        validate_module_for_codegen_with(&unspecified, &identity)
            .iter()
            .any(|e| matches!(e, ValidationError::AssertPanicKindUnspecified { .. }))
    );
    assert_eq!(
        validate_module_for_codegen_with(&unspecified, &faithful),
        vec![]
    );
}

// ---------------------------------------------------------------------------
// §4.2: an obligation sited on a check must be of a kind the check discharges
// ---------------------------------------------------------------------------

/// `m` with one `Pending` row of `obligation` sited on the check (function
/// 1, block 0, instruction 1).
fn with_sited_row(m: &Module, obligation: trust_ir::ObligationKind) -> Module {
    let mut m = m.clone();
    m.proof_obligations.push(
        trust_ir::ProofObligation::new(
            trust_ir::ProofId::new(0),
            obligation,
            trust_ir::ProofStatus::Pending,
            "amendment P row",
        )
        .with_function(FuncId::new(1))
        .with_site(trust_ir::ObligationSite::new(
            FuncId::new(1),
            trust_ir::BlockId::new(0),
            1,
        )),
    );
    m
}

fn site_kind_refused(errors: &[ValidationError]) -> bool {
    errors
        .iter()
        .any(|e| matches!(e, ValidationError::ObligationSiteKindMismatch { .. }))
}

/// A bounds row on an overflow check, an arithmetic row on a bounds check
/// and a memory row on a division check are refused: the check's kind is
/// its identity, so a row cannot be retargeted onto another check.
#[test]
fn an_obligation_kind_the_check_cannot_discharge_is_refused_on_a_kinded_assert() {
    use trust_ir::ObligationKind as K;
    let location_only = Shape {
        entry_params: vec![Ty::Ptr],
        ..Shape::bounds()
    };
    let overflow = module(&location_only, |_, _| {
        AssertKind::Overflow(trust_ir::AssertOverflowOp::Add)
    });
    let division = module(&location_only, |_, _| AssertKind::DivByZero);
    let bounds_check = module(&Shape::bounds(), bounds);
    for (m, refused, admitted) in [
        (&overflow, K::BoundsCheck, K::ArithmeticSafety),
        (&bounds_check, K::ArithmeticSafety, K::BoundsCheck),
        (&division, K::MemorySafety, K::ArithmeticSafety),
    ] {
        let errors = validate_module(&with_sited_row(m, refused.clone()));
        assert!(site_kind_refused(&errors), "{refused:?}: {errors:?}");
        let errors = validate_module(&with_sited_row(m, admitted.clone()));
        assert!(errors.is_empty(), "{admitted:?}: {errors:?}");
        // PanicFreedom is discharged by every check.
        let errors = validate_module(&with_sited_row(m, K::PanicFreedom));
        assert!(errors.is_empty(), "PanicFreedom: {errors:?}");
    }
}

/// `Unspecified` keeps admitting exactly the check-obligation kinds an
/// assert admitted before the kind existed, so no older module changes
/// verdict: ArithmeticSafety, BoundsCheck and PanicFreedom, and still not
/// MemorySafety (which admitted no assert then).
#[test]
fn an_unspecified_assert_still_admits_every_check_obligation_kind() {
    use trust_ir::ObligationKind as K;
    let location_only = Shape {
        entry_params: vec![Ty::Ptr],
        ..Shape::bounds()
    };
    let unspecified = module(&location_only, |_, _| AssertKind::Unspecified);
    for kind in [K::ArithmeticSafety, K::BoundsCheck, K::PanicFreedom] {
        let errors = validate_module(&with_sited_row(&unspecified, kind.clone()));
        assert!(errors.is_empty(), "{kind:?}: {errors:?}");
    }
    let errors = validate_module(&with_sited_row(&unspecified, K::MemorySafety));
    assert!(site_kind_refused(&errors), "{errors:?}");
}

/// The new `MemorySafety` row: misaligned-pointer and null checks admit a
/// `MemorySafety` obligation (the in-repo frontend files them so), and a
/// bounds check does not.
#[test]
fn memory_safety_obligations_site_on_misaligned_and_null_checks() {
    use trust_ir::ObligationKind as K;
    let location_only = Shape {
        entry_params: vec![Ty::Ptr],
        ..Shape::bounds()
    };
    let misaligned = module(&Shape::bounds(), |r, f| AssertKind::MisalignedPtr {
        required: r,
        found: f,
    });
    let null = module(&location_only, |_, _| AssertKind::NullPtr);
    for m in [&misaligned, &null] {
        let errors = validate_module(&with_sited_row(m, K::MemorySafety));
        assert!(errors.is_empty(), "{errors:?}");
        let errors = validate_module(&with_sited_row(m, K::BoundsCheck));
        assert!(site_kind_refused(&errors), "{errors:?}");
    }
    let errors = validate_module(&with_sited_row(
        &module(&Shape::bounds(), bounds),
        K::MemorySafety,
    ));
    assert!(
        site_kind_refused(&errors),
        "a bounds check is not MemorySafety: {errors:?}"
    );
}

/// WS1.8 rule (f) covers `AssertInvoke`: a safety claim on the check itself
/// with no `ProofRef` to a row sited on it is refused, exactly as on an
/// `Assert`.
#[test]
fn rule_f_covers_assert_invoke() {
    use trust_ir_build::validate::unbacked_claim_on_check_errors;
    let mut m = assert_invoke_module(true, false);
    let node = m.functions[1].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::AssertInvoke { .. }))
        .expect("the assert_invoke");
    node.proofs.push(trust_ir::ProofAnnotation::NoOverflow);
    let errors = unbacked_claim_on_check_errors(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::UnbackedClaimOnCheck { block: 0, .. })),
        "{errors:?}"
    );
    // Control: the claim-free `AssertInvoke` is not this rule's.
    assert_eq!(
        unbacked_claim_on_check_errors(&assert_invoke_module(true, false)),
        vec![]
    );
}
