// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// GAP G3 regression tests — three checks that turn v41 decoration into
// enforcement:
//
//   (a) `validate_module_for_codegen` — the `Function::body_gate` codegen
//       license. `Ungated` and "no claim at all" are BOTH refused, as
//       SEPARATELY MATCHABLE variants.
//   (b) the reserved `@trust-internal::` SpecModule namespace.
//   (c) `Ty::Error` anywhere in a module — including the ~30 instruction
//       fields that spell a `Ty` inline, of which validation previously
//       checked exactly one (`Inst::Const`).
//
// Every test here fails against the pre-fix validator; each was observed
// failing before the corresponding check was written.

use trust_ir::dialect::{AttrEntry, AttrValue, DialectInst};
use trust_ir::inst::{
    AllocOrigin, AtomicRMWOp, BinOp, BindingFrameDef, BindingSlot, CastOp, ICmpOp, Inst, Ordering,
};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BindingFrameId, BlockId, FuncId, GlobalId, ValueId};
use trust_ir::{
    Block, BodyGate, CallingConv, Function, FunctionSummary, Linkage, Module, SpecEnforcementMode,
    SpecInvariant, SpecModule, SpecOrigin, SpecVar,
};
use trust_ir_build::validate::{
    RESERVED_TRUST_INTERNAL_SPEC_MODULES, ValidationError, codegen_license_errors,
    validate_module_for_codegen,
};
use trust_ir_build::validate_module;

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn b(i: u32) -> BlockId {
    BlockId::new(i)
}
fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn ret_block() -> Block {
    let mut block = Block::new(b(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    block
}

/// A module holding `count` well-formed nullary functions, each with a body.
/// The caller stamps whatever licenses it wants to test.
fn bodies(names: &[&str]) -> Module {
    let mut module = Module::new("m");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (i, name) in names.iter().enumerate() {
        let mut func = Function::new(FuncId::new(i as u32), *name, ft, b(0));
        func.blocks.push(ret_block());
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

fn gate_errors(module: &Module) -> Vec<ValidationError> {
    validate_module_for_codegen(module)
        .into_iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::UngatedBodyForCodegen { .. }
                    | ValidationError::UnlicensedBodyForCodegen { .. }
            )
        })
        .collect()
}

// ===========================================================================
// (a) the codegen license
// ===========================================================================

#[test]
fn plain_validate_module_is_structurally_clean_for_every_license_state() {
    // The composition boundary, stated as a test: `validate_module` is
    // license-BLIND. A module may legitimately CARRY an ungated or unlicensed
    // body — that is what an artifact under inspection looks like. Only
    // CONSUMING one for codegen is refused, and only by the codegen entry
    // point. If this ever starts failing, the license check has leaked into
    // the structural pass and every producer's test suite breaks.
    let mut module = bodies(&["gated", "ungated", "grandfathered"]);
    module.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".to_string(),
        evidence: None,
    });
    module.functions[1].body_gate = Some(BodyGate::Ungated);
    module.functions[2].body_gate = None;
    assert_eq!(validate_module(&module), Vec::new());
}

#[test]
fn gated_body_may_proceed() {
    // An authority OUTSIDE `EVIDENCE_BOUND_GATE_AUTHORITIES` keeps its
    // pre-WS1.5 standing on the policy-free entry point. (Until WS1.5 this
    // test used `clean-kernel-tv` with no evidence at all — exactly the F-006
    // hole; that shape is now the c05 negative twin in section (d).)
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "trust-direct-lane-structural".to_string(),
        evidence: None,
    });
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
}

#[test]
fn affirmatively_ungated_body_is_refused() {
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    assert_eq!(
        gate_errors(&module),
        vec![ValidationError::UngatedBodyForCodegen {
            function: 0,
            name: "f".to_string(),
        }]
    );
}

#[test]
fn absent_license_is_refused_under_its_own_variant() {
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = None;
    assert_eq!(
        gate_errors(&module),
        vec![ValidationError::UnlicensedBodyForCodegen {
            function: 0,
            name: "f".to_string(),
        }]
    );
}

#[test]
fn ungated_and_unlicensed_never_collapse_into_one_message() {
    // THE load-bearing test of gap (a). `None` and `Ungated` mean opposite
    // things — "no claim was made" versus "the claim is that no gate ran" —
    // and a consumer that grandfathers pre-v41 artifacts must be able to admit
    // the first while still refusing the second. That is only expressible if
    // the two arrive as different values AND different rendered text.
    let mut module = bodies(&["ungated", "grandfathered"]);
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    module.functions[1].body_gate = None;

    let errors = gate_errors(&module);
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(matches!(
        errors[0],
        ValidationError::UngatedBodyForCodegen { function: 0, .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::UnlicensedBodyForCodegen { function: 1, .. }
    ));

    // Distinguishable in rendered form too, not merely in the type.
    let rendered: Vec<String> = errors.iter().map(ToString::to_string).collect();
    assert_ne!(rendered[0], rendered[1]);
    assert!(
        rendered[0].contains("AFFIRMATIVELY UNGATED"),
        "{rendered:?}"
    );
    assert!(rendered[1].contains("NO codegen license"), "{rendered:?}");

    // And the grandfathering policy the caller owns is expressible as a filter.
    let strict_but_grandfathering: Vec<_> = errors
        .into_iter()
        .filter(|e| !matches!(e, ValidationError::UnlicensedBodyForCodegen { .. }))
        .collect();
    assert_eq!(strict_but_grandfathering.len(), 1);
    assert!(matches!(
        strict_but_grandfathering[0],
        ValidationError::UngatedBodyForCodegen { .. }
    ));
}

#[test]
fn bodyless_declarations_are_not_codegen_subjects() {
    // A declaration emits no machine code, so it is refused for nothing. Both
    // shapes the validator already recognizes as legitimate body-less
    // functions are covered: the external import, and the contract-only
    // declaration whose linkage is NOT external (audit 2026-06-25 F4) — that
    // second one is why the check uses linkage-agnostic `is_declaration()`
    // rather than `is_bodyless_external_declaration`.
    let mut module = Module::new("m");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut import = Function::new(FuncId::new(0), "imported", ft, b(0));
    import.linkage = Linkage::External;
    // A cross-crate RUST import, not a C one: `is_foreign_abi_boundary` is
    // false, so this module needs no `target_info` and the assertion below can
    // be exact equality rather than a filter.
    import.calling_conv = CallingConv::Rust;
    import.body_gate = None;
    module
        .try_add_function(import)
        .expect("Module::try_add_function: test fixture");

    let mut contract_only = Function::new(FuncId::new(1), "contract_only", ft, b(0));
    contract_only.linkage = Linkage::Internal;
    contract_only.summary = Some(FunctionSummary::new());
    contract_only.body_gate = None;
    module
        .try_add_function(contract_only)
        .expect("Module::try_add_function: test fixture");

    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
}

#[test]
fn an_ungated_declaration_is_still_not_refused() {
    // Even an AFFIRMATIVE `ungated` on a body-less declaration is not a codegen
    // refusal: there is no body here to generate code from. Whatever module
    // owns the definition is where the license is decided.
    let mut module = Module::new("m");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut import = Function::new(FuncId::new(0), "imported", ft, b(0));
    import.linkage = Linkage::External;
    import.calling_conv = CallingConv::Rust;
    import.body_gate = Some(BodyGate::Ungated);
    module
        .try_add_function(import)
        .expect("Module::try_add_function: test fixture");
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
}

#[test]
fn codegen_validation_composes_rather_than_replaces() {
    // The structural errors must still be reported: `validate_module_for_codegen`
    // is `validate_module` + the license layer, never a license-only check.
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".to_string(),
        evidence: None,
    });
    // Break the body structurally: a block with no terminator.
    module.functions[0].blocks[0].body.clear();
    module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Assume { cond: v(9) }));

    let errors = validate_module_for_codegen(&module);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::MissingTerminator { .. })),
        "{errors:?}"
    );
    // ...and the licensed body contributes no license error.
    assert!(gate_errors(&module).is_empty());
}

#[test]
fn codegen_license_errors_is_the_license_layer_alone() {
    // The separately-exposed layer, for a caller that already validated through
    // `validate_module_with_authority`. It must be exactly the tail of
    // `validate_module_for_codegen`.
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    let composed = validate_module_for_codegen(&module);
    let layer = codegen_license_errors(&module);
    assert_eq!(layer.len(), 1);
    assert_eq!(composed[composed.len() - layer.len()..], layer[..]);
}

// ===========================================================================
// (b) the reserved `@trust-internal::` SpecModule namespace
// ===========================================================================

fn disclosure(name: &str) -> SpecModule {
    let mut spec = SpecModule::new(name);
    spec.invariants
        .push(SpecInvariant::new("disclosure", "descriptive row"));
    spec
}

fn with_spec(spec: SpecModule) -> Module {
    let mut module = Module::new("m");
    module.spec_modules.push(spec);
    module
}

fn reserved_errors(module: &Module) -> Vec<ValidationError> {
    validate_module(module)
        .into_iter()
        .filter(|e| matches!(e, ValidationError::ReservedSpecModuleName { .. }))
        .collect()
}

#[test]
fn every_recognized_reserved_disclosure_is_admitted() {
    // The allowlist must not lock out the compiler that actually mints these.
    // All three are built by `SpecModule::new` (= design-only + embedded) and
    // populate `invariants` only, which is exactly the admitted shape.
    for name in RESERVED_TRUST_INTERNAL_SPEC_MODULES {
        let module = with_spec(disclosure(name));
        assert_eq!(validate_module(&module), Vec::new(), "{name}");
    }
}

#[test]
fn a_minted_trust_internal_name_is_refused() {
    // The anti-impersonation core: a plausible-looking but unrecognized name in
    // the reserved namespace. Nothing in a `Module` authenticates its producer,
    // so a closed occupant set is the only defense the format can mount.
    let module = with_spec(disclosure("@trust-internal::borrow-check-disclosure-v1"));
    let errors = reserved_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].to_string().contains("closed set"), "{errors:?}");
}

#[test]
fn a_case_variant_of_the_reserved_prefix_is_refused() {
    let module = with_spec(disclosure("@TRUST-INTERNAL::contract-disclosure-v1"));
    assert_eq!(reserved_errors(&module).len(), 1);
}

#[test]
fn a_padded_spelling_of_a_reserved_name_is_refused() {
    // Namespace membership trims; occupant membership is byte-exact. A padded
    // name is not the reserved name, and admitting it would let two distinct
    // strings both read as the same disclosure.
    let module = with_spec(disclosure(" @trust-internal::contract-disclosure-v1"));
    assert_eq!(reserved_errors(&module).len(), 1);
}

#[test]
fn a_reserved_disclosure_may_not_carry_executable_or_certifying_authority() {
    // Shadowing with teeth: the right name, but fields that make CLAIMS. A
    // disclosure is descriptive rows and nothing else.
    let mut spec = disclosure(RESERVED_TRUST_INTERNAL_SPEC_MODULES[1]);
    spec.vars.push(SpecVar::new("x", "Int"));
    spec.actions.push("Step".to_string());
    let module = with_spec(spec);
    let errors = reserved_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    let rendered = errors[0].to_string();
    assert!(rendered.contains("vars"), "{rendered}");
    assert!(rendered.contains("actions"), "{rendered}");
}

#[test]
fn a_reserved_disclosure_may_not_declare_linked_enforcement() {
    let mut spec = disclosure(RESERVED_TRUST_INTERNAL_SPEC_MODULES[0]);
    spec.enforcement = SpecEnforcementMode::Linked;
    let module = with_spec(spec);
    let errors = reserved_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].to_string().contains("linked"), "{errors:?}");
}

#[test]
fn a_reserved_disclosure_may_not_claim_an_external_origin() {
    let mut spec = disclosure(RESERVED_TRUST_INTERNAL_SPEC_MODULES[2]);
    spec.origin = SpecOrigin::External("attacker.tla".to_string());
    let module = with_spec(spec);
    let errors = reserved_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].to_string().contains("attacker.tla"), "{errors:?}");
}

#[test]
fn an_ordinary_spec_module_name_is_untouched() {
    let module = with_spec(disclosure("MyProtocol"));
    assert_eq!(validate_module(&module), Vec::new());
    // Including one that merely mentions the marker without claiming it.
    let module = with_spec(disclosure("not-@trust-internal::anything"));
    assert_eq!(validate_module(&module), Vec::new());
}

// ===========================================================================
// (c) the `Ty::Error` hole
// ===========================================================================

/// Wrap `inst` in a one-function module and return the validator's verdict.
fn module_with_inst(inst: Inst) -> Module {
    let mut module = Module::new("m");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut block = Block::new(b(0));
    block.body.push(InstrNode::new(inst));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Did validation report `Ty::Error` at some position?
///
/// Deliberately loose about the surrounding errors: a `Ty::Error` operand also
/// trips arity/type checks, and those are not what this gap is about.
fn reports_error_ty(module: &Module) -> bool {
    validate_module(module).iter().any(|e| {
        matches!(
            e,
            ValidationError::ConstTypeMismatch { actual, .. } if actual == "error"
        )
    })
}

#[test]
fn error_ty_is_rejected_in_every_inline_instruction_position() {
    // The measured hole: before this, `validate_module_error_types` walked the
    // module type table, func types, globals, struct/record/enum fields,
    // closure captures, block params — and, of the ~30 instruction fields that
    // spell a `Ty` inline, exactly ONE (`Inst::Const`). Everything below
    // therefore passed validation and reached `binary::write_ty`, whose
    // `Ty::Error` arm is a `panic!`.
    let e = || Ty::Error;
    let cases: Vec<(&str, Inst)> = vec![
        (
            "BinOp.ty",
            Inst::BinOp {
                op: BinOp::Add,
                ty: e(),
                lhs: v(0),
                rhs: v(1),
            },
        ),
        (
            "ICmp.ty",
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: e(),
                lhs: v(0),
                rhs: v(1),
            },
        ),
        (
            "Cast.src_ty",
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: e(),
                dst_ty: Ty::I32,
                operand: v(0),
            },
        ),
        (
            "Cast.dst_ty",
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I32,
                dst_ty: e(),
                operand: v(0),
            },
        ),
        (
            "Load.ty",
            Inst::Load {
                ty: e(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
        ),
        (
            "Store.ty",
            Inst::Store {
                ty: e(),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
        ),
        (
            "Alloca.ty",
            Inst::Alloca {
                ty: e(),
                count: None,
                align: None,
            },
        ),
        (
            "HeapAlloc.ty",
            Inst::HeapAlloc {
                ty: e(),
                count: None,
                align: None,
                origin: AllocOrigin::RustHeap,
            },
        ),
        (
            "GEP.pointee_ty",
            Inst::GEP {
                pointee_ty: e(),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            },
        ),
        (
            "PtrData.ptr_ty",
            Inst::PtrData {
                ptr_ty: e(),
                ptr: v(0),
            },
        ),
        (
            "PtrMetadata.metadata_ty",
            Inst::PtrMetadata {
                ptr_ty: Ty::Ptr,
                metadata_ty: e(),
                ptr: v(0),
            },
        ),
        (
            "PtrFromParts.ptr_ty",
            Inst::PtrFromParts {
                ptr_ty: e(),
                metadata_ty: Ty::Usize,
                data: v(0),
                metadata: v(1),
            },
        ),
        (
            "AtomicLoad.ty",
            Inst::AtomicLoad {
                ty: e(),
                ptr: v(0),
                ordering: Ordering::SeqCst,
            },
        ),
        (
            "AtomicRMW.ty",
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: e(),
                ptr: v(0),
                value: v(1),
                ordering: Ordering::SeqCst,
            },
        ),
        (
            "ExtractField.ty",
            Inst::ExtractField {
                ty: e(),
                aggregate: v(0),
                field: 0,
            },
        ),
        (
            "InsertElement.ty",
            Inst::InsertElement {
                ty: e(),
                array: v(0),
                index: v(1),
                value: v(2),
            },
        ),
        ("Undef.ty", Inst::Undef { ty: e() }),
        (
            "Copy.ty",
            Inst::Copy {
                ty: e(),
                operand: v(0),
            },
        ),
        (
            "Select.ty",
            Inst::Select {
                ty: e(),
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            },
        ),
        (
            "OpenFrame.def.slots[].ty",
            Inst::OpenFrame {
                def: BindingFrameDef::new(
                    BindingFrameId::new(0),
                    "frame",
                    vec![BindingSlot::new("i", e())],
                ),
            },
        ),
        (
            "LoadSlot.ty",
            Inst::LoadSlot {
                frame: v(0),
                slot: 0,
                ty: e(),
            },
        ),
        (
            "DialectOp.result_tys",
            Inst::DialectOp(Box::new({
                let mut op = DialectInst::new("verif", "probe");
                op.result_tys.push(e());
                op
            })),
        ),
        (
            "DialectOp.attrs[AttrValue::Ty]",
            Inst::DialectOp(Box::new({
                let mut op = DialectInst::new("verif", "probe");
                op.attrs.push(AttrEntry {
                    name: "elem_ty".to_string(),
                    value: AttrValue::Ty(e()),
                });
                op
            })),
        ),
        // Nested, not bare: the recursion through inline type structure must
        // reach it too.
        (
            "Alloca.ty nested under Ref/Tuple/Vector",
            Inst::Alloca {
                ty: Ty::Ref(Box::new(Ty::Tuple(vec![
                    Ty::I32,
                    Ty::Vector(Box::new(e()), 4),
                ]))),
                count: None,
                align: None,
            },
        ),
    ];

    let mut missed = Vec::new();
    for (label, inst) in cases {
        if !reports_error_ty(&module_with_inst(inst)) {
            missed.push(label);
        }
    }
    assert!(
        missed.is_empty(),
        "Ty::Error reached the writer unreported at: {missed:?}"
    );
}

#[test]
fn error_ty_in_a_const_is_still_rejected() {
    // The one position that was already covered. Kept so the rewrite of the
    // walk cannot silently drop it.
    assert!(reports_error_ty(&module_with_inst(Inst::Const {
        ty: Ty::Error,
        value: trust_ir::Constant::Int(0),
    })));
}

#[test]
fn error_ty_diagnostics_name_the_instruction_that_carries_it() {
    // A whole-module "somewhere there is an error type" verdict is not
    // actionable on a real module. The location must name function, block,
    // instruction index and opcode.
    let module = module_with_inst(Inst::Alloca {
        ty: Ty::Error,
        count: None,
        align: None,
    });
    let rendered: Vec<String> = validate_module(&module)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        rendered
            .iter()
            .any(|r| r.contains("function 'f'") && r.contains("bb0") && r.contains("alloca")),
        "{rendered:?}"
    );
}

#[test]
fn a_module_free_of_error_types_is_untouched() {
    // The other half of a fail-closed check: it must not fire on well-formed
    // input. Exercises the same instruction positions with real types.
    let mut module = Module::new("m");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut block = Block::new(b(0));
    for inst in [
        Inst::GlobalAddr {
            global: GlobalId::new(0),
        },
        Inst::Undef { ty: Ty::I32 },
        Inst::DialectOp(Box::new({
            let mut op = DialectInst::new("verif", "probe");
            op.attrs.push(AttrEntry {
                name: "elem_ty".to_string(),
                value: AttrValue::Ty(Ty::I32),
            });
            op
        })),
    ] {
        block.body.push(InstrNode::new(inst));
    }
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
    func.blocks.push(block);
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    assert!(!reports_error_ty(&module));
}

// ===========================================================================
// (d) WS1.5 — the codegen license is bound to evidence (F-006), the composed
//     policy/authority/registry-taking entry points (F-009), and disclosure
//     keys (F-017)
// ===========================================================================
//
// Tests named `b<N>_gap_*` are the in-repo ports of the two-language proof
// program's GAP ratchet rows of the same id (dots spelled `_`); each asserts
// the row's FLIPPED (now-refused / now-possible) state.

use std::collections::BTreeSet;

use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofLineageId,
    ProofLineageManifest, ProofObligation, ProofStatus, ProofTransform, ProofTransformStage,
    RejectingModuleProofAuthority,
};
use trust_ir::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
use trust_ir::value::ProofId;
use trust_ir::{
    Constant, Endianness, Global, Producer, StructPassingPolicy, TargetInfo, Visibility,
};
use trust_ir_build::{
    CodegenAdmission, EVIDENCE_BOUND_GATE_AUTHORITIES, GateEvidenceRule, HandleEntryPoint,
    HandleRegistry, HandleRuntimePin, ModuleBuilder, ModuleSet, PinnedTy, TRUSTED_HANDLE_RUNTIMES,
    UnlicensedBodyPolicy, certify_identity_lineage_rung, codegen_license_errors_with,
    gate_evidence_rule, validate_linked_module, validate_linked_module_with,
    validate_module_for_codegen_with, validate_module_report,
    validate_module_report_with_authority_and_registry, validate_module_with_authority,
    validate_module_with_bundle, validate_module_with_bundle_with_authority,
};

const CLEAN_KERNEL_TV: &str = "clean-kernel-tv";
const DIRECT_LANE: &str = "trust-direct-lane-structural";
const CLEAN_ORIGIN: &str = "@trust-internal::clean-origin-disclosure-v1";

fn gated(authority: &str) -> BodyGate {
    BodyGate::Gated {
        authority: authority.to_string(),
        evidence: None,
    }
}

/// The Fragment-2 subject: `[Clean] addmul(a, b) = a*b + 7` at `U64`, licensed
/// `Gated{"clean-kernel-tv"}`, plus (when `with_helper`) a second Clean body
/// `helper(a, b) = a*b + a` under the same license. Nothing is certified yet.
fn addmul_module(with_helper: bool) -> Module {
    let mut mb = ModuleBuilder::new("ws1_5_addmul");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    {
        let mut f = mb.function("addmul", sig);
        f.set_body_gate(gated(CLEAN_KERNEL_TV));
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let bb = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let p = f.mul(Ty::U64, a, bb);
        let k = f.iconst(Ty::U64, 7);
        let r = f.add(Ty::U64, p, k);
        f.ret(vec![r]);
        f.build();
    }
    if with_helper {
        let mut f = mb.function("helper", sig);
        f.set_body_gate(gated(CLEAN_KERNEL_TV));
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let bb = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let p = f.mul(Ty::U64, a, bb);
        let r = f.add(Ty::U64, p, a);
        f.ret(vec![r]);
        f.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Mint a kernel-checkable `clean_backend_tv` row for function `index` with
/// the PUBLIC minter (obligation id = current obligation count).
fn certify(module: &mut Module, index: usize) -> u32 {
    let id = u32::try_from(module.proof_obligations.len()).unwrap();
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        module,
        ProofLineageId::new(id),
        ProofId::new(id),
        ProofTransform::new(ProofTransformStage::Frontend, "identity", "ws1-5", "1.0.0"),
        module.functions[index].id,
    )
    .expect("fixture function is in the backend-TV fragment");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    id
}

/// The positive fixture: `addmul` with its Certified TV row.
fn certified_addmul() -> Module {
    let mut module = addmul_module(false);
    certify(&mut module, 0);
    module
}

/// The license-partition refusals only (the three pre-existing variants plus
/// the three WS1.5 ones).
fn license_errors(errors: &[ValidationError]) -> Vec<ValidationError> {
    errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                ValidationError::UngatedBodyForCodegen { .. }
                    | ValidationError::UnlicensedBodyForCodegen { .. }
                    | ValidationError::GatedWithoutEvidence { .. }
                    | ValidationError::GatedFunctionRefuted { .. }
                    | ValidationError::UnrecognizedGateAuthority { .. }
            )
        })
        .cloned()
        .collect()
}

/// `Some(detail)` iff `errors` is exactly one `GatedWithoutEvidence` for
/// function 0 under `clean-kernel-tv`.
fn sole_without_evidence(errors: &[ValidationError]) -> Option<&str> {
    match errors {
        [
            ValidationError::GatedWithoutEvidence {
                function: 0,
                authority,
                detail,
            },
        ] if authority == CLEAN_KERNEL_TV => Some(detail.as_str()),
        _ => None,
    }
}

#[test]
fn ws1_5_the_evidence_table_binds_exactly_clean_kernel_tv() {
    assert_eq!(
        EVIDENCE_BOUND_GATE_AUTHORITIES,
        &[(
            CLEAN_KERNEL_TV,
            GateEvidenceRule::KernelTranslationValidation
        )]
    );
    assert_eq!(
        gate_evidence_rule(CLEAN_KERNEL_TV),
        Some(GateEvidenceRule::KernelTranslationValidation)
    );
    // Byte-exact: a case or padding variant is a DIFFERENT, unbound authority.
    for other in [
        "CLEAN-KERNEL-TV",
        " clean-kernel-tv",
        "clean-kernel-tv ",
        DIRECT_LANE,
    ] {
        assert_eq!(gate_evidence_rule(other), None, "{other:?}");
    }
}

#[test]
fn ws1_5_positive_certified_addmul_is_admitted_for_codegen() {
    let module = certified_addmul();
    assert_eq!(module.proof_obligations.len(), 1);
    assert_eq!(
        module.proof_obligations[0].kind,
        ObligationKind::TranslationValidation
    );
    assert_eq!(module.proof_obligations[0].status, ProofStatus::Certified);
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    assert_eq!(codegen_license_errors(&module), Vec::new());
    // The report-reusing form agrees and needs no second kernel pass.
    let report = validate_module_report(&module);
    assert_eq!(codegen_license_errors_with(&report), Vec::new());
    // And so does the composed lane under a replay capability.
    let admission = CodegenAdmission::pinned().with_authority(&RejectingModuleProofAuthority);
    assert_eq!(
        validate_module_for_codegen_with(&module, &admission),
        Vec::new()
    );
}

#[test]
fn ws1_5_negative_tv_row_removed() {
    let mut module = certified_addmul();
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    let errors = validate_module_for_codegen(&module);
    let detail = sole_without_evidence(&errors).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(
        detail.contains("no TranslationValidation obligation"),
        "{detail}"
    );
}

#[test]
fn ws1_5_negative_tv_row_made_failed() {
    let mut module = certified_addmul();
    module.proof_obligations[0].status = ProofStatus::Failed;
    let errors = validate_module_for_codegen(&module);
    assert_eq!(
        license_errors(&errors),
        vec![ValidationError::GatedFunctionRefuted {
            function: 0,
            obligation: 0,
        }],
        "{errors:?}"
    );
}

#[test]
fn ws1_5_negative_tv_cert_belongs_to_another_function() {
    // `helper` carries the only Certified TV row; `addmul` wears the same
    // license with nothing behind it.
    let mut module = addmul_module(true);
    certify(&mut module, 1);
    assert_eq!(validate_module(&module), Vec::new());
    let errors = validate_module_for_codegen(&module);
    let detail = sole_without_evidence(&errors).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(
        detail.contains("no TranslationValidation obligation"),
        "{detail}"
    );
    // Mutation control: certifying `addmul` too admits the module.
    certify(&mut module, 0);
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
}

#[test]
fn ws1_5_negative_body_edited_after_mint() {
    // +7 -> +8 after the certificate was minted: `body_gate` is untouched,
    // but the recheck re-derives the emitted side from the CURRENT body.
    let mut module = certified_addmul();
    let hit = module.functions[0].blocks[0]
        .body
        .iter_mut()
        .find_map(|node| match &mut node.inst {
            Inst::Const { value, .. } if *value == Constant::Int(7) => Some(value),
            _ => None,
        })
        .expect("fixture carries the +7 constant");
    *hit = Constant::Int(8);
    let errors = validate_module_for_codegen(&module);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, .. }
        )),
        "{errors:?}"
    );
    let license = license_errors(&errors);
    let detail = sole_without_evidence(&license).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(detail.contains("not kernel-replayed"), "{detail}");
}

/// The c05 reproduction baseline: `[Clean] clean_f() -> u64 { load @G + 2 }`,
/// `Gated{"clean-kernel-tv"}`, ZERO obligations and ZERO certificates.
fn c05_baseline() -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(
        "c05_lic",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    mb.add_global(Global {
        name: "G".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(40)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut f = mb.function("clean_f", sig);
    f.set_producer(Producer::Clean);
    f.set_body_gate(gated(CLEAN_KERNEL_TV));
    f.set_display_path("Demo.cleanF");
    let e = f.create_block();
    f.switch_to_block(e);
    let p = f.global_addr(GlobalId::new(0));
    let x = f.load(Ty::U64, p);
    let two = f.uconst(Ty::U64, 2);
    let r = f.add(Ty::U64, x, two);
    f.ret(vec![r]);
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn ws1_5_negative_c05_baseline_with_zero_obligations() {
    let module = c05_baseline();
    assert!(module.proof_obligations.is_empty());
    assert_eq!(validate_module(&module), Vec::new());
    let errors = validate_module_for_codegen(&module);
    assert!(sole_without_evidence(&errors).is_some(), "{errors:?}");
}

#[test]
fn ws1_5_negative_second_pending_tv_row_is_ambiguous() {
    let mut module = certified_addmul();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "a second, still-pending translation validation of the same body",
        )
        .with_function(module.functions[0].id),
    );
    assert_eq!(validate_module(&module), Vec::new());
    let errors = validate_module_for_codegen(&module);
    let detail = sole_without_evidence(&errors).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(
        detail.starts_with("ambiguous: 2 TranslationValidation rows"),
        "{detail}"
    );
}

#[test]
fn ws1_5_revocation_applies_to_every_gated_body() {
    // Rule 3 is authority-independent: a direct-lane body with a Failed
    // Postcondition loses its license too, and a Failed Precondition likewise.
    for kind in [ObligationKind::Postcondition, ObligationKind::Precondition] {
        let mut module = bodies(&["f"]);
        module.functions[0].body_gate = Some(gated(DIRECT_LANE));
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                kind.clone(),
                ProofStatus::Failed,
                "refuted",
            )
            .with_function(FuncId::new(0))
            .with_formula(ProofFormula::smtlib2("(= 1 2)", "Bool")),
        );
        let errors = validate_module_for_codegen(&module);
        assert_eq!(
            license_errors(&errors),
            vec![ValidationError::GatedFunctionRefuted {
                function: 0,
                obligation: 0,
            }],
            "{kind:?}: {errors:?}"
        );
    }
    // Control: a Failed row of a kind that states no claim about the body's
    // meaning (PanicFreedom) is not a license refutation.
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(gated(DIRECT_LANE));
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Failed,
            "not a refutation of the license",
        )
        .with_function(FuncId::new(0)),
    );
    assert!(license_errors(&validate_module_for_codegen(&module)).is_empty());
}

#[test]
fn ws1_5_mutation_control_direct_lane_is_a_consumer_decision() {
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(gated(DIRECT_LANE));
    // Policy-free entry: no evidence rule for this authority, so it proceeds.
    assert_eq!(validate_module_for_codegen(&module), Vec::new());
    // A consumer recognizing only the kernel-TV authority refuses it by name.
    let recognized = BTreeSet::from([CLEAN_KERNEL_TV.to_string()]);
    let admission = CodegenAdmission::pinned().with_recognized(&recognized);
    assert_eq!(
        validate_module_for_codegen_with(&module, &admission),
        vec![ValidationError::UnrecognizedGateAuthority {
            function: 0,
            authority: DIRECT_LANE.to_string(),
        }]
    );
    // DECIDE 1: the direct lane is admitted only when the consumer NAMES it.
    let recognized = BTreeSet::from([CLEAN_KERNEL_TV.to_string(), DIRECT_LANE.to_string()]);
    let admission = CodegenAdmission::pinned().with_recognized(&recognized);
    assert_eq!(
        validate_module_for_codegen_with(&module, &admission),
        Vec::new()
    );
}

#[test]
fn ws1_5_recognition_never_relaxes_the_evidence_table() {
    // Recognizing `clean-kernel-tv` does not admit it without its evidence.
    let module = c05_baseline();
    let recognized = BTreeSet::from([CLEAN_KERNEL_TV.to_string()]);
    let admission = CodegenAdmission::pinned().with_recognized(&recognized);
    let errors = validate_module_for_codegen_with(&module, &admission);
    assert!(sole_without_evidence(&errors).is_some(), "{errors:?}");
    // And the positive fixture is admitted under the same recognized set.
    assert_eq!(
        validate_module_for_codegen_with(&certified_addmul(), &admission),
        Vec::new()
    );
}

#[test]
fn ws1_5_unlicensed_policy_permits_none_and_never_ungated() {
    let mut module = bodies(&["legacy", "ungated"]);
    module.functions[0].body_gate = None;
    module.functions[1].body_gate = Some(BodyGate::Ungated);
    let refuse = validate_module_for_codegen_with(&module, &CodegenAdmission::pinned());
    assert_eq!(refuse, validate_module_for_codegen(&module));
    assert_eq!(refuse.len(), 2, "{refuse:?}");
    let permit = CodegenAdmission::pinned().with_unlicensed(UnlicensedBodyPolicy::Permit);
    assert_eq!(
        validate_module_for_codegen_with(&module, &permit),
        vec![ValidationError::UngatedBodyForCodegen {
            function: 1,
            name: "ungated".to_string(),
        }]
    );
}

// ---- handle registry through the codegen / authority / linked lanes -------

/// The pinned `trust_bignum::Nat` row with one extra, test-only entry point
/// `gcd : (Nat, Nat) -> Nat` — a caller-owned registry extension. (`mul`
/// joined the shipped row in WS3.2, so the extension must be a role the
/// table does NOT pin: `from_pins` refuses a duplicate.)
fn extended_nat_pin(gcd_returns: &'static [PinnedTy]) -> HandleRuntimePin {
    let nat = TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins trust_bignum::Nat");
    let mut entries = nat.entry_points.to_vec();
    entries.push(HandleEntryPoint {
        role: "gcd",
        symbol: "trust_bignum_nat_gcd",
        def_path: "trust_bignum::Nat::gcd",
        params: &[PinnedTy::Handle, PinnedTy::Handle],
        returns: gcd_returns,
    });
    HandleRuntimePin {
        entry_points: Box::leak(entries.into_boxed_slice()),
        ..nat.clone()
    }
}

/// A licensed Rust body `square_is_zero(x: u64) -> bool` that builds a Nat,
/// folds it through the extension's `gcd` (gcd(h, h) — the shape is what
/// matters, not the arithmetic), tests it and releases it — declaring
/// `from_u64`, `is_zero`, `gcd` and `drop` from `pin`.
fn nat_square_module(pin: &HandleRuntimePin) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(
        "ws1_5_nat",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let decls = mb
        .declare_handle_runtime_roles(pin, &["from_u64", "is_zero", "gcd", "drop"])
        .expect("declarations");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let mut f = mb.function("square_is_zero", sig);
    f.set_producer(Producer::TRust);
    f.set_body_gate(gated(DIRECT_LANE));
    let e = f.create_block();
    let x = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let h = f.call(decls.entry("from_u64").unwrap(), vec![x]);
    let sq = f.call(decls.entry("gcd").unwrap(), vec![h, h]);
    let z = f.call(decls.entry("is_zero").unwrap(), vec![sq]);
    f.call_void(decls.entry("drop").unwrap(), vec![sq]);
    f.call_void(decls.entry("drop").unwrap(), vec![h]);
    f.ret(vec![z]);
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn sole_foreign_gcd(errors: &[ValidationError]) -> bool {
    matches!(
        errors,
        [ValidationError::HandleForeignDeclaration { name, .. }] if name == "trust_bignum_nat_gcd"
    )
}

#[test]
fn b5_gap_no_codegen_or_authority_entry_point_takes_a_handle_registry() {
    let pin = extended_nat_pin(&[PinnedTy::Handle]);
    let extended = HandleRegistry::from_pins(std::slice::from_ref(&pin)).expect("well-formed");
    let module = nat_square_module(&pin);

    // Negative twin: the pinned table refuses the extension's symbol on every
    // lane, exactly once.
    assert!(
        sole_foreign_gcd(&validate_module(&module)),
        "{:?}",
        validate_module(&module)
    );
    assert!(sole_foreign_gcd(&validate_module_for_codegen(&module)));
    assert!(sole_foreign_gcd(&validate_module_with_authority(
        &module,
        &RejectingModuleProofAuthority
    )));
    let resolver = ModuleSet::new(std::iter::empty());
    assert!(sole_foreign_gcd(
        validate_linked_module(&module, &resolver, &RejectingModuleProofAuthority).errors()
    ));

    // The flip: every composed lane now TAKES the registry.
    let admission = CodegenAdmission::pinned().with_handle_registry(&extended);
    assert_eq!(
        validate_module_for_codegen_with(&module, &admission),
        Vec::new()
    );
    let admission = admission.with_authority(&RejectingModuleProofAuthority);
    assert_eq!(
        validate_module_for_codegen_with(&module, &admission),
        Vec::new()
    );
    assert!(
        validate_module_report_with_authority_and_registry(
            &module,
            &RejectingModuleProofAuthority,
            &extended
        )
        .is_ok()
    );
    assert!(
        validate_linked_module_with(
            &module,
            &resolver,
            &RejectingModuleProofAuthority,
            &extended
        )
        .errors()
        .is_empty()
    );
}

#[test]
fn ws1_5_mutation_control_the_registry_is_threaded_not_ignored() {
    // An extension whose `gcd` is pinned to return a u64: the module's
    // Nat-returning declaration is now a signature forgery on every lane that
    // takes the registry — so the registry is actually consulted.
    let honest = extended_nat_pin(&[PinnedTy::Handle]);
    let skewed = extended_nat_pin(&[PinnedTy::Scalar(Ty::U64)]);
    let skewed_registry = HandleRegistry::from_pins(std::slice::from_ref(&skewed)).unwrap();
    let module = nat_square_module(&honest);
    let mismatch = |errors: &[ValidationError]| {
        errors.iter().any(|e| {
            matches!(
                e,
                ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                    if symbol == "trust_bignum_nat_gcd"
            )
        })
    };
    let admission = CodegenAdmission::pinned().with_handle_registry(&skewed_registry);
    assert!(mismatch(&validate_module_for_codegen_with(
        &module, &admission
    )));
    assert!(mismatch(
        validate_module_report_with_authority_and_registry(
            &module,
            &RejectingModuleProofAuthority,
            &skewed_registry
        )
        .errors()
    ));
    let resolver = ModuleSet::new(std::iter::empty());
    assert!(mismatch(
        validate_linked_module_with(
            &module,
            &resolver,
            &RejectingModuleProofAuthority,
            &skewed_registry
        )
        .errors()
    ));
}

// ---- authority through the codegen / bundle lanes --------------------------

/// A stand-in replay capability that re-establishes exactly one prover's
/// `Discharged` rows (the shape of a real one such as the ay adapter's).
struct StandIn;

impl trust_ir::proof::ModuleProofAuthority for StandIn {
    fn replays_authority(
        &self,
        _module: &Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        obligation.status == ProofStatus::Discharged && certificate.prover == "ws1-5-stand-in"
    }
}

#[test]
fn b2_gap_no_authority_taking_codegen_or_bundle_entry_point() {
    let mut module = bodies(&["f"]);
    module.functions[0].body_gate = Some(gated(DIRECT_LANE));
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "discharged by a replayable prover",
        )
        .with_function(FuncId::new(0))
        .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool")),
    );
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "ws1-5-stand-in".to_string(),
        evidence: ProofEvidence::SmtProof(vec![1]),
        assurance: None,
    });
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        module.stable_digest(),
        module.clone(),
        ProofLineageManifest::default(),
    );
    bundle.requests = Vec::new();
    let discharged_without = vec![ValidationError::DischargedWithoutCertificate { obligation: 0 }];

    // The structural tier refuses the row on both composed entry points...
    assert_eq!(validate_module_for_codegen(&module), discharged_without);
    assert_eq!(
        validate_module_with_bundle(&module, &bundle),
        discharged_without
    );
    // ...and the flip: each now has an authority-taking sibling.
    assert_eq!(
        validate_module_with_authority(&module, &StandIn),
        Vec::new()
    );
    let admission = CodegenAdmission::pinned().with_authority(&StandIn);
    assert_eq!(
        validate_module_for_codegen_with(&module, &admission),
        Vec::new()
    );
    assert_eq!(
        validate_module_with_bundle_with_authority(&module, &bundle, &StandIn),
        Vec::new()
    );
}

#[test]
fn b3_gap_kernel_tv_license_not_bound_to_certificate() {
    // The demoted, out-of-fragment Clean body `ult(a, b) = a < b` claiming
    // `Gated{"clean-kernel-tv"}` with NO TranslationValidation obligation.
    let mut mb = ModuleBuilder::new("b3_demoted");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::Bool]);
    let mut f = mb.function("ult", sig);
    f.set_producer(Producer::Clean);
    f.set_body_gate(gated(CLEAN_KERNEL_TV));
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let bb = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let c = f.icmp(ICmpOp::Ult, Ty::U64, a, bb);
    f.ret(vec![c]);
    f.build();
    let claimed = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(claimed.proof_obligations.is_empty());
    assert_eq!(validate_module(&claimed), Vec::new());
    let errors = validate_module_for_codegen(&claimed);
    assert!(sole_without_evidence(&errors).is_some(), "{errors:?}");

    // A Pending TV row ("not yet certified") is refused as well, by status.
    let mut pending = claimed.clone();
    pending.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "outside the clean_backend_tv fragment",
        )
        .with_function(FuncId::new(0)),
    );
    let errors = validate_module_for_codegen(&pending);
    let detail = sole_without_evidence(&errors).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(detail.contains("not `certified`"), "{detail}");
}

/// `b1.gap.gated_authority_unpinned`, RE-SCOPED rather than flipped: the
/// evidence-bound authority is now PASS (bound to its certificate), while an
/// unknown authority remains a consumer decision by ratified design — admitted
/// by the policy-free entry, refused by a consumer that names its set.
#[test]
fn b1_gap_gated_authority_unpinned() {
    // PASS half: `clean-kernel-tv` is no longer free text.
    let mut forged = bodies(&["f"]);
    forged.functions[0].body_gate = Some(gated(CLEAN_KERNEL_TV));
    assert!(sole_without_evidence(&validate_module_for_codegen(&forged)).is_some());

    // By-design half: unknown authorities, including look-alikes of the
    // bound one, are the consumer's decision.
    let recognized = BTreeSet::from([CLEAN_KERNEL_TV.to_string()]);
    let admission = CodegenAdmission::pinned().with_recognized(&recognized);
    for authority in [
        "attacker-says-ok",
        "CLEAN-KERNEL-TV",
        " clean-kernel-tv",
        "none",
        "ungated",
        "x",
    ] {
        let mut module = bodies(&["f"]);
        module.functions[0].body_gate = Some(gated(authority));
        assert_eq!(
            validate_module_for_codegen(&module),
            Vec::new(),
            "{authority:?}"
        );
        assert_eq!(
            validate_module_for_codegen_with(&module, &admission),
            vec![ValidationError::UnrecognizedGateAuthority {
                function: 0,
                authority: authority.to_string(),
            }],
            "{authority:?}"
        );
    }
}

// ---- disclosure keys (F-017) -----------------------------------------------

fn clean_origin(rows: &[(&str, &str)]) -> SpecModule {
    let mut spec = SpecModule::new(CLEAN_ORIGIN);
    for (key, row) in rows {
        spec.invariants.push(SpecInvariant::new(*key, *row));
    }
    spec
}

/// A row shaped exactly as `~/trust` `trust-thir-lower` `clean_origin_join.rs`
/// writes it for an emitted gate-tier body.
const HONEST_ROW: &str = r#"{"schema":"trust.clean-origin-disclosure.v1","def_path":"Demo.cleanF","clean_name":"clean_f","shape":"leaf","tier":"gate","body_gate":"carrier-faithful","mir_gate":"kernel Faithful earned for the emitted MIR body at the finalize seam"}"#;

#[test]
fn b1_gap_disclosure_rows_unbound_to_module() {
    // Honest: `fn:0` names the one bodied function, plus the other key
    // families the minter writes (which need not name a body here).
    let mut honest = c05_baseline();
    honest.spec_modules.push(clean_origin(&[
        ("fn:0", HONEST_ROW),
        (
            "skipped:3",
            r#"{"schema":"trust.clean-origin-disclosure.v1"}"#,
        ),
        (
            "general:Demo.helper",
            r#"{"schema":"trust.clean-origin-disclosure.v1"}"#,
        ),
    ]));
    assert_eq!(validate_module(&honest), Vec::new());

    // The flip (key half): a ghost key is refused by name.
    let mut ghost = c05_baseline();
    ghost
        .spec_modules
        .push(clean_origin(&[("fn:999", HONEST_ROW)]));
    let errors = reserved_errors(&ghost);
    assert_eq!(
        errors,
        vec![ValidationError::ReservedSpecModuleName {
            name: CLEAN_ORIGIN.to_string(),
            detail: "disclosure row fn:999 names no bodied function".to_string(),
        }]
    );
    assert_eq!(validate_module(&ghost), errors);
}

#[test]
fn ws1_5_disclosure_keys_must_parse_and_name_a_body() {
    for key in [
        "fn:",
        "fn:x",
        "fn:+0",
        "fn:-0",
        "fn:00",
        "fn:0 ",
        "fn:4294967296",
    ] {
        let mut module = c05_baseline();
        module.spec_modules.push(clean_origin(&[(key, HONEST_ROW)]));
        let errors = reserved_errors(&module);
        assert_eq!(errors.len(), 1, "{key:?}: {errors:?}");
        assert!(
            errors[0].to_string().contains("does not parse"),
            "{key:?}: {errors:?}"
        );
    }
    // A key naming a body-less declaration is refused too.
    let mut module = Module::new("m");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut import = Function::new(FuncId::new(0), "imported", ft, b(0));
    import.linkage = Linkage::External;
    import.calling_conv = CallingConv::Rust;
    module
        .try_add_function(import)
        .expect("Module::try_add_function: test fixture");
    module
        .spec_modules
        .push(clean_origin(&[("fn:0", HONEST_ROW)]));
    let errors = reserved_errors(&module);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].to_string().contains("body-less declaration"),
        "{errors:?}"
    );
    // The other reserved disclosures are not keyed by function.
    let mut module = c05_baseline();
    let mut spec = SpecModule::new(RESERVED_TRUST_INTERNAL_SPEC_MODULES[1]);
    spec.invariants.push(SpecInvariant::new("fn:999", "{}"));
    module.spec_modules.push(spec);
    assert_eq!(validate_module(&module), Vec::new());
}

// ---- adversarial review (WS1.5) ----------------------------------------------
//
// Shapes the first cut did not write. Each was observed ACCEPTED (or, for the
// controls, the direction was pinned) before the matching rule was tightened.

use trust_ir::proof::ObligationSite;

/// A `Failed` claim about `F` that names `F` only through its v34 `site` —
/// `function: None` — is still a claim about `F`'s body: `validate_module`
/// accepts that shape (the site rule only refuses a scope that CONTRADICTS
/// the site), so revocation must read the site's function as the scope.
#[test]
fn ws1_5_adversarial_site_only_failed_row_revokes_the_license() {
    for kind in [
        ObligationKind::TranslationValidation,
        ObligationKind::Postcondition,
        ObligationKind::Precondition,
    ] {
        let mut module = bodies(&["f"]);
        module.functions[0].body_gate = Some(gated(DIRECT_LANE));
        let mut row = ProofObligation::new(
            ProofId::new(0),
            kind.clone(),
            ProofStatus::Failed,
            "refuted at a site in f, with no function scope",
        )
        .with_site(ObligationSite::new(FuncId::new(0), b(0), 0));
        if kind != ObligationKind::TranslationValidation {
            row = row.with_formula(ProofFormula::smtlib2("(= 1 2)", "Bool"));
        }
        module.proof_obligations.push(row);
        assert_eq!(validate_module(&module), Vec::new(), "{kind:?}");
        assert_eq!(
            license_errors(&validate_module_for_codegen(&module)),
            vec![ValidationError::GatedFunctionRefuted {
                function: 0,
                obligation: 0,
            }],
            "{kind:?}"
        );
    }
}

/// A second TranslationValidation row about `addmul`, scoped only by its
/// site, is the same ambiguity as a second function-scoped row.
#[test]
fn ws1_5_adversarial_site_only_second_tv_row_is_ambiguous() {
    let mut module = certified_addmul();
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "a second translation validation, scoped only by site",
        )
        .with_site(ObligationSite::new(module.functions[0].id, b(0), 0)),
    );
    assert_eq!(validate_module(&module), Vec::new());
    let errors = validate_module_for_codegen(&module);
    let detail = sole_without_evidence(&errors).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(
        detail.starts_with("ambiguous: 2 TranslationValidation rows"),
        "{detail}"
    );
}

/// Control (legitimate module must not be refused): a refutation, and a
/// second TV row, about ANOTHER function — by scope or by site — never
/// touches this body's license.
#[test]
fn ws1_5_adversarial_rows_about_another_function_never_revoke() {
    let mut module = addmul_module(true);
    certify(&mut module, 0);
    // `helper` is gated by the direct lane so it needs no evidence itself.
    module.functions[1].body_gate = Some(gated(DIRECT_LANE));
    let helper = module.functions[1].id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Failed,
            "refutes helper, by scope",
        )
        .with_function(helper)
        .with_formula(ProofFormula::smtlib2("(= 1 2)", "Bool")),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(2),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "about helper, by site",
        )
        .with_site(ObligationSite::new(helper, b(0), 0)),
    );
    assert_eq!(validate_module(&module), Vec::new());
    assert_eq!(
        license_errors(&validate_module_for_codegen(&module)),
        vec![ValidationError::GatedFunctionRefuted {
            function: 1,
            obligation: 1,
        }]
    );
}

/// Two `fn:N` rows for ONE body make the key->row binding ambiguous: the
/// minter writes one row per emitted body, so a second row under the same key
/// is refused rather than letting either be read as THE disclosure.
#[test]
fn ws1_5_adversarial_duplicate_disclosure_key_is_refused() {
    let mut module = c05_baseline();
    module.spec_modules.push(clean_origin(&[
        ("fn:0", HONEST_ROW),
        (
            "fn:0",
            r#"{"schema":"trust.clean-origin-disclosure.v1","tier":"structural","body_gate":"ungated"}"#,
        ),
    ]));
    let errors = reserved_errors(&module);
    assert_eq!(
        errors,
        vec![ValidationError::ReservedSpecModuleName {
            name: CLEAN_ORIGIN.to_string(),
            detail: "disclosure row fn:0 appears more than once".to_string(),
        }],
        "{errors:?}"
    );
    // Control: one row per body is accepted.
    let mut module = addmul_module(true);
    module
        .spec_modules
        .push(clean_origin(&[("fn:0", HONEST_ROW), ("fn:1", HONEST_ROW)]));
    assert_eq!(reserved_errors(&module), Vec::new());
}

/// The WS3.1 composition seam: every `ValidationConfig` lane that runs the
/// codegen layers — single-module and the linked walk — enforces the
/// evidence rule, and reads its evidence from the kernel tier ITS OWN pass
/// replayed. A lane that consulted an empty set would wrongly refuse the
/// certified `addmul`; one that skipped the rule would admit the c05 body.
#[test]
fn ws1_5_adversarial_config_and_linked_codegen_lanes_bind_the_license() {
    use trust_ir_build::{
        ValidationConfig, validate_linked_module_with_config, validate_module_with_config,
    };
    let codegen = ValidationConfig::pinned().with_codegen(true);
    let resolver = ModuleSet::new(std::iter::empty());

    let certified = certified_addmul();
    assert!(
        validate_module_with_config(&certified, &codegen).is_ok(),
        "{:?}",
        validate_module_with_config(&certified, &codegen).errors()
    );
    let linked = validate_linked_module_with_config(&certified, &resolver, &codegen);
    assert!(linked.errors().is_empty(), "{:?}", linked.errors());
    // The admission lane built from the same config agrees.
    assert_eq!(
        validate_module_for_codegen_with(&certified, &CodegenAdmission::from_config(codegen)),
        Vec::new()
    );

    let forged = c05_baseline();
    let report = validate_module_with_config(&forged, &codegen);
    assert!(
        sole_without_evidence(report.errors()).is_some(),
        "{:?}",
        report.errors()
    );
    let linked = validate_linked_module_with_config(&forged, &resolver, &codegen);
    assert!(
        sole_without_evidence(linked.errors()).is_some(),
        "{:?}",
        linked.errors()
    );
    // Without codegen intent the config lane stays structural.
    assert!(validate_module_with_config(&forged, &ValidationConfig::pinned()).is_ok());
}

// ---- adversarial review, second pass (WS1.5) ---------------------------------
//
// Shapes neither earlier pass wrote. Each pins a direction the rule must hold.

/// A replay capability that vouches for EVERY row it is shown. It may lift a
/// `Discharged` row into the Discharged tier, but it is not the Clean kernel:
/// only a kernel re-check earns `Certified`, so a row the capability replayed
/// must never serve as `clean-kernel-tv` license evidence.
struct AcceptEverything;

impl trust_ir::proof::ModuleProofAuthority for AcceptEverything {
    fn replays_authority(
        &self,
        _module: &Module,
        _obligation: &ProofObligation,
        _certificate: &ProofCertificate,
    ) -> bool {
        true
    }
}

#[test]
fn ws1_5_adversarial_capability_replayed_discharged_tv_row_is_not_license_evidence() {
    let mut module = certified_addmul();
    module.proof_obligations[0].status = ProofStatus::Discharged;
    let admission = CodegenAdmission::pinned().with_authority(&AcceptEverything);
    let errors = validate_module_for_codegen_with(&module, &admission);
    let license = license_errors(&errors);
    let detail = sole_without_evidence(&license).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(detail.contains("not `certified`"), "{detail}");
    // The report-reusing layer agrees under the same capability.
    let report = trust_ir_build::validate_module_report_with_authority(&module, &AcceptEverything);
    let license = codegen_license_errors_with(&report);
    assert!(sole_without_evidence(&license).is_some(), "{license:?}");
}

/// Two honestly certified bodies whose certificates are SWAPPED (each
/// certificate now names the other body's row): every certificate still
/// cites the backend-TV anchor and a Certified TV row exists for each body,
/// but neither recheck re-derives against the body it now claims, so the
/// kernel tier empties and BOTH licenses fall.
#[test]
fn ws1_5_adversarial_swapped_certificates_lose_both_licenses() {
    let mut module = addmul_module(true);
    certify(&mut module, 0);
    certify(&mut module, 1);
    assert_eq!(validate_module_for_codegen(&module), Vec::new());

    let mut swapped = module.clone();
    let (first, second) = (
        swapped.proof_certificates[0].obligation,
        swapped.proof_certificates[1].obligation,
    );
    swapped.proof_certificates[0].obligation = second;
    swapped.proof_certificates[1].obligation = first;
    let license = license_errors(&validate_module_for_codegen(&swapped));
    for function in [0, 1] {
        assert!(
            license.iter().any(|e| matches!(
                e,
                ValidationError::GatedWithoutEvidence { function: f, authority, .. }
                    if *f == function && authority == CLEAN_KERNEL_TV
            )),
            "function {function}: {license:?}"
        );
    }

    // Retargeting the ROWS instead (each row now scoped to the other body)
    // is refused the same way: the scope is part of what the recheck binds.
    let mut rescoped = module.clone();
    let (f0, f1) = (
        rescoped.proof_obligations[0].function,
        rescoped.proof_obligations[1].function,
    );
    rescoped.proof_obligations[0].function = f1;
    rescoped.proof_obligations[1].function = f0;
    let license = license_errors(&validate_module_for_codegen(&rescoped));
    assert_eq!(license.len(), 2, "{license:?}");
    assert!(
        license
            .iter()
            .all(|e| matches!(e, ValidationError::GatedWithoutEvidence { .. })),
        "{license:?}"
    );
}

/// The duplicate-key rule is per disclosure, so a second copy of the
/// reserved disclosure carrying the same `fn:N` key must not be a way around
/// it: whichever check fires, the module is refused.
#[test]
fn ws1_5_adversarial_second_disclosure_module_cannot_launder_a_duplicate_key() {
    let mut module = c05_baseline();
    module
        .spec_modules
        .push(clean_origin(&[("fn:0", HONEST_ROW)]));
    module.spec_modules.push(clean_origin(&[(
        "fn:0",
        r#"{"schema":"trust.clean-origin-disclosure.v1","tier":"structural","body_gate":"ungated"}"#,
    )]));
    let errors = validate_module(&module);
    assert!(
        !errors.is_empty(),
        "two disclosures keyed fn:0 were accepted"
    );
}
