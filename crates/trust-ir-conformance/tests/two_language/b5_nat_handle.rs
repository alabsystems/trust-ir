//! b5 — the Lean `Nat` carrier: `Ty::Handle{name:"Nat", runtime:"trust_bignum::Nat"}` (wire v43).
//!
//! The design's end state (2026-08-27 §6.4, GOAL G2/G3): a Clean-producer `Nat -> Nat`
//! function, spelled ONLY through the validator-pinned `trust_bignum_nat_{from_u64,add,sub,
//! is_zero}` C entry points, called from a Rust-producer function, in one module.
//!
//! Ported (roadmap WS8.6) from the archived Part B battery
//! `reports/2026-09-17-two-language-proof-program/partb/tests/b5_nat_handle.rs`, measured there
//! at trust-ir 4efb21bc and re-measured at the port. Every row is checked against
//! `RATCHETS.tsv` (see `harness.rs`). `file:line` citations are relative to
//! `crates/` and date from 4efb21bc: re-locate them by name.
//! The CLI rows live in `crates/trust-ir-cli/tests/two_language_cli.rs`, over
//! `b5_fixtures.rs`. Since 454ed396 the pin table has a fifth, RELEASE entry point
//! (`trust_bignum_nat_drop`), and since WS3.2 (F-052) the row also carries the Clean
//! kernel's native `Nat` surface (nineteen roles), so `nat_program()`'s
//! `declare_handle_runtime` declares all of them and a staged, unpinned role is `gcd`.
//!
//! Source citations: TB = trust-ir-build/src, TI = trust-ir/src.

mod common;

use common::{
    Expect, Outcome, feature_check, feature_gap, feature_ratified, roundtrip_all, run_nullary,
    run_with_args,
};
use trust_ir::binary::{
    BinaryError, BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions,
    ProjectedModuleBinaryPlan,
};
use trust_ir::bridge::ConformanceSubset;
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::interpret::InterpretValue;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ProofFormula, RejectingModuleProofAuthority,
};
use trust_ir::shape::{TyLayoutKind, TyShape};
use trust_ir::ty::{EnumDef, EnumVariant};
use trust_ir::value::EnumId;
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FieldDef, FuncId, FuncTy, Function, FunctionSummary,
    Global, HandleTy, Inst, InstrNode, Linkage, Module, ModuleImport, Producer, StructDef,
    StructId, StructRepr, Ty, ValueId, Visibility,
};
use trust_ir_build::linked::ModuleSet;
use trust_ir_build::{
    CodegenAdmission, HandleDeclError, HandleEntryPoint, HandleRegistry, HandleRuntimePin,
    ModuleBuilder, PinnedHandleHost, PinnedTy, TRUSTED_HANDLE_RUNTIMES, ValidationError,
    validate_linked_module, validate_linked_module_with, validate_module,
    validate_module_for_codegen, validate_module_for_codegen_with,
    validate_module_report_with_authority_and_registry, validate_module_with_authority,
    validate_module_with_handle_registry,
};

/// Refusal counts measured at the port (a change of count is a change of the
/// gap's shape, so the rows pin them). WS3.7 split the archived five-refusal
/// memory row: the spilled local now validates, and the `&Nat` / `&mut Nat`
/// parameter pair (one `Load`, one `Store`) is what remains.
const HANDLE_BEHIND_REF_PARAM_REFUSALS: usize = 2;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

#[path = "b5_fixtures.rs"]
mod b5_fixtures;
#[allow(unused_imports)]
use b5_fixtures::*;

fn function_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut Function {
    module
        .functions
        .iter_mut()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
}

fn func_id(module: &Module, name: &str) -> FuncId {
    module
        .function_by_name(name)
        .unwrap_or_else(|| panic!("no function `{name}`"))
        .id
}

fn next_func_id(module: &Module) -> FuncId {
    FuncId::new(
        module
            .functions
            .iter()
            .map(|f| f.id.index())
            .max()
            .map_or(0, |m| m + 1),
    )
}

fn has<F: Fn(&ValidationError) -> bool>(errors: &[ValidationError], pred: F) -> bool {
    errors.iter().any(pred)
}

fn only<F: Fn(&ValidationError) -> bool>(errors: &[ValidationError], pred: F) -> bool {
    !errors.is_empty() && errors.iter().all(pred)
}

fn invalid_handle_use_naming(errors: &[ValidationError], inst: &str) -> bool {
    let needle =
        format!("`{inst}` cannot produce, consume or reinterpret an opaque runtime handle");
    has(
        errors,
        |e| matches!(e, ValidationError::InvalidHandleUse { detail, .. } if detail.contains(&needle)),
    )
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

/// Append a bodyless C `External` declaration (what `ModuleBuilder::declare_function` /
/// `declare_handle_runtime` produce) to an already-built module.
fn push_c_declaration(
    module: &mut Module,
    symbol: &str,
    display_path: Option<&str>,
    params: Vec<Ty>,
    returns: Vec<Ty>,
) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = next_func_id(module);
    let mut decl = Function::new(id, symbol, sig, BlockId::new(0));
    decl.calling_conv = CallingConv::C;
    decl.linkage = Linkage::External;
    decl.display_path = display_path.map(str::to_owned);
    assert!(decl.is_declaration());
    module
        .try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    id
}

// ===========================================================================
// PASS rows
// ===========================================================================

/// `Ty::Handle{name:"Nat",runtime:"trust_bignum::Nat"}` + `ModuleBuilder::declare_handle_runtime`.
fn b5_01_handle_type_and_pinned_declarations() {
    // --- the type itself -----------------------------------------------------
    let module = nat_program();
    let h = nat();
    let identity = h.handle_ty().cloned();
    let layout = module.ty_layout_shape(&h);
    let ptr_layout = module.ty_layout_shape(&Ty::Ptr);
    let one_word = matches!(
        (&layout, &ptr_layout),
        (Ok(l), Ok(p)) if l.size_bits == 64
            && l.size_bits == p.size_bits
            && l.align_bits == p.align_bits
            && l.kind == TyLayoutKind::Scalar(TyShape::Handle)
    );
    let ok = identity == Some(HandleTy::new("Nat", "trust_bignum::Nat"))
        && h.is_handle()
        && !h.is_pointer_like()
        && h != Ty::Ptr
        && one_word
        && nat_pin().handle_ty() == h
        && validate_module(&module).is_empty();
    assert!(feature_check(
        "b5.ty_handle.nat",
        ok,
        &format!(
            "display=`{h}` identity={identity:?} is_handle={} is_pointer_like={} eq_ptr={} layout={layout:?} \
             (TI/ty.rs:341 HandleTy, :871 Ty::handle; TI/shape.rs:994 one pointer word, :221 not pointer-like)",
            h.is_handle(),
            h.is_pointer_like(),
            h == Ty::Ptr
        ),
    ));

    // negative twin A: the pinned NAME at a foreign runtime, spelled ONLY in an unused
    // type-table row, is refused by identity (TB/validate.rs:15707).
    let mut evil = nat_program();
    evil.types.push(Ty::handle("Nat", "evil::Nat"));
    let errors = validate_module(&evil);
    assert!(feature_check(
        "b5.ty_handle.nat.twin_untrusted_runtime",
        only(&errors, |e| matches!(
            e,
            ValidationError::UntrustedHandleRuntime { name, runtime, .. }
                if name == "Nat" && runtime == "evil::Nat"
        )),
        &format!("handle<Nat, evil::Nat> => {errors:?}"),
    ));

    // negative twin B: the pinned RUNTIME under an unpinned name (`Int` has no row).
    let mut int = nat_program();
    int.add_func_type(FuncTy {
        params: vec![Ty::handle("Int", "trust_bignum::Nat")],
        returns: vec![],
        abi: None,
        is_vararg: false,
    })
    .expect("Module::add_func_type: test fixture");
    let errors = validate_module(&int);
    assert!(feature_check(
        "b5.ty_handle.nat.twin_unpinned_name",
        only(&errors, |e| matches!(
            e,
            ValidationError::UntrustedHandleRuntime { name, runtime, .. }
                if name == "Int" && runtime == "trust_bignum::Nat"
        )),
        &format!("handle<Int, trust_bignum::Nat> => {errors:?}"),
    ));

    // negative twin C: a lexically malformed identity is refused AS malformed.
    let mut bad = nat_program();
    bad.types
        .push(Ty::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::"))));
    let errors = validate_module(&bad);
    assert!(feature_check(
        "b5.ty_handle.nat.twin_malformed_identity",
        has(&errors, |e| matches!(
            e,
            ValidationError::InvalidHandleType { .. }
        )) && !has(&errors, |e| matches!(
            e,
            ValidationError::UntrustedHandleRuntime { .. }
        )),
        &format!("handle<Nat, `trust_bignum::`> => {errors:?}"),
    ));

    // --- ModuleBuilder::declare_handle_runtime ---------------------------------
    let mut mb = ModuleBuilder::new_with_target_info("b5_decls", target());
    let first = mb.declare_handle_runtime(nat_pin()).unwrap();
    let second = mb.declare_handle_runtime(nat_pin()).unwrap();
    let roles: Vec<_> = first.entries().map(|(role, _)| role).collect();
    let decl_module = mb.build().expect("ModuleBuilder::build: test fixture");
    let mut shape_ok = first == second
        && first.handle == nat()
        // The v1 five plus the Clean kernel's native `Nat` surface (WS3.2), in role order;
        // `gcd` is outside that surface and stays unpinned.
        && roles
            == [
                "add",
                "beq",
                "ble",
                "clone",
                "div",
                "drop",
                "fits_u64",
                "from_u64",
                "is_zero",
                "land",
                "lor",
                "mod",
                "mul",
                "pow",
                "shift_left",
                "shift_right",
                "sub",
                "to_u64",
                "xor",
            ]
        && first.entry("gcd").is_none()
        && decl_module.functions.len() == 19
        && validate_module(&decl_module).is_empty()
        && validate_module_for_codegen(&decl_module).is_empty();
    let mut rendered = Vec::new();
    for entry in nat_pin().entry_points {
        let decl = decl_module.function_by_name(entry.symbol).unwrap();
        shape_ok &= decl.is_declaration()
            && decl.linkage == Linkage::External
            && decl.calling_conv == CallingConv::C
            && decl.display_path.as_deref() == Some(entry.def_path)
            && decl_module.func_type(decl.ty) == Some(&nat_pin().func_ty(entry));
        let sig = decl_module.func_type(decl.ty).unwrap();
        rendered.push(format!(
            "{}:{}({})->({})",
            entry.role,
            entry.symbol,
            sig.params
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(","),
            sig.returns
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ));
    }
    assert!(feature_check(
        "b5.declare_handle_runtime",
        shape_ok,
        &format!(
            "idempotent={} roles={roles:?} decls=[{}] (TB/builder.rs:399; pin table TB/validate.rs:5729-5765)",
            first == second,
            rendered.join("; ")
        ),
    ));

    // negative twin: a pre-existing Ptr-typed `trust_bignum_nat_add` makes the builder
    // decline atomically (TB/builder.rs:424-440) — nothing is added.
    let mut mb = ModuleBuilder::new_with_target_info("b5_conflict", target());
    let ptr_sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]);
    mb.declare_function("trust_bignum_nat_add", ptr_sig);
    let refused = mb.declare_handle_runtime(nat_pin());
    let left = mb
        .build()
        .expect("ModuleBuilder::build: test fixture")
        .functions
        .len();
    assert!(feature_check(
        "b5.declare_handle_runtime.twin_conflicting_declaration",
        refused
            == Err(HandleDeclError::ConflictingDeclaration {
                symbol: "trust_bignum_nat_add".into()
            })
            && left == 1,
        &format!("{refused:?}, functions left={left}"),
    ));
}

/// The Clean `Nat -> Nat` recursion called from Rust: validate, codegen-validate, shape.
fn b5_02_clean_nat_function_called_from_rust_validates() {
    let module = nat_program();
    let errors = validate_module(&module);
    let codegen = validate_module_for_codegen(&module);
    let with_registry = validate_module_with_handle_registry(&module, HandleRegistry::pinned());
    // [reviewer] the authority tier (ImportPolicy::Refuse, TB/validate.rs:9069-9091) is the
    // strictest single-module entry point; the module is import- and certificate-free.
    let with_authority = validate_module_with_authority(&module, &RejectingModuleProofAuthority);

    let double = module.function_by_name("nat_double").unwrap();
    let double_sig = module.func_type(double.ty).unwrap().clone();
    // Every callee reached from nat_double / nat_mul is a pinned entry point or itself.
    let pinned: Vec<FuncId> = nat_pin()
        .entry_points
        .iter()
        .map(|e| func_id(&module, e.symbol))
        .collect();
    let mut clean_callees_ok = true;
    for name in ["nat_double", "nat_mul"] {
        let f = module.function_by_name(name).unwrap();
        for block in &f.blocks {
            for node in &block.body {
                if let Inst::Call { callee, .. } = &node.inst {
                    clean_callees_ok &= pinned.contains(callee) || *callee == f.id;
                }
            }
        }
    }
    let caller = module.function_by_name("rust_double_eq").unwrap();
    let edge = caller
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .any(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == double.id));
    let ok = errors.is_empty()
        && codegen.is_empty()
        && with_registry.is_empty()
        && with_authority.is_empty()
        && double.producer == Some(Producer::Clean)
        && caller.producer == Some(Producer::TRust)
        && double_sig.params == vec![nat()]
        && double_sig.returns == vec![nat()]
        && clean_callees_ok
        && edge;
    assert!(feature_check(
        "b5.clean_nat_fn_called_from_rust.validate",
        ok,
        &format!(
            "validate_module={errors:?} validate_module_for_codegen={codegen:?} \
             validate_module_with_handle_registry(pinned)={with_registry:?} \
             validate_module_with_authority(Rejecting)={with_authority:?} nat_double: {:?} ({}) -> ({}) \
             callees_only_pinned_or_self={clean_callees_ok} rust->clean edge={edge} caller={:?}",
            double.producer, double_sig.params[0], double_sig.returns[0], caller.producer
        ),
    ));

    // negative twin 1: the Rust caller hands the Clean callee its raw u64 (skips from_u64).
    // Refused on the exact call edge, attributed to both producers.
    let skewed = validate_module(&build_program("b5_skewed", true, CallEdge::Skewed));
    let twin = has(&skewed, |e| {
        matches!(
            e,
            ValidationError::CallArgTypeMismatch {
                callee,
                arg_index: 0,
                expected,
                actual,
                caller_producer: Some(cp),
                callee_producer: Some(ce),
                ..
            } if callee.contains("nat_double")
                && *expected == nat().to_string()
                && actual == "u64"
                && cp == &Producer::TRust.to_string()
                && ce == &Producer::Clean.to_string()
        )
    });
    assert!(feature_check(
        "b5.clean_nat_fn_called_from_rust.twin_u64_passed_as_nat",
        twin,
        &format!("{skewed:?}"),
    ));

    // negative twin 2: "just cast it" — the Rust caller forges the Nat from its u64 with
    // IntToPtr instead of calling from_u64. TB/validate.rs:6384-6423 (transport only) AND the
    // cast rule's own second line (TB/validate.rs:5393-5397).
    let mut forged = nat_program();
    let nat_double = func_id(&forged, "nat_double");
    {
        let f = function_mut(&mut forged, "rust_double_eq");
        let k = f.blocks[0].params[0].0;
        let block = &mut f.blocks[0];
        let call_at = block
            .body
            .iter()
            .position(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == nat_double))
            .unwrap();
        let fresh = ValueId::new(900);
        block.body.insert(
            call_at,
            InstrNode::new(Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::U64,
                dst_ty: nat(),
                operand: k,
            })
            .with_result(fresh),
        );
        if let Inst::Call { args, .. } = &mut block.body[call_at + 1].inst {
            args[0] = fresh;
        }
    }
    let errors = validate_module(&forged);
    assert!(feature_check(
        "b5.clean_nat_fn_called_from_rust.twin_cast_forged_nat",
        invalid_handle_use_naming(&errors, "Cast"),
        &format!("{errors:?}"),
    ));
}

/// Writer selects v43; 4-format round trip.
fn b5_03_wire_v43_and_four_format_round_trip() {
    let module = nat_program();
    let rt = roundtrip_all(&module);
    assert!(feature_check(
        "b5.wire_version_v43",
        rt.binary_version == 43 && trust_ir::binary::HANDLE_TYPE_FORMAT_VERSION == 43,
        &format!(
            "writer selected v{} (VERSION={}, HANDLE_TYPE_FORMAT_VERSION={}; TI/binary.rs:395)",
            rt.binary_version,
            trust_ir::binary::VERSION,
            trust_ir::binary::HANDLE_TYPE_FORMAT_VERSION
        ),
    ));

    // negative twin 1: the SAME program at the U64 carrier has no handle, so the writer must
    // NOT select 43 (it selects 41: body_gate/display_path are v41 contract surface).
    let analog = u64_program();
    let analog_errors = validate_module(&analog);
    let analog_rt = roundtrip_all(&analog);
    assert!(feature_check(
        "b5.wire_version_v43.twin_handle_free_analog_is_v41",
        analog_errors.is_empty() && analog_rt.binary_version == 41,
        &format!(
            "u64 analog validates={:?} writer selected v{}",
            analog_errors, analog_rt.binary_version
        ),
    ));

    // negative twin 2: an explicit v38 projection REFUSES, naming the handle.
    let mut refusals = Vec::new();
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let options = ModuleBinaryOptions {
            body,
            ..Default::default()
        };
        refusals.push(ProjectedModuleBinaryPlan::try_new(&module, options).err());
    }
    assert!(feature_check(
        "b5.wire_version_v43.twin_v38_projection_refused",
        refusals
            .iter()
            .all(|r| *r == Some(BinaryProjectionError::HandleTypeRequiresV43)),
        &format!("RawV38/CanonicalV38 => {refusals:?} (TI/binary.rs:6942-6954)"),
    ));

    // negative twin 3: relabel the v43 blob as v42 — an older-version header carrying type
    // tag 38 is refused, never misread (read gate `version >= 43`).
    let mut relabelled = rt.binary.encoded.clone();
    relabelled[8..12].copy_from_slice(&42u32.to_le_bytes());
    let refused = trust_ir::binary::deserialize_module(&relabelled);
    assert!(feature_check(
        "b5.wire_version_v43.twin_v42_header_refuses_tag_38",
        matches!(refused, Err(BinaryError::InvalidTag(38))),
        &format!("v42-labelled handle blob => {:?}", refused.as_ref().err()),
    ));

    assert!(feature_check(
        "b5.roundtrip.production",
        rt.lossless_production(),
        &rt.summary(),
    ));
    assert!(feature_check(
        "b5.roundtrip.text",
        rt.text.lossless(),
        &rt.text.summary(),
    ));
    // The decoded module is still the handle module (not a Ptr-typed collapse) in all four.
    let still_handle = rt.all().iter().all(|trip| {
        trip.decoded.as_ref().is_some_and(|m| {
            let f = m.function_by_name("nat_double").unwrap();
            let sig = m.func_type(f.ty).unwrap();
            sig.params == vec![nat()] && sig.returns == vec![nat()] && validate_module(m).is_empty()
        })
    });
    let text = String::from_utf8_lossy(&rt.text.encoded).into_owned();
    let spelled = text
        .lines()
        .find(|l| l.contains("handle<"))
        .unwrap_or("<no handle spelling found>")
        .trim()
        .to_string();
    assert!(feature_check(
        "b5.roundtrip.decoded_modules_keep_the_nominal_handle_and_revalidate",
        still_handle,
        &format!("text spelling: {spelled}"),
    ));

    // negative twin (round trip): flip the runtime path inside the JSON image — the decoder
    // accepts any lexically valid pair (the pin never travels on the wire), and the VALIDATOR
    // refuses the decoded module. This is what makes the pin validator-owned.
    let json = String::from_utf8(rt.json.encoded.clone()).unwrap();
    let tampered = json.replace("trust_bignum::Nat", "evil_bignum::Nat");
    let decoded: Result<Module, _> = serde_json::from_str(&tampered);
    let errors = decoded.as_ref().map(validate_module).unwrap_or_default();
    assert!(feature_check(
        "b5.roundtrip.twin_tampered_runtime_decodes_but_is_refused",
        decoded.is_ok()
            && has(&errors, |e| matches!(
                e,
                ValidationError::UntrustedHandleRuntime { runtime, .. } if runtime == "evil_bignum::Nat"
            )),
        &format!(
            "decode_ok={} distinct error variants={:?}",
            decoded.is_ok(),
            errors
                .iter()
                .map(|e| format!("{e:?}")
                    .split([' ', '{'])
                    .next()
                    .unwrap_or("")
                    .to_string())
                .collect::<std::collections::BTreeSet<_>>()
        ),
    ));
}

/// Every forgery in the design/CLAUDE.md list is a NAMED error. Each row mutates the
/// validating `nat_program()` by exactly one edit.
fn b5_04_every_forgery_is_a_named_error() {
    assert!(validate_module(&nat_program()).is_empty(), "baseline");

    // (1) Ptr-typed redeclaration of a pinned symbol.
    let mut m = nat_program();
    let ptr_sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    function_mut(&mut m, "trust_bignum_nat_add").ty = ptr_sig;
    let errors = validate_module(&m);
    let named = errors.iter().find(|e| {
        matches!(
            e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol, actual, .. }
                if symbol == "trust_bignum_nat_add" && actual == "signature (ptr, ptr) -> (ptr)"
        )
    });
    assert!(feature_check(
        "b5.forgery.ptr_typed_redeclaration",
        named.is_some(),
        &format!(
            "{named:?} (+{} follow-on call-edge error(s))",
            errors.len().saturating_sub(1)
        ),
    ));

    // (1') the same forgery in a module that never spells a handle (namespace guard runs on
    // EVERY module: TB/validate.rs:5971-5974).
    let mut bare = Module::new("b5_no_handle");
    bare.target_info = Some(target());
    push_c_declaration(
        &mut bare,
        "trust_bignum_nat_add",
        None,
        vec![Ty::Ptr, Ty::Ptr],
        vec![Ty::Ptr],
    );
    let errors = validate_module(&bare);
    assert!(feature_check(
        "b5.forgery.ptr_typed_redeclaration_in_handle_free_module",
        only(&errors, |e| matches!(
            e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                if symbol == "trust_bignum_nat_add"
        )),
        &format!("{errors:?}"),
    ));

    // (1'') wrong calling convention / wrong display path on an otherwise exact declaration.
    let mut m = nat_program();
    function_mut(&mut m, "trust_bignum_nat_sub").calling_conv = CallingConv::Rust;
    let conv = validate_module(&m);
    let mut m = nat_program();
    function_mut(&mut m, "trust_bignum_nat_sub").display_path =
        Some("trust_bignum::Nat::mul".into());
    let path = validate_module(&m);
    let is_mismatch = |errors: &[ValidationError], needle: &str| {
        has(errors, |e| {
            matches!(
                e,
                ValidationError::HandleEntryPointSignatureMismatch { symbol, actual, .. }
                    if symbol == "trust_bignum_nat_sub" && actual.contains(needle)
            )
        })
    };
    assert!(feature_check(
        "b5.forgery.wrong_convention_or_display_path",
        is_mismatch(&conv, "calling convention") && is_mismatch(&path, "display path"),
        &format!("conv={:?} path={:?}", conv.first(), path.first()),
    ));

    // (2) local definition of a pinned symbol (a body that returns its own argument).
    let mut m = nat_program();
    {
        let add = function_mut(&mut m, "trust_bignum_nat_add");
        let mut body = Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), nat())
            .with_param(ValueId::new(1), nat());
        body.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        add.blocks.push(body);
    }
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.local_definition",
        only(&errors, |e| matches!(
            e,
            ValidationError::HandleEntryPointDefinedLocally { symbol, .. } if symbol == "trust_bignum_nat_add"
        )),
        &format!("{errors:?}"),
    ));

    // (2') interposable linkage on the bodyless declaration is the same refusal.
    let mut m = nat_program();
    function_mut(&mut m, "trust_bignum_nat_add").linkage = Linkage::Weak;
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.weak_linkage_declaration",
        has(&errors, |e| matches!(
            e,
            ValidationError::HandleEntryPointDefinedLocally { symbol, .. } if symbol == "trust_bignum_nat_add"
        )),
        &format!(
            "{errors:?} (EmptyFunction rides along: only `Linkage::External` may be bodyless, TB/validate.rs:3022)"
        ),
    ));

    // (3) a global shadowing a pinned symbol.
    let mut m = nat_program();
    m.globals.push(global("trust_bignum_nat_is_zero", Ty::I64));
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.shadowing_global",
        only(&errors, |e| matches!(
            e,
            ValidationError::HandleEntryPointShadowedByGlobal { global, symbol }
                if global == "trust_bignum_nat_is_zero" && symbol == global
        )),
        &format!("{errors:?}"),
    ));

    // (4) address-taken, global-initializer spelling.
    let mut m = nat_program();
    let mut table = global("nat_vtable", Ty::Ptr);
    table.initializer = Some(Constant::SymbolAddr {
        symbol: "trust_bignum_nat_add".into(),
        addend: 0,
    });
    m.globals.push(table);
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.address_taken_global_initializer",
        only(&errors, |e| matches!(
            e,
            ValidationError::HandleEntryPointAddressTaken { location, symbol }
                if symbol == "trust_bignum_nat_add" && location == "global 'nat_vtable'"
        )),
        &format!("{errors:?}"),
    ));

    // (4') address-taken, function-body spelling: a handle-FREE module that drives the runtime
    // through `CallIndirect` over relocatable symbol addresses with Ptr-typed signatures.
    let mut mb = ModuleBuilder::new_with_target_info("b5_symbol_addr", target());
    let from_u64 = mb.add_func_type(vec![Ty::U64], vec![Ty::Ptr]);
    let is_zero = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::Bool]);
    {
        let mut fb = mb.function("main", main_ty);
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let seven = fb.uconst(Ty::U64, 7);
        let f = fb.const_value(
            Ty::Func(from_u64),
            Constant::SymbolAddr {
                symbol: "trust_bignum_nat_from_u64".into(),
                addend: 0,
            },
        );
        let n = fb.call_indirect(f, from_u64, vec![seven]);
        let z = fb.const_value(
            Ty::Func(is_zero),
            Constant::SymbolAddr {
                symbol: "trust_bignum_nat_is_zero".into(),
                addend: 0,
            },
        );
        let out = fb.call_indirect(z, is_zero, vec![n]);
        fb.ret(vec![out]);
        fb.build();
    }
    let forged = mb.build().expect("ModuleBuilder::build: test fixture");
    let errors = validate_module(&forged);
    let taken = |symbol: &str| {
        has(&errors, |e| {
            matches!(
                e,
                ValidationError::HandleEntryPointAddressTaken { symbol: s, .. } if s == symbol
            )
        })
    };
    // closeness control: the SAME shape over an unpinned neighbour symbol validates.
    let mut mb = ModuleBuilder::new_with_target_info("b5_symbol_addr_ok", target());
    let is_zero = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::Bool]);
    {
        let mut fb = mb.function("main", main_ty);
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let cell = fb.alloca(Ty::U64);
        let z = fb.const_value(
            Ty::Func(is_zero),
            Constant::SymbolAddr {
                symbol: "some_other_runtime_is_zero".into(),
                addend: 0,
            },
        );
        let out = fb.call_indirect(z, is_zero, vec![cell]);
        fb.ret(vec![out]);
        fb.build();
    }
    let control = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(feature_check(
        "b5.forgery.address_taken_call_indirect_in_handle_free_module",
        taken("trust_bignum_nat_from_u64")
            && taken("trust_bignum_nat_is_zero")
            && control.is_empty(),
        &format!("forged={errors:?} unpinned-neighbour control={control:?}"),
    ));

    // (5) CallIndirect over a raw pointer cannot return a Nat (no pinned origin).
    let mut m = nat_program();
    let unop = m.function_by_name("nat_double").unwrap().ty;
    {
        let f = function_mut(&mut m, "rust_nat_or");
        let a = f.blocks[0].params[0].0;
        let block = &mut f.blocks[0];
        let at = block.body.len() - 1;
        block.body.insert(
            at,
            InstrNode::new(Inst::NullPtr).with_result(ValueId::new(900)),
        );
        block.body.insert(
            at + 1,
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(900),
                sig: unop,
                args: vec![a],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(901)),
        );
    }
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.call_indirect_over_raw_pointer",
        invalid_handle_use_naming(&errors, "CallIndirect"),
        &format!("{errors:?}"),
    ));

    // (6) a branch edge cannot retype a Nat as a Ptr (exact-typed transport).
    let mut m = nat_program();
    {
        let f = function_mut(&mut m, "nat_double");
        let join = f
            .blocks
            .iter_mut()
            .find(|b| !b.params.is_empty() && b.id != BlockId::new(0))
            .unwrap();
        join.params[0].1 = Ty::Ptr;
    }
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.branch_edge_retypes_nat_as_ptr",
        has(&errors, |e| matches!(
            e,
            ValidationError::BranchArgTypeMismatch { expected, actual, .. }
                if expected == "ptr" && *actual == nat().to_string()
        )),
        &format!("{errors:?}"),
    ));

    // (7) a Nat cannot enter a variadic slot.
    let mut m = nat_program();
    let vsig = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let printf_like = next_func_id(&m);
    let mut decl = Function::new(printf_like, "printf_like", vsig, BlockId::new(0));
    decl.calling_conv = CallingConv::C;
    m.try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
    {
        let f = function_mut(&mut m, "rust_nat_or");
        let a = f.blocks[0].params[0].0;
        let block = &mut f.blocks[0];
        let at = block.body.len() - 1;
        block.body.insert(
            at,
            InstrNode::new(Inst::Call {
                callee: printf_like,
                args: vec![a],
            }),
        );
    }
    let errors = validate_module(&m);
    assert!(feature_check(
        "b5.forgery.nat_in_variadic_slot",
        has(&errors, |e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains("variadic")
        )),
        &format!("{errors:?}"),
    ));
}

/// Derived arithmetic is expressible as a DEFINED function (the only escape from the
/// four-entry pin table). Negative twin: strip the body and it becomes a foreign origin.
fn b5_05_derived_mul_is_a_defined_function() {
    let module = nat_program();
    let mul = module.function_by_name("nat_mul").unwrap();
    let sig = module.func_type(mul.ty).unwrap();
    assert!(feature_check(
        "b5.derived_mul_defined_over_pinned_entry_points",
        validate_module(&module).is_empty()
            && !mul.is_declaration()
            && sig.params == vec![nat(), nat()]
            && sig.returns == vec![nat()],
        "Clean nat_mul(a,b) by recursion on b over is_zero/sub/add/from_u64 validates (O(b) adds: carried, \
         not efficient)",
    ));

    let mut stripped = nat_program();
    function_mut(&mut stripped, "nat_mul").blocks.clear();
    let errors = validate_module(&stripped);
    assert!(feature_check(
        "b5.derived_mul_defined_over_pinned_entry_points.twin_bodyless",
        has(&errors, |e| matches!(
            e,
            ValidationError::HandleForeignDeclaration { name, handle, .. }
                if name == "nat_mul" && handle.contains("trust_bignum::Nat")
        )),
        &format!("{errors:?}"),
    ));
}

/// [reviewer] Two more laundering routes the v43 text names, each against its closest
/// WELL-FORMED baseline (same function over `Ptr`), so exactly one thing changes: the type
/// the pointer is claimed to become.
///
/// * `Invoke`'s NORMAL edge is a branch edge: `bb0(p: Ptr): invoke f() to bb1(p)` with
///   `bb1(h: Nat)` must be refused like `Br` (TB/validate.rs:6558-6579).
/// * A refinement is representation-preserving and the return/branch/call type checks skip
///   refined types (`!(actual.is_refine() || expected.is_refine())`, TB/validate.rs:11245), so
///   `Refine(Ptr, NonNull)` returned from `-> Nat` must be caught by the refinement rule.
fn b5_06_laundering_a_pointer_into_a_nat_is_refused() {
    // ---- Invoke normal edge ------------------------------------------------------------
    let invoke_module = |join: Ty, unwind_param: Option<Ty>| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_invoke_edge", target());
        mb.declare_handle_runtime(nat_pin()).unwrap();
        let thrower_sig = mb.add_func_type(vec![], vec![]);
        let thrower = mb.declare_function("may_unwind", thrower_sig);
        let sig = mb.add_func_type(vec![Ty::Ptr], vec![join.clone()]);
        let mut fb = mb.function("launder", sig);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(rust_gate());
        let bb0 = fb.create_block();
        let p = fb.add_block_param(bb0, Ty::Ptr);
        let bb1 = fb.create_block();
        let h = fb.add_block_param(bb1, join.clone());
        let bb2 = fb.create_block();
        if let Some(ty) = unwind_param {
            fb.add_block_param(bb2, ty);
        }
        fb.switch_to_block(bb0);
        fb.invoke_void(thrower, vec![], bb1, vec![p], bb2);
        fb.switch_to_block(bb1);
        fb.ret(vec![h]);
        fb.switch_to_block(bb2);
        let (exn, _sel) = fb.landingpad(true, vec![]);
        fb.resume(exn);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let baseline = validate_module(&invoke_module(Ty::Ptr, None));
    let forged = validate_module(&invoke_module(nat(), None));
    assert!(feature_check(
        "b5.forgery.invoke_normal_edge_retypes_ptr_as_nat",
        baseline.is_empty()
            && forged.len() == 1
            && matches!(
                &forged[0],
                ValidationError::BranchArgTypeMismatch { block: 0, target: 1, arg_index: 0, expected, actual }
                    if *expected == nat().to_string() && actual == "ptr"
            ),
        &format!(
            "Ptr join baseline={baseline:?}; Nat join => {forged:?} (TB/validate.rs:6558-6579)"
        ),
    ));
    // The unwind edge binds nothing, so a landing-pad block cannot conjure a Nat parameter.
    let unwind = validate_module(&invoke_module(Ty::Ptr, Some(nat())));
    assert!(feature_check(
        "b5.forgery.invoke_unwind_block_cannot_declare_a_nat_param",
        has(&unwind, |e| matches!(
            e,
            ValidationError::BranchArgCountMismatch {
                block: 0,
                target: 2,
                expected: 1,
                actual: 0
            }
        )),
        &format!("{unwind:?}"),
    ));

    // ---- Refine(Ptr, NonNull) returned from `-> Nat` -----------------------------------
    let refine_module = |ret: Ty| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_refine_launder", target());
        mb.declare_handle_runtime(nat_pin()).unwrap();
        let non_null = mb
            .intern_pred(trust_ir::Pred::NonNull)
            .expect("intern NonNull");
        let refined = mb.refine_ty(Ty::Ptr, non_null);
        let sig = mb.add_func_type(vec![refined.clone()], vec![ret]);
        let mut fb = mb.function("launder_refined", sig);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(rust_gate());
        let bb0 = fb.create_block();
        let p = fb.add_block_param(bb0, refined);
        fb.switch_to_block(bb0);
        fb.ret(vec![p]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let baseline = validate_module(&refine_module(Ty::Ptr));
    let forged = validate_module(&refine_module(nat()));
    assert!(feature_check(
        "b5.forgery.refined_ptr_returned_as_nat",
        baseline.is_empty()
            && !forged.is_empty()
            && has(&forged, |e| matches!(
                e,
                ValidationError::RefinementTypeInvalid { detail, .. } if detail.contains("does not match")
            )),
        &format!("`-> ptr` baseline={baseline:?}; `-> Nat` => {forged:?}"),
    ));
}

/// The three probes the archived battery CLAIMED but never landed (finding b5.uf05), now
/// real rows (roadmap WS8.6 step 1e). Each launders a function pointer whose signature
/// RETURNS a Nat: a `Const` `SymbolAddr` of an unpinned symbol typed `Ty::Func(u64 -> Nat)`,
/// a `Bitcast` of a raw `Ptr` to that function type, and an `Undef` / `Load` of it. The
/// closeness control for each is the SAME function over `Ty::Func(u64 -> u64)`, which
/// validates, so exactly one thing changes: the handle in the callee's return type.
fn b5_07_function_pointer_forgeries_of_a_nat() {
    // `forge(x: u64) -> R` = call_indirect(<origin of a Func(u64 -> R)>)(x).
    let forge = |ret: Ty, origin: &str| -> Vec<ValidationError> {
        let mut mb = ModuleBuilder::new_with_target_info("b5_fn_ptr_forgery", target());
        mb.declare_handle_runtime(nat_pin()).unwrap();
        let callee_sig = mb.add_func_type(vec![Ty::U64], vec![ret.clone()]);
        let sig = mb.add_func_type(vec![Ty::U64], vec![ret]);
        let mut fb = mb.function("forge", sig);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(rust_gate());
        let bb0 = fb.create_block();
        let x = fb.add_block_param(bb0, Ty::U64);
        fb.switch_to_block(bb0);
        let f = match origin {
            "symbol" => fb.const_value(
                Ty::Func(callee_sig),
                Constant::SymbolAddr {
                    symbol: "evil_nat_from_u64".into(),
                    addend: 0,
                },
            ),
            "bitcast" => {
                let p = fb.null_ptr();
                fb.cast(CastOp::Bitcast, Ty::Ptr, Ty::Func(callee_sig), p)
            }
            "undef" => fb.undef(Ty::Func(callee_sig)),
            "load" => {
                let slot = fb.alloca(Ty::Func(callee_sig));
                fb.load(Ty::Func(callee_sig), slot)
            }
            other => panic!("unknown origin {other}"),
        };
        let out = fb.call_indirect(f, callee_sig, vec![x]);
        fb.ret(vec![out]);
        fb.build();
        validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"))
    };
    // The ORIGIN instruction is refused by name (a Func type whose signature reaches a
    // handle is itself handle-bearing, so the pointer cannot even be formed).
    for (row, origin, named) in [
        (
            "b5.forgery.func_const_of_unpinned_symbol_returning_nat",
            "symbol",
            "Const",
        ),
        (
            "b5.forgery.bitcast_ptr_to_func_returning_nat",
            "bitcast",
            "Cast",
        ),
        ("b5.forgery.undef_func_returning_nat", "undef", "Undef"),
        ("b5.forgery.load_func_returning_nat", "load", "Load"),
    ] {
        let control = forge(Ty::U64, origin);
        let forged = forge(nat(), origin);
        // WS3.7: `Alloca` / `Load` / `Store` reaching a handle are decided by the
        // sealed-slot rule, which names ITS reason rather than the transport rule's:
        // a `Func` type whose signature reaches a handle is not a sealable slot type,
        // so the slot is refused by that name and the load as a read of an unsealed
        // slot — still exactly two refusals, both `InvalidHandleUse`.
        let named_refusal = if origin == "load" {
            let slot_refused = has(&forged, |e| {
                matches!(e, ValidationError::InvalidHandleUse { detail, .. }
                    if detail.starts_with("`Alloca` of `functy.")
                        && detail.contains("is not a sealable slot type"))
            });
            let load_refused = has(&forged, |e| {
                matches!(e, ValidationError::InvalidHandleUse { detail, .. }
                    if detail.starts_with("`Load` at `functy.")
                        && detail.contains("which is not sealed")
                        && detail.contains("is not a sealable slot type"))
            });
            slot_refused && load_refused
        } else {
            invalid_handle_use_naming(&forged, named)
        };
        assert!(feature_check(
            row,
            control.is_empty()
                && named_refusal
                && if origin == "bitcast" {
                    // the cast rule's own second line rides along (exactly one of it)
                    forged.len() == 2
                        && has(&forged, |e| {
                            matches!(e, ValidationError::CastLayoutUnsupported { reason, .. }
                            if reason.contains("an opaque runtime handle has no cast in or out"))
                        })
                } else if origin == "load" {
                    // the slot it is loaded from is refused too (exactly the Alloca)
                    forged.len() == 2
                        && forged
                            .iter()
                            .all(|e| matches!(e, ValidationError::InvalidHandleUse { .. }))
                } else {
                    forged.len() == 1
                },
            &format!(
                "closeness control over Func(u64 -> u64) => {control:?}; over Func(u64 -> Nat) => {forged:?}"
            ),
        ));
    }
}

// ===========================================================================
// GAP ratchets
// ===========================================================================

/// Was GAP: `mul`/`mod`/`to_u64`/compare/clone/drop were NOT pinned.
///
/// Cause (archived): `TRUSTED_HANDLE_RUNTIMES` had ONE row with exactly four entry points
/// and rule 6 (`validate_handle_foreign_declarations`) refuses EVERY other bodyless
/// declaration whose signature reaches a handle. Blocked GOAL G2/G3 (Lean `Nat` beyond
/// successor-style recursion: `*`, `/`, `%`, `<`, `decEq`, `toUInt64`, and handle lifetime).
///
/// FLIPPED: `drop` upstream by 454ed396 (the release pin), and every other row by WS3.2
/// (F-052), which made the pinned `Nat` row the Clean kernel's native `Nat` surface. The
/// row names are the archived ones; `eq` / `lt` are PASS on the kernel's spelling (`beq` /
/// `ble`, pinned) with the archived spelling as the twin that stays foreign, and `cmp` is
/// PASS asserting it STAYS foreign (the kernel has no three-way compare).
fn b5_10_gap_unpinned_nat_entry_points() {
    let h = nat();
    let roles: Vec<&str> = nat_pin().entry_points.iter().map(|e| e.role).collect();
    // FLIPPED (closed upstream by 454ed396 "ratify the handle RELEASE entry point"): the
    // archived ratchet recorded a four-entry table with no release path. The table now pins
    // a fifth, RELEASE entry point `trust_bignum_nat_drop : (Nat) -> ()`. Negative twin: a
    // Ptr-typed redeclaration of the release symbol is the named signature forgery.
    let mut forged_drop = Module::new("b5_forged_drop");
    forged_drop.target_info = Some(target());
    push_c_declaration(
        &mut forged_drop,
        "trust_bignum_nat_drop",
        None,
        vec![Ty::Ptr],
        vec![],
    );
    let forged = validate_module(&forged_drop);
    // FLIPPED again by WS3.2: the v1 five, then the Clean kernel's native `Nat` surface
    // (its closed `NAT_BINOPS` allowlist, the two-pin projection and `clone`), and nothing else.
    assert!(feature_check(
        "b5.gap.pin_table_is_exactly_four_entry_points",
        TRUSTED_HANDLE_RUNTIMES.len() == 1
            && roles
                == [
                    "from_u64",
                    "add",
                    "sub",
                    "is_zero",
                    "drop",
                    "mul",
                    "div",
                    "mod",
                    "beq",
                    "ble",
                    "fits_u64",
                    "to_u64",
                    "clone",
                    "land",
                    "lor",
                    "xor",
                    "shift_left",
                    "shift_right",
                    "pow",
                ]
            && validate_module(&nat_program()).is_empty()
            && only(&forged, |e| matches!(
                e,
                ValidationError::HandleEntryPointSignatureMismatch { symbol, .. } if symbol == "trust_bignum_nat_drop"
            )),
        &format!(
            "closed upstream by 454ed396 (drop) and WS3.2 (the kernel surface): \
             TRUSTED_HANDLE_RUNTIMES rows={} roles={roles:?}; negative twin: \
             `trust_bignum_nat_drop(ptr)` => {forged:?}",
            TRUSTED_HANDLE_RUNTIMES.len()
        ),
    ));

    // Baseline: the validating handle module. Single change: ONE more bodyless C declaration
    // in the runtime's own symbol/def-path scheme.
    assert!(validate_module(&nat_program()).is_empty(), "baseline");
    let wanted: Vec<(&str, Vec<Ty>, Vec<Ty>)> = vec![
        ("mul", vec![h.clone(), h.clone()], vec![h.clone()]),
        ("div", vec![h.clone(), h.clone()], vec![h.clone()]),
        ("mod", vec![h.clone(), h.clone()], vec![h.clone()]),
        ("pow", vec![h.clone(), h.clone()], vec![h.clone()]),
        ("to_u64", vec![h.clone()], vec![Ty::U64]),
        ("eq", vec![h.clone(), h.clone()], vec![Ty::Bool]),
        ("lt", vec![h.clone(), h.clone()], vec![Ty::Bool]),
        ("cmp", vec![h.clone(), h.clone()], vec![Ty::I32]),
        ("clone", vec![h.clone()], vec![h.clone()]),
    ];
    for (role, params, returns) in wanted {
        let symbol = format!("trust_bignum_nat_{role}");
        let def_path = format!("trust_bignum::Nat::{role}");
        // Negative twin shared by every pinned row: a Ptr-typed redeclaration of the pinned
        // symbol, in a module with no other declaration, is the named signature forgery — the
        // symbol is admitted because it is pinned at THIS shape, not because the namespace
        // opened.
        let ptr_twin = |symbol: &str, arity: usize| {
            let mut forged = Module::new("b5_forged_pin");
            forged.target_info = Some(target());
            push_c_declaration(&mut forged, symbol, None, vec![Ty::Ptr; arity], vec![]);
            validate_module(&forged)
        };
        let pinned_shape = |role: &str| {
            nat_pin()
                .entry_points
                .iter()
                .find(|e| e.role == role)
                .map(|e| nat_pin().func_ty(e))
        };
        match role {
            // FLIPPED by WS3.2 (F-052): the archived role, at the archived runtime shape, is a
            // row of the pinned table; `declare_handle_runtime` declares it and the handle
            // program validates with it.
            "mul" | "div" | "mod" | "pow" | "to_u64" | "clone" => {
                let shape = pinned_shape(role);
                let program = nat_program();
                let declared = program
                    .function_by_name(&symbol)
                    .is_some_and(|f| f.is_declaration());
                let twin = ptr_twin(&symbol, params.len());
                assert!(feature_check(
                    &format!("b5.gap.entry_point_not_pinned.{role}"),
                    shape
                        .as_ref()
                        .is_some_and(|t| t.params == params && t.returns == returns)
                        && declared
                        && validate_module(&program).is_empty()
                        && only(&twin, |e| matches!(
                            e,
                            ValidationError::HandleEntryPointSignatureMismatch { symbol: s, .. }
                                if *s == symbol
                        )),
                    &format!(
                        "closed by WS3.2: `{symbol}` pinned at {shape:?}, declared by \
                         declare_handle_runtime={declared}; negative twin (ptr params) => {twin:?}"
                    ),
                ));
            }
            // FLIPPED by WS3.2 on the kernel's spelling: `eq` / `lt` are Lean's `Nat.beq` /
            // `Nat.ble`, pinned as `beq` / `ble` at the same shape. Twin: the archived spelling
            // stays exactly one foreign declaration (one spelling per operation).
            // `cmp`: the kernel has no three-way compare (Lean `compare` derives from `beq` /
            // `ble`), so the PASS is that it STAYS exactly one foreign declaration while the two
            // roles it derives from are pinned.
            "eq" | "lt" | "cmp" => {
                let kernel: &[&str] = match role {
                    "eq" => &["beq"],
                    "lt" => &["ble"],
                    _ => &["beq", "ble"],
                };
                let kernel_pinned = kernel.iter().all(|k| {
                    pinned_shape(k).is_some_and(|t| {
                        t.params == vec![h.clone(), h.clone()] && t.returns == vec![Ty::Bool]
                    }) && nat_program()
                        .function_by_name(&format!("trust_bignum_nat_{k}"))
                        .is_some_and(|f| f.is_declaration())
                });
                let mut m = nat_program();
                push_c_declaration(&mut m, &symbol, Some(&def_path), params, returns);
                let errors = validate_module(&m);
                assert!(feature_check(
                    &format!("b5.gap.entry_point_not_pinned.{role}"),
                    kernel_pinned
                        && validate_module(&nat_program()).is_empty()
                        && nat_pin().entry_points.iter().all(|e| e.role != role)
                        && errors.len() == 1
                        && matches!(
                            &errors[0],
                            ValidationError::HandleForeignDeclaration { name, handle, .. }
                                if *name == symbol && handle.contains("trust_bignum::Nat")
                        ),
                    &format!(
                        "WS3.2: the kernel spelling {kernel:?} is pinned and declared; the \
                         archived spelling `{symbol}` => {errors:?}"
                    ),
                ));
            }
            other => panic!("unexpected archived role {other}"),
        }
    }

    // FLIPPED (closed upstream by 454ed396): the archived `entry_point_not_pinned.drop`
    // ratchet is now a PASS. `declare_handle_runtime` emits the pinned release entry point and
    // the handle program validates with it; negative twin: a SECOND bodyless declaration of
    // the release symbol is refused as a duplicate link-time symbol.
    let with_drop = nat_program();
    let drop_decl = with_drop.function_by_name("trust_bignum_nat_drop");
    let mut twice = nat_program();
    push_c_declaration(
        &mut twice,
        "trust_bignum_nat_drop",
        Some("trust_bignum::Nat::drop"),
        vec![h.clone()],
        vec![],
    );
    let duplicate = validate_module(&twice);
    assert!(feature_check(
        "b5.gap.entry_point_not_pinned.drop",
        nat_pin().entry_points.iter().any(|e| e.role == "drop")
            && drop_decl.is_some_and(|f| f.is_declaration())
            && validate_module(&with_drop).is_empty()
            && only(&duplicate, |e| matches!(
                e,
                ValidationError::DuplicateFunctionSymbol { name, .. } if name == "trust_bignum_nat_drop"
            )),
        &format!(
            "closed upstream by 454ed396: drop is pinned and declared; negative twin (second declaration) => {duplicate:?}"
        ),
    ));

    // Closeness control: the refusal is about the HANDLE, not the declaration — the same
    // symbol scheme over machine words validates.
    let mut m = nat_program();
    push_c_declaration(
        &mut m,
        "trust_bignum_nat_mul_u64",
        None,
        vec![Ty::U64, Ty::U64],
        vec![Ty::U64],
    );
    let control = validate_module(&m);
    assert!(control.is_empty(), "control: {control:?}");

    // FLIPPED by WS3.2: there was NO way to compare, project or release a Nat. Now there is,
    // through the pinned roles only — compare via `beq`, project via `fits_u64` / `to_u64`,
    // release via `drop` — and that module validates on the plain and codegen lanes. The
    // twin is by design: the in-format substitutes stay refused by name (pointer identity is
    // not Nat equality). Baseline = the same three functions over `Ty::Ptr` (validates);
    // single change = the carrier type.
    let pinned_ops = {
        let mut mb = ModuleBuilder::new_with_target_info("b5_nat_ops_pinned", target());
        let decls = mb
            .declare_handle_runtime_roles(nat_pin(), &["beq", "fits_u64", "to_u64", "drop"])
            .expect("pinned roles");
        let cmp = mb.add_func_type(vec![nat(), nat()], vec![Ty::Bool]);
        let to_int = mb.add_func_type(vec![nat()], vec![Ty::U64]);
        let fits = mb.add_func_type(vec![nat()], vec![Ty::Bool]);
        let drop_sig = mb.add_func_type(vec![nat()], vec![]);
        for (name, sig, role, arity) in [
            ("x_eq", cmp, "beq", 2),
            ("x_fits_u64", fits, "fits_u64", 1),
            ("x_to_u64", to_int, "to_u64", 1),
            ("x_drop", drop_sig, "drop", 1),
        ] {
            let mut fb = mb.function(name, sig);
            fb.set_producer(Producer::Clean);
            fb.set_body_gate(clean_gate());
            let bb0 = fb.create_block();
            let args: Vec<ValueId> = (0..arity).map(|_| fb.add_block_param(bb0, nat())).collect();
            fb.switch_to_block(bb0);
            let callee = decls.entry(role).unwrap();
            if role == "drop" {
                fb.call_void(callee, args);
                fb.ret(vec![]);
            } else {
                let r = fb.call(callee, args);
                fb.ret(vec![r]);
            }
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let pinned_plain = validate_module(&pinned_ops);
    let pinned_codegen = validate_module_for_codegen(&pinned_ops);
    let build = |x: Ty| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_nat_ops", target());
        if x.is_handle() {
            mb.declare_handle_runtime(nat_pin()).unwrap();
        }
        let cmp = mb.add_func_type(vec![x.clone(), x.clone()], vec![Ty::Bool]);
        let to_int = mb.add_func_type(vec![x.clone()], vec![Ty::U64]);
        let drop_sig = mb.add_func_type(vec![x.clone()], vec![]);
        {
            let mut fb = mb.function("x_eq", cmp);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, x.clone());
            let b = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            let r = fb.icmp(ICmpOp::Eq, x.clone(), a, b);
            fb.ret(vec![r]);
            fb.build();
        }
        {
            let mut fb = mb.function("x_to_u64", to_int);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            let r = fb.cast(CastOp::PtrToInt, x.clone(), Ty::U64, a);
            fb.ret(vec![r]);
            fb.build();
        }
        {
            let mut fb = mb.function("x_drop", drop_sig);
            let bb0 = fb.create_block();
            let a = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            fb.release(a);
            fb.ret(vec![]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let baseline = validate_module(&build(Ty::Ptr));
    let errors = validate_module(&build(nat()));
    // One InvalidHandleUse per instruction, plus the generic operand rule each also trips
    // (ICmp over a non-integer, PtrToInt from a non-pointer, Release of a non-pointer) — the
    // exact shape the archived GAP recorded, now the by-design twin.
    let in_format_shape = errors
        .iter()
        .filter(|e| matches!(e, ValidationError::InvalidHandleUse { .. }))
        .count()
        == 3
        && errors.iter().all(|e| {
            let rendered = format!("{e:?}");
            [
                "InvalidHandleUse",
                "ICmpRequiresIntegerOrPtr",
                "CastIncompatible",
                "OperandNotPointer",
            ]
            .iter()
            .any(|variant| rendered.starts_with(variant))
        });
    assert!(feature_check(
        "b5.gap.no_in_format_compare_project_or_release_of_a_nat",
        pinned_plain.is_empty()
            && pinned_codegen.is_empty()
            && baseline.is_empty()
            && in_format_shape
            && invalid_handle_use_naming(&errors, "ICmp")
            && invalid_handle_use_naming(&errors, "Cast")
            && invalid_handle_use_naming(&errors, "Release"),
        &format!(
            "closed by WS3.2: beq/fits_u64/to_u64/drop module => plain {pinned_plain:?}, codegen \
             {pinned_codegen:?}; twin: Ptr baseline={baseline:?}; in-format at Nat: {} error(s), \
             InvalidHandleUse for ICmp/Cast(PtrToInt)/Release => {errors:?}",
            errors.len()
        ),
    ));
}

/// [reviewer] Scope of the pin-table GAP: it is a gap in the CONTENT of the validator-owned
/// `TRUSTED_HANDLE_RUNTIMES` table, not in the wire format or the rule set. The same module
/// that `validate_module` refuses for declaring an unpinned role validates — byte for byte
/// unchanged — under `validate_module_with_handle_registry` with a registry whose `Nat` row
/// carries one more entry point (`HandleRegistry::from_pins`). So closing the gap needs no
/// version bump (and WS3.2 closed its kernel-surface half exactly that way). The staged role
/// was `mul` until WS3.2 pinned it; it is now `gcd` (Lean's `Nat.gcd`, outside the Clean
/// kernel's native surface, so it stays unpinned). What stays a GAP: that explicit-registry lane is the
/// ONLY one — `validate_module_for_codegen`, `validate_module_with_authority` and
/// `validate_linked_module` are hard-wired to `HandleRegistry::pinned()`
/// (TB/validate.rs:8322,9085; TB/linked.rs:511), so no codegen-admitting or authority-tier
/// validation of a module declaring a staged role existed at the audit tree.
fn b5_15_pin_table_gap_is_validator_only() {
    // The shipped row plus the staged `gcd` role (so the only delta is `gcd`).
    const GCD: HandleEntryPoint = HandleEntryPoint {
        role: "gcd",
        symbol: "trust_bignum_nat_gcd",
        def_path: "trust_bignum::Nat::gcd",
        params: &[PinnedTy::Handle, PinnedTy::Handle],
        returns: &[PinnedTy::Handle],
    };
    assert!(nat_pin().entry_points.iter().all(|e| e.role != "gcd"));
    let mut entries = nat_pin().entry_points.to_vec();
    entries.push(GCD);
    let extended_row = HandleRuntimePin {
        entry_points: Box::leak(entries.into_boxed_slice()),
        ..nat_pin().clone()
    };
    assert_eq!(
        &extended_row.entry_points[..nat_pin().entry_points.len()],
        nat_pin().entry_points
    );
    let extended = HandleRegistry::from_pins(&[extended_row]).expect("well-formed extended pins");

    let with_gcd = |params: Vec<Ty>, returns: Vec<Ty>| {
        let mut m = nat_program();
        let gcd = push_c_declaration(
            &mut m,
            "trust_bignum_nat_gcd",
            Some("trust_bignum::Nat::gcd"),
            params,
            returns,
        );
        // ...and USE it, so the row is about a callable entry point, not a dead declaration:
        // rust_nat_or returns gcd(a, b) instead of select(..).
        let f = function_mut(&mut m, "rust_nat_or");
        let (a, b) = (f.blocks[0].params[0].0, f.blocks[0].params[1].0);
        let block = &mut f.blocks[0];
        let at = block.body.len() - 1;
        block.body.insert(
            at,
            InstrNode::new(Inst::Call {
                callee: gcd,
                args: vec![a, b],
            })
            .with_result(ValueId::new(950)),
        );
        if let Inst::Return { values } = &mut block.body[at + 1].inst {
            values[0] = ValueId::new(950);
        }
        m
    };
    let h = nat();
    let module = with_gcd(vec![h.clone(), h.clone()], vec![h.clone()]);
    let under_pinned = validate_module(&module);
    let under_extended = validate_module_with_handle_registry(&module, &extended);
    let rt = roundtrip_all(&module);
    assert!(feature_check(
        "b5.pin_table_extension_is_validator_only_no_wire_change",
        under_extended.is_empty()
            && rt.lossless_all()
            && rt.binary_version == 43
            && under_pinned.len() == 1
            && matches!(
                &under_pinned[0],
                ValidationError::HandleForeignDeclaration { name, .. } if name == "trust_bignum_nat_gcd"
            ),
        &format!(
            "module declaring+calling trust_bignum_nat_gcd: validate_module_with_handle_registry(pinned row + gcd)={under_extended:?}; \
             SAME bytes under the shipped table => {under_pinned:?}; {}",
            rt.summary()
        ),
    ));
    // negative twin: the extended registry is not a wildcard — a Ptr-typed `gcd` is the same
    // named forgery the shipped entry points get.
    let forged = with_gcd(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr]);
    let errors = validate_module_with_handle_registry(&forged, &extended);
    assert!(feature_check(
        "b5.pin_table_extension.twin_ptr_typed_mul_is_signature_mismatch",
        has(&errors, |e| matches!(
            e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol, actual, .. }
                if symbol == "trust_bignum_nat_gcd" && actual == "signature (ptr, ptr) -> (ptr)"
        )),
        &format!("{errors:?}"),
    ));
    // FLIPPED by WS1.5 (F-009): no strict-tier entry point accepted a registry
    // — `validate_module_for_codegen`, `validate_module_with_authority` and the
    // linked walk were hard-wired to `HandleRegistry::pinned()`. PASS: the
    // composed lanes take the extended registry and admit the same bytes —
    // `validate_module_for_codegen_with(CodegenAdmission::with_handle_registry)`,
    // `validate_module_report_with_authority_and_registry`, and
    // `validate_linked_module_with`. Negative twin: the pinned entry points
    // (the same lanes under the shipped table) still refuse exactly the `gcd`
    // declaration (`mul` joined the pinned Nat row in WS3.2, so the extension
    // entry is `gcd`), and the Ptr-typed forgery is refused by the extended
    // codegen lane too — the registry is threaded, not a wildcard.
    let codegen = validate_module_for_codegen(&module);
    let authority = validate_module_with_authority(&module, &RejectingModuleProofAuthority);
    let foreign_gcd = |errors: &[ValidationError]| {
        errors.len() == 1
            && matches!(
                &errors[0],
                ValidationError::HandleForeignDeclaration { name, .. } if name == "trust_bignum_nat_gcd"
            )
    };
    let admission = CodegenAdmission::pinned().with_handle_registry(&extended);
    let codegen_with = validate_module_for_codegen_with(&module, &admission);
    let authority_with = validate_module_report_with_authority_and_registry(
        &module,
        &RejectingModuleProofAuthority,
        &extended,
    )
    .into_errors();
    let no_imports = ModuleSet::new(std::iter::empty::<&Module>());
    let linked_with = validate_linked_module_with(
        &module,
        &no_imports,
        &RejectingModuleProofAuthority,
        &extended,
    );
    let linked_pinned =
        validate_linked_module(&module, &no_imports, &RejectingModuleProofAuthority);
    let forged_codegen = validate_module_for_codegen_with(&forged, &admission);
    let forgery_refused = has(&forged_codegen, |e| {
        matches!(
            e,
            ValidationError::HandleEntryPointSignatureMismatch { symbol, .. }
                if symbol == "trust_bignum_nat_gcd"
        )
    });
    assert!(feature_check(
        "b5.gap.no_codegen_or_authority_entry_point_takes_a_handle_registry",
        codegen_with.is_empty()
            && authority_with.is_empty()
            && linked_with.errors().is_empty()
            && foreign_gcd(&codegen)
            && foreign_gcd(&authority)
            && foreign_gcd(linked_pinned.errors())
            && forgery_refused,
        &format!(
            "closed by WS1.5: extended registry => for_codegen_with={codegen_with:?} \
             report_with_authority_and_registry={authority_with:?} linked_with={:?}; pinned twins => \
             for_codegen={codegen:?} with_authority={authority:?} linked={:?}; Ptr-typed gcd under \
             the extended codegen lane => {forged_codegen:?}",
            linked_with.errors(),
            linked_pinned.errors()
        ),
    ));
}

/// One aggregate shape over a payload type `x`: `set(agg, v) -> agg` and `get(agg) -> x`,
/// with the aggregate received as a parameter so no constant of type `x` is needed (the
/// U64 -> Nat flip is then a SINGLE change).
fn aggregate_module(name: &str, x: Ty, kind: &str) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    if x.is_handle() {
        mb.declare_handle_runtime(nat_pin()).unwrap();
    }
    let (agg, field): (Ty, u32) = match kind {
        "struct" => (Ty::Struct(StructId::new(0)), 0),
        // enum value model = [tag, fields..] (TI/interpret.rs:1984-1992): payload is field 1.
        "enum" => (Ty::Enum(EnumId::new(0)), 1),
        "tuple" => (Ty::Tuple(vec![Ty::U64, x.clone()]), 1),
        other => panic!("unknown aggregate kind {other}"),
    };
    let set_sig = mb.add_func_type(vec![agg.clone(), x.clone()], vec![agg.clone()]);
    let get_sig = mb.add_func_type(vec![agg.clone()], vec![x.clone()]);
    {
        let mut fb = mb.function("set_payload", set_sig);
        fb.set_producer(Producer::Clean);
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, agg.clone());
        let v = fb.add_block_param(bb0, x.clone());
        fb.switch_to_block(bb0);
        let out = fb.insert_field(agg.clone(), a, field, v);
        fb.ret(vec![out]);
        fb.build();
    }
    {
        let mut fb = mb.function("get_payload", get_sig);
        fb.set_producer(Producer::TRust);
        let bb0 = fb.create_block();
        let a = fb.add_block_param(bb0, agg.clone());
        fb.switch_to_block(bb0);
        let out = fb.extract_field(x.clone(), a, field);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    match kind {
        "struct" => {
            module.add_struct(StructDef {
                id: StructId::new(0),
                name: "Acct".into(),
                fields: vec![FieldDef {
                    name: "bal".into(),
                    ty: x,
                    offset: None,
                }],
                size: None,
                align: None,
                repr: StructRepr::C,
                origin: None,
            });
        }
        "enum" => {
            // Lean: inductive Lvl | zero | param (n : Nat)
            module.add_enum(EnumDef::new(
                EnumId::new(0),
                "Lvl",
                vec![
                    EnumVariant {
                        name: "zero".into(),
                        fields: vec![],
                        field_names: vec![],
                    },
                    EnumVariant {
                        name: "param".into(),
                        fields: vec![x],
                        field_names: vec!["n".into()],
                    },
                ],
            ));
        }
        _ => {}
    }
    module
}

/// `b5.carrier.one_nat_spelling` (WS3.4, the F-047 carrier seam; DG-45 option (a)).
///
/// Measured at `5b45b83b8` (audit c11, item 5): ONE two-language module carried three
/// spellings of `trust_bignum::Nat` — the Rust lane's `Struct("trust_bignum::Nat")`, the
/// Clean general lane's boxed `Ptr`, and the pinned `Ty::Handle`. §7 now ratifies one
/// carrier: a value of a pinned runtime's type crosses every producer boundary as
/// `Ty::Handle` and nothing else. The validator half: in a handle-bearing module a
/// `StructDef`/`EnumDef`/`RecordDef` whose `name` is a pinned runtime path is
/// `HandleRuntimeSpelledStructurally` (TB/validate.rs `validate_handle_runtime_spellings`).
/// The `Ptr` spelling stays undetectable here (a `Ptr` names no type): WS6 F-102.
fn b5_16_one_nat_carrier_across_producers() {
    let nat_struct = |id: u32, name: &str| StructDef {
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
    };

    // The mixed Clean+Rust module plus an unrelated struct `Acct` validates: the rule is
    // keyed on a definition's NAME, not on "a struct beside a handle".
    let mut with_acct = nat_program();
    with_acct.add_struct(nat_struct(0, "Acct"));
    let acct = validate_module(&with_acct);
    let acct_codegen = validate_module_for_codegen(&with_acct);
    assert!(feature_check(
        "b5.carrier.one_nat_spelling",
        acct.is_empty() && acct_codegen.is_empty(),
        &format!("nat_program + struct Acct: validate={acct:?} codegen={acct_codegen:?}"),
    ));

    // negative twin A: the same module plus `Struct("trust_bignum::Nat")` — the Rust lane's
    // measured spelling — is exactly one refusal naming the definition and the runtime.
    let mut two_spellings = nat_program();
    two_spellings.add_struct(nat_struct(0, "Acct"));
    two_spellings.add_struct(nat_struct(1, "trust_bignum::Nat"));
    let errors = validate_module(&two_spellings);
    let codegen = validate_module_for_codegen(&two_spellings);
    let is_the_rule = |errors: &[ValidationError]| {
        matches!(
            errors,
            [ValidationError::HandleRuntimeSpelledStructurally { def, runtime }]
                if def == "struct #1" && runtime == "trust_bignum::Nat"
        )
    };
    assert!(feature_check(
        "b5.carrier.one_nat_spelling.twin_structural_spelling_refused",
        is_the_rule(&errors)
            && is_the_rule(&codegen)
            && errors[0].to_string().contains("second spelling"),
        &format!("nat_program + struct trust_bignum::Nat => {errors:?}; codegen => {codegen:?}"),
    ));

    // negative twin B: the handle-free analog carrying the same struct validates — a Rust
    // crate that uses `trust_bignum::Nat` natively is not a producer boundary.
    let mut native = u64_program();
    native.add_struct(nat_struct(0, "trust_bignum::Nat"));
    let native_errors = validate_module(&native);
    assert!(feature_check(
        "b5.carrier.one_nat_spelling.twin_handle_free_module_is_not_a_boundary",
        native_errors.is_empty() && !native.types.iter().any(Ty::is_handle),
        &format!("u64_program + struct trust_bignum::Nat => {native_errors:?}"),
    ));

    // review twin C: the refusal survives EVERY wire lane. The rule reads a decoded module's
    // struct NAME; a transport that mangled `trust_bignum::Nat` (the `::` path separator was
    // outside the text grammar's bare-identifier alphabet until WS4.3) would hand a consumer
    // a module the rule no longer fires on. All FOUR lanes now round-trip the two-spelling
    // module losslessly — binary / JSON / MessagePack always did, and since WS4.3 (quoted
    // definition-site names) plus WS4.5 (struct field names and offsets) the canonical text
    // carries `"trust_bignum::Nat"` too, so it is no longer printed `#lossy` and no longer
    // refused — and each decoded module is exactly one refusal naming the runtime (a lane
    // may renumber the definition, so the row keys on the runtime, not the `struct #N`).
    // The mutation control is what makes that a measurement of the CARRIED name rather than
    // of the fixture: rename the decoded struct by one character on every lane and the rule
    // goes silent, so the refusal is decided by the bytes the transport carried.
    let rt = roundtrip_all(&two_spellings);
    let is_the_runtime_rule = |errors: &[ValidationError]| {
        matches!(
            errors,
            [ValidationError::HandleRuntimeSpelledStructurally { runtime, .. }]
                if runtime == "trust_bignum::Nat"
        )
    };
    let every_lane_refused = rt.all().iter().all(|trip| {
        trip.decoded
            .as_ref()
            .is_some_and(|back| is_the_runtime_rule(&validate_module(back)))
    });
    // mutation control: the carried NAME is what decides. One character off the pinned
    // runtime path on each decoded module and every lane validates clean.
    let near_miss_is_silent = rt.all().iter().all(|trip| {
        trip.decoded.as_ref().is_some_and(|back| {
            let mut renamed = back.clone();
            let mut hit = false;
            for def in &mut renamed.structs {
                if def.name == "trust_bignum::Nat" {
                    def.name = "trust_bignum::Nat_".into();
                    hit = true;
                }
            }
            hit && validate_module(&renamed).is_empty()
        })
    });
    assert!(feature_check(
        "b5.carrier.one_nat_spelling.twin_refusal_survives_every_wire_lane",
        rt.lossless_all() && every_lane_refused && near_miss_is_silent,
        &format!(
            "{}; every lane decoded and refused = {every_lane_refused}; text #lossy = {:?}; renamed-by-one-character control silent on every lane = {near_miss_is_silent}",
            rt.summary(),
            rt.text.lossy,
        ),
    ));
}

/// PASS (WS3.6, F-047 aggregate half): a Handle IS a struct / tuple / enum payload.
///
/// A struct or tuple lane is read and written at EXACTLY its declared type; an enum
/// payload lane is projected only under a dominating tag-switch case that selects the
/// variant carrying it (`TB/validate.rs`, `handle_aggregate_lane_rule`). Each row carries
/// its right-reason negative twin: the lane retyped (the `PtrToInt` leak) for struct and
/// tuple, and the projection lifted out of the guarded block for the enum. GOAL G2/G3
/// ("Nat carried everywhere Lean data can hold it") and TREE-06 (`param : Nat` inside the
/// paired enum) are exactly the shapes this admits.
fn b5_11_handle_as_an_aggregate_payload() {
    for kind in ["struct", "tuple"] {
        let baseline = validate_module(&aggregate_module("b5_agg_u64", Ty::U64, kind));
        let at_nat = validate_module(&aggregate_module("b5_agg_nat", nat(), kind));
        // The twin: the same module with the payload lane READ as a U64.
        let mut retyped = aggregate_module("b5_agg_retyped", nat(), kind);
        let field = if kind == "struct" { 0 } else { 1 };
        {
            let get = function_mut(&mut retyped, "get_payload");
            let node = get.blocks[0].body.first_mut().expect("the extract");
            node.inst = Inst::ExtractField {
                ty: Ty::U64,
                aggregate: ValueId::new(0),
                field,
            };
        }
        let twin = validate_module(&retyped);
        assert!(feature_check(
            &format!("b5.gap.handle_as_{kind}_payload"),
            baseline.is_empty()
                && at_nat.is_empty()
                && has(&twin, |e| matches!(
                    e,
                    ValidationError::InvalidHandleUse { .. }
                )),
            &format!(
                "U64 baseline={baseline:?}; Nat payload={at_nat:?}; lane read as U64 => {twin:?}"
            ),
        ));
    }
    // The enum half, under its tag switch. Same single U64 -> Nat flip.
    let baseline = validate_module(&guarded_enum_module("b5_enum_u64", Ty::U64, true));
    let at_nat = validate_module(&guarded_enum_module("b5_enum_nat", nat(), true));
    let unguarded_u64 = validate_module(&guarded_enum_module("b5_enum_u64_free", Ty::U64, false));
    let unguarded = validate_module(&guarded_enum_module("b5_enum_nat_free", nat(), false));
    assert!(feature_check(
        "b5.gap.handle_as_enum_payload",
        baseline.is_empty()
            && at_nat.is_empty()
            && unguarded_u64.is_empty()
            && has(&unguarded, |e| matches!(
                e,
                ValidationError::InvalidHandleUse { .. }
            )),
        &format!(
            "U64 guarded={baseline:?}; Nat guarded={at_nat:?}; U64 unguarded={unguarded_u64:?}; \
             Nat unguarded={unguarded:?}"
        ),
    ));

    // PASS (WS3.6): the TYPE is no longer spellable-but-uninhabitable. A
    // `MakeAggregate` over a pinned call's result seeds `Acct { bal: Nat }`, the lane
    // reads back at `Ty::Handle`, and the transport-only module still validates — while
    // `Undef` stays refused, so the value still has no origin but a pinned one.
    let mut m = aggregate_module("b5_agg_transport_only", nat(), "struct");
    m.functions.retain(|f| f.is_declaration());
    let agg = Ty::Struct(StructId::new(0));
    let id_sig = m
        .add_func_type(FuncTy {
            params: vec![agg.clone()],
            returns: vec![agg.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = next_func_id(&m);
    let mut pass = Function::new(id, "pass_acct", id_sig, BlockId::new(0));
    let mut bb0 = Block::new(BlockId::new(0)).with_param(ValueId::new(0), agg.clone());
    bb0.body.push(
        InstrNode::new(Inst::Copy {
            ty: agg.clone(),
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    );
    bb0.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    pass.blocks.push(bb0);
    m.try_add_function(pass)
        .expect("Module::try_add_function: test fixture");
    let transport = validate_module(&m);

    // The introduction form: `fn seed(n: Nat) -> Acct { Acct { bal: n } }`, then the
    // lane read straight back out at its exact type.
    let mut inhabited = m.clone();
    let seed_sig = inhabited
        .add_func_type(FuncTy {
            params: vec![nat()],
            returns: vec![agg.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let seed_id = next_func_id(&inhabited);
    let mut seed = Function::new(seed_id, "seed_acct", seed_sig, BlockId::new(0));
    let mut seed_bb0 = Block::new(BlockId::new(0)).with_param(ValueId::new(0), nat());
    seed_bb0.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: agg.clone(),
            variant: None,
            fields: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    seed_bb0.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: nat(),
            aggregate: ValueId::new(1),
            field: 0,
        })
        .with_result(ValueId::new(2)),
    );
    seed_bb0.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    seed.blocks.push(seed_bb0);
    inhabited
        .try_add_function(seed)
        .expect("Module::try_add_function: test fixture");
    let built = validate_module(&inhabited);

    // ...and neither a constant nor an undef can introduce one.
    let mut with_undef = m.clone();
    {
        let f = function_mut(&mut with_undef, "pass_acct");
        f.blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Undef { ty: agg.clone() }).with_result(ValueId::new(7)),
        );
    }
    let undef = validate_module(&with_undef);
    assert!(feature_check(
        "b5.gap.struct_with_nat_field_is_spellable_but_uninhabitable",
        transport.is_empty() && built.is_empty() && invalid_handle_use_naming(&undef, "Undef"),
        &format!(
            "transport-only={transport:?}; make_aggregate-seeded={built:?}; \
             adding `Undef Acct` => {undef:?}"
        ),
    ));
}

/// `fn make_param(x) -> Lvl` + `fn get_param(l: Lvl, fallback: x) -> x`, where the
/// projection sits inside the `param` case's successor when `guarded`, and before the
/// switch when not. TREE-06's `inductive Lvl | zero | param (n : Nat)`.
fn guarded_enum_module(name: &str, x: Ty, guarded: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    if x.is_handle() {
        mb.declare_handle_runtime(nat_pin()).unwrap();
    }
    let enum_id = EnumId::new(0);
    let def = EnumDef::new(
        enum_id,
        "Lvl",
        vec![
            EnumVariant {
                name: "zero".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "param".into(),
                fields: vec![x.clone()],
                field_names: vec!["n".into()],
            },
        ],
    );
    let tag_ty = def.canonical_tag_repr().expect("a canonical tag repr").ty();
    let e = Ty::Enum(enum_id);
    let make_sig = mb.add_func_type(vec![x.clone()], vec![e.clone()]);
    let get_sig = mb.add_func_type(vec![e.clone(), x.clone()], vec![x.clone()]);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.add_enum(def);

    let make_id = next_func_id(&module);
    let mut make = Function::new(make_id, "make_param", make_sig, BlockId::new(0));
    make.producer = Some(Producer::Clean);
    let mut bb0 = Block::new(BlockId::new(0)).with_param(ValueId::new(0), x.clone());
    bb0.body.push(
        InstrNode::new(Inst::MakeAggregate {
            ty: e.clone(),
            variant: Some(1),
            fields: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    bb0.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    make.blocks.push(bb0);
    module
        .try_add_function(make)
        .expect("Module::try_add_function: test fixture");

    let get_id = next_func_id(&module);
    let mut get = Function::new(get_id, "get_param", get_sig, BlockId::new(0));
    get.producer = Some(Producer::TRust);
    let project = InstrNode::new(Inst::ExtractField {
        ty: x.clone(),
        aggregate: ValueId::new(0),
        field: 1,
    })
    .with_result(ValueId::new(3));
    let mut entry = Block::new(BlockId::new(0))
        .with_param(ValueId::new(0), e)
        .with_param(ValueId::new(1), x);
    entry.body.push(
        InstrNode::new(Inst::ExtractField {
            ty: tag_ty,
            aggregate: ValueId::new(0),
            field: 0,
        })
        .with_result(ValueId::new(2)),
    );
    if !guarded {
        entry.body.push(project.clone());
    }
    entry.body.push(InstrNode::new(Inst::Switch {
        value: ValueId::new(2),
        default: BlockId::new(2),
        default_args: vec![],
        cases: vec![trust_ir::inst::SwitchCase {
            value: Constant::Int(1),
            target: BlockId::new(1),
            args: vec![],
        }],
        exhaustive_enum_unreachable: false,
    }));
    let mut hit = Block::new(BlockId::new(1));
    if guarded {
        hit.body.push(project);
        hit.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }));
    } else {
        hit.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
    }
    let mut miss = Block::new(BlockId::new(2));
    miss.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    get.blocks = vec![entry, hit, miss];
    module
        .try_add_function(get)
        .expect("Module::try_add_function: test fixture");
    module
}

/// WS3.7 (F-047, memory half): a Handle in memory. The archived row
/// `b5.gap.handle_behind_ref_or_in_memory` measured three functions, which WS3.7 splits:
///
/// * `…spilled_local` — PASS. The spill (`let slot = v; let r = &slot; *r`), spelled as the
///   Rust producers spell `&slot` (the slot address itself), is a SEALED slot
///   (`TB/validate/handle_slots.rs`): its pointer is used only by exact-typed stores and
///   loads, and every load is dominated by a store.
///   Right-reason twin: the same spill with the load BEFORE the store is refused by name
///   ("load of a handle slot not dominated by a store" — an uninitialized word would be a
///   forged handle).
/// * `…behind_ref_param` — GAP until WS3.7 phase 2 (DG-46, gated on WS5.16 / F-094): a
///   `Load` / `Store` at `Nat` through a `&Nat` / `&mut Nat` PARAMETER goes through a
///   pointer that is not a sealed slot, so both are refused. Blocks LCR-10 (Rust APIs over
///   `&Nat`) unless the producer lowers `&Nat` as the handle word itself.
/// * `b5.gap.handle_typed_global` — PASS asserting the RATIFIED refusal (SPEC §7): a global
///   is machine storage no sealed-slot discipline covers, and a Lean top-level `Nat`
///   constant is a function returning a fresh handle.
fn b5_12_handle_in_memory() {
    let build = |x: Ty, spill: bool, refs: bool, load_first: bool| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_ref", target());
        if x.is_handle() {
            mb.declare_handle_runtime(nat_pin()).unwrap();
        }
        let deref_sig = mb.add_func_type(vec![Ty::Ref(Box::new(x.clone()))], vec![x.clone()]);
        let write_sig = mb.add_func_type(vec![Ty::RefMut(Box::new(x.clone())), x.clone()], vec![]);
        let spill_sig = mb.add_func_type(vec![x.clone()], vec![x.clone()]);
        if refs {
            // fn read(r: &X) -> X { *r }
            let mut fb = mb.function("read_ref", deref_sig);
            fb.set_producer(Producer::TRust);
            let bb0 = fb.create_block();
            let r = fb.add_block_param(bb0, Ty::Ref(Box::new(x.clone())));
            fb.switch_to_block(bb0);
            let v = fb.load(x.clone(), r);
            fb.ret(vec![v]);
            fb.build();
        }
        if refs {
            // fn write(r: &mut X, v: X) { *r = v }
            let mut fb = mb.function("write_ref", write_sig);
            fb.set_producer(Producer::TRust);
            let bb0 = fb.create_block();
            let r = fb.add_block_param(bb0, Ty::RefMut(Box::new(x.clone())));
            let v = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            fb.store(x.clone(), r, v);
            fb.ret(vec![]);
            fb.build();
        }
        if spill {
            // fn spill(v: X) -> X { let slot = v; let r = &slot; *r }   (THIR-style local)
            let mut fb = mb.function("spill_local", spill_sig);
            fb.set_producer(Producer::TRust);
            let bb0 = fb.create_block();
            let v = fb.add_block_param(bb0, x.clone());
            fb.switch_to_block(bb0);
            let slot = fb.alloca(x.clone());
            let out = if load_first {
                // The twin: read the slot before anything was stored into it.
                let out = fb.load(x.clone(), slot);
                fb.store(x.clone(), slot, v);
                out
            } else {
                // THIR's spelling of `let r = &slot; *r`: the reference IS the slot
                // address, so the load goes through `slot` itself. A function
                // stamped `Producer::TRust` carries no permission instruction
                // (SPEC "A Rust reference carries no permission instruction").
                fb.store(x.clone(), slot, v);
                fb.load(x.clone(), slot)
            };
            fb.ret(vec![out]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    };

    // …spilled_local: PASS.
    let baseline_module = build(Ty::U64, true, false, false);
    let baseline = validate_module(&baseline_module);
    // The baseline is semantically real: spill_local(9) == 9 on the reference interpreter.
    let ran = run_with_args(
        &baseline_module,
        "spill_local",
        vec![InterpretValue::int(Ty::U64, 9).unwrap()],
    );
    let ran_ok = ran
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128)
        == Some(9);
    let spilled = validate_module(&build(nat(), true, false, false));
    let unstored = validate_module(&build(nat(), true, false, true));
    let twin_refused = !unstored.is_empty()
        && unstored.iter().all(|e| {
            matches!(e, ValidationError::InvalidHandleUse { detail, .. }
                if detail.contains("load of a handle slot not dominated by a store"))
        });
    assert!(feature_check(
        "b5.gap.handle_behind_ref_or_in_memory.spilled_local",
        baseline.is_empty() && ran_ok && spilled.is_empty() && twin_refused,
        &format!(
            "U64 baseline validate={baseline:?} spill_local(9)={ran:?}; spilled Nat local => \
             {spilled:?}; load before store => {unstored:?}"
        ),
    ));

    // …behind_ref_param: GAP until WS3.7 phase 2.
    let refs_baseline = validate_module(&build(Ty::U64, false, true, false));
    let at_nat = validate_module(&build(nat(), false, true, false));
    let names = |op: &str| {
        has(&at_nat, |e| {
            matches!(e, ValidationError::InvalidHandleUse { detail, .. }
                if detail.starts_with(&format!("`{op}` at `{}` goes through a pointer", nat())))
        })
    };
    assert!(feature_gap(
        "b5.gap.handle_behind_ref_or_in_memory.behind_ref_param",
        Expect::refused_times(
            "InvalidHandleUse",
            at_nat.len().max(1),
            &["goes through a pointer that is not a sealed handle slot"]
        ),
        Outcome::of(&at_nat).given(&[
            ("the U64 baseline validates", refs_baseline.is_empty()),
            ("the Load through `&Nat` is named", names("Load")),
            ("the Store through `&mut Nat` is named", names("Store")),
            (
                "the refusal count is the recorded one",
                at_nat.len() == HANDLE_BEHIND_REF_PARAM_REFUSALS
            ),
        ]),
        &format!(
            "U64 baseline validate={refs_baseline:?}; &Nat / &mut Nat params => {} error(s): \
             {at_nat:?}",
            at_nat.len()
        ),
    ));

    // A Nat cannot be a global either (no static / thread-local Nat) — RATIFIED.
    let mut m = nat_program();
    m.globals.push(global("NAT_CACHE", nat()));
    let errors = validate_module(&m);
    let mut m64 = nat_program();
    m64.globals.push(global("NAT_CACHE", Ty::U64));
    let control = validate_module(&m64);
    let ratified = matches!(
        errors.as_slice(),
        [ValidationError::InvalidHandleUse { location, detail }]
            if location.contains("NAT_CACHE")
                && detail.contains("globals declare machine storage")
                && detail.contains("outside a sealed function-local slot")
    );
    assert!(feature_check(
        "b5.gap.handle_typed_global",
        control.is_empty() && ratified,
        &format!("U64 global control={control:?}; Nat global => {errors:?} (ratified refusal)"),
    ));
}

/// PASS since WS3.3 (F-048): a cross-crate body-less USER function over Nat is
/// importable through `validate_linked_module` when its declaration is bound to
/// the dependency with an entity-only `backed_by` (DG-26).
///
/// Before WS3.3 rule 6 had NO exception for an import-backed declaration (it
/// skipped only definitions and pinned symbols), so the root was exactly one
/// `HandleForeignDeclaration` in every lane. Linked rule L11 now resolves the
/// binding at `ExternRefSite::HandleDeclaration` (R4 hardened to a far
/// definition), and rule 6 admits the declaration under the linked walk only.
/// Unblocks design 2026-08-27 cross-crate calls into a dependency's
/// `Nat`-typed Clean def (Part A `dep`) and LCR-10's cross-crate Nat callee.
fn b5_13_gap_cross_crate_user_function_over_nat() {
    /// `dep` DEFINES `dep_double : X -> X` (Clean); `root` declares it bodyless
    /// (bound to import 0 with an entity-only `backed_by` when `bound`),
    /// records the import row, and a Rust `root_use(x: X) -> X` calls it.
    fn pair(use_nat: bool, bound: bool) -> (Module, Module) {
        let dep = {
            let mut mb = ModuleBuilder::new_with_target_info("b5_dep", target());
            let carrier = if use_nat {
                Carrier::Nat(mb.declare_handle_runtime(nat_pin()).unwrap())
            } else {
                Carrier::U64
            };
            let c = carrier.ty();
            let unop = mb.add_func_type(vec![c.clone()], vec![c.clone()]);
            let mut fb = mb.function("dep_double", unop);
            fb.set_producer(Producer::Clean);
            fb.set_body_gate(clean_gate());
            let bb0 = fb.create_block();
            let n = fb.add_block_param(bb0, c.clone());
            fb.switch_to_block(bb0);
            let out = carrier.add(&mut fb, n, n);
            fb.ret(vec![out]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        let root = {
            let mut mb = ModuleBuilder::new_with_target_info("b5_root", target());
            let c = if use_nat {
                mb.declare_handle_runtime(nat_pin()).unwrap().handle
            } else {
                Ty::U64
            };
            let unop = mb.add_func_type(vec![c.clone()], vec![c.clone()]);
            mb.set_default_producer(Producer::Clean);
            let far = mb.declare_function("dep_double", unop);
            let mut fb = mb.function("root_use", unop);
            fb.set_producer(Producer::TRust);
            fb.set_body_gate(rust_gate());
            let bb0 = fb.create_block();
            let x = fb.add_block_param(bb0, c.clone());
            fb.switch_to_block(bb0);
            let out = fb.call(far, vec![x]);
            fb.ret(vec![out]);
            fb.build();
            let mut root = mb.build().expect("ModuleBuilder::build: test fixture");
            let import = root
                .intern_import(
                    ModuleImport::new("b5_dep", dep.stable_digest()).with_producer(Producer::Clean),
                )
                .expect("Module::intern_import: test fixture");
            if bound {
                function_mut(&mut root, "dep_double").summary = Some(
                    FunctionSummary::new()
                        .with_params(vec!["x".to_string()])
                        .backed_by(trust_ir::ExternRef::new(import, "dep_double")),
                );
            }
            root
        };
        (dep, root)
    }

    let (dep64, root64) = pair(false, false);
    let (dep_nat, root_nat) = pair(true, true);
    let (_, root_nat_unbound) = pair(true, false);
    let linked = |root: &Module, dep: &Module| {
        validate_linked_module(root, &ModuleSet::new([dep]), &RejectingModuleProofAuthority)
            .into_errors()
    };

    let base_dep = validate_module(&dep64);
    let base_root = validate_module(&root64);
    let base_verify = root64
        .verify_import(trust_ir::ImportId::new(0), &dep64)
        .is_ok();
    let base_linked = linked(&root64, &dep64);

    let nat_dep = validate_module(&dep_nat);
    let nat_verify = root_nat
        .verify_import(trust_ir::ImportId::new(0), &dep_nat)
        .is_ok();
    let nat_linked = linked(&root_nat, &dep_nat);
    assert!(feature_check(
        "b5.gap.cross_crate_user_fn_over_nat_is_foreign_declaration",
        base_dep.is_empty()
            && base_root.is_empty()
            && base_verify
            && base_linked.is_empty()
            && nat_dep.is_empty()
            && nat_verify
            && nat_linked.is_empty(),
        &format!(
            "U64 baseline: dep={base_dep:?} root={base_root:?} verify_import={base_verify} \
             linked={base_linked:?}; Nat: dep (DEFINES dep_double)={nat_dep:?} verify_import \
             (digest authenticates)={nat_verify}; root bound with an entity-only backed_by: \
             validate_linked_module={nat_linked:?}"
        ),
    ));

    // The twin: the SAME bound root outside the linked walk, and the unbound
    // root inside it, are each exactly one `HandleForeignDeclaration` — with
    // the reason that applies.
    let foreign = |errors: &[ValidationError], needle: &str| {
        errors.len() == 1
            && matches!(
                &errors[0],
                ValidationError::HandleForeignDeclaration { name, handle, detail, .. }
                    if name == "dep_double"
                        && handle.contains("trust_bignum::Nat")
                        && detail.contains(needle)
            )
    };
    let plain = validate_module(&root_nat);
    let authority = validate_module_with_authority(&root_nat, &RejectingModuleProofAuthority);
    let unbound = linked(&root_nat_unbound, &dep_nat);
    assert!(feature_check(
        "b5.gap.cross_crate_user_fn_over_nat_is_foreign_declaration.twin_refused_outside_the_linked_walk",
        foreign(&plain, "admitted only by validate_linked_module")
            && foreign(&authority, "admitted only by validate_linked_module")
            && foreign(&unbound, "no `backed_by` binds it"),
        &format!(
            "bound root: validate_module={plain:?} validate_module_with_authority={authority:?}; \
             unbound root: validate_linked_module={unbound:?}"
        ),
    ));
}

/// PASS (host-assisted, WS2.13; was GAP under F-035): the reference interpreter
/// executes the handle-bearing program through the reference host model of the
/// pinned `trust_bignum::Nat` runtime (`trust_ir_build::PinnedHandleHost`,
/// installed with `Interpreter::with_host`). The model is a TRUSTED reading of
/// the runtime (TRUST.md item 9), so the run reports `host_calls > 0` and is
/// host-assisted evidence, never in-format execution. Negative twin: the same
/// program with NO host is the named, fail-closed `UnsupportedCall` at the first
/// pinned entry point (the WS2.12 shape), never `MissingBlock`. Mutation
/// control: `rust_double_eq(21, 43)` is false under the model.
///
/// `handle_is_outside_the_proven_conformance_subset` stays RATIFIED-OUT by
/// design: `Ty::Handle` is runtime-opaque (TI/bridge.rs, "outside the proven
/// subset by construction"; TRUST.md item 9), and a host model does not move
/// it inside — it is the reason the run is host-assisted.
fn b5_14_reference_interpreter_executes_handles_host_assisted() {
    // Baseline: the SAME program at the U64 carrier validates and executes
    // in-format (zero host calls).
    let analog = u64_program();
    let analog_errors = validate_module(&analog);
    let analog_run = run_nullary(&analog, "program");
    let analog_true = analog_run
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(|v| v.as_bool())
        == Some(true);
    let mul = run_with_args(
        &analog,
        "nat_mul",
        vec![
            InterpretValue::int(Ty::U64, 6).unwrap(),
            InterpretValue::int(Ty::U64, 7).unwrap(),
        ],
    );
    let mul_ok = mul
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128)
        == Some(42);

    // Single change: the carrier. Validates; executes ONLY host-assisted.
    let module = nat_program();
    let errors = validate_module(&module);
    let unhosted = run_nullary(&module, "program");
    let hosted = run_hosted(&module, "program", Vec::new());
    let hosted_true = hosted
        .as_ref()
        .ok()
        .and_then(|(v, _)| v.first())
        .and_then(|v| v.as_bool())
        == Some(true);
    let host_calls = hosted.as_ref().ok().map_or(0, |(_, calls)| *calls);
    let u64_arg = |v: u64| InterpretValue::int(Ty::U64, i128::from(v)).unwrap();
    let mutant = run_hosted(&module, "rust_double_eq", vec![u64_arg(21), u64_arg(43)]);
    let mutant_false = mutant
        .as_ref()
        .ok()
        .and_then(|(v, _)| v.first())
        .and_then(|v| v.as_bool())
        == Some(false);
    let twin_named = matches!(
        &unhosted,
        Err(message)
            if message.starts_with("UnsupportedCall:")
                && message.contains(
                    "call to bodyless declaration @trust_bignum_nat_from_u64: no host model"
                )
    );
    assert!(feature_check(
        "b5.gap.reference_interpreter_cannot_execute_handle_program",
        analog_errors.is_empty()
            && analog_true
            && mul_ok
            && errors.is_empty()
            && hosted_true
            && host_calls > 0
            && mutant_false
            && twin_named,
        &format!(
            "tool=trust_ir::interpret::Interpreter (in-process); U64 analog: program()={analog_run:?} \
             nat_mul(6,7)={mul:?}; Nat module (validates={}): with PinnedHandleHost program()={hosted:?} \
             rust_double_eq(21,43)={mutant:?}; without a host program()={unhosted:?}",
            errors.is_empty()
        ),
    ));

    // The proven-subset classifier still agrees: every Nat-typed site is a
    // violation, by design — a host model is not the proven subset.
    let subset = ConformanceSubset::CURRENT.check(&module);
    let analog_subset = ConformanceSubset::CURRENT.check(&analog);
    let reasons: std::collections::BTreeSet<&str> = subset
        .as_ref()
        .err()
        .map(|v| v.iter().map(|x| x.reason).collect())
        .unwrap_or_default();
    assert!(feature_ratified(
        "b5.gap.handle_is_outside_the_proven_conformance_subset",
        Expect::measured("one reason: handle types are runtime-opaque"),
        Outcome::measured(match reasons.iter().collect::<Vec<_>>().as_slice() {
            [r] if r.starts_with("handle types are runtime-opaque") =>
                "one reason: handle types are runtime-opaque".to_string(),
            other => format!("reasons {other:?}"),
        })
        .given(&[("the U64 analog is inside the subset", analog_subset.is_ok())]),
        &format!(
            "RATIFIED-OUT (TRUST.md item 9; TI/bridge.rs `Ty::Handle` is outside the proven \
             subset by construction): ConformanceSubset v{} : U64 analog={:?}; Nat module \
             violations={} reasons={reasons:?}",
            ConformanceSubset::CURRENT.version,
            analog_subset.as_ref().map_err(|v| v.len()),
            subset.as_ref().err().map_or(0, Vec::len)
        ),
    ));

    // The CLI `run --host pinned` lane rows
    // (`b5.gap.cli_run_cannot_execute_handle_program`,
    // `b5.gap.cli_run_without_validate_traps_at_pinned_stub`) run the real binary and live
    // in `crates/trust-ir-cli/tests/two_language_cli.rs` over `b5_fixtures.rs`.
}

/// `common::run_with_args` with the reference host model of the pinned
/// runtimes installed (WS2.13). Returns the values and the host-call count.
fn run_hosted(
    module: &Module,
    entry: &str,
    args: Vec<InterpretValue>,
) -> Result<(Vec<InterpretValue>, u64), String> {
    let func = module
        .function_by_name(entry)
        .ok_or_else(|| format!("no function named @{entry}"))?;
    let id = func.id;
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("two-language-interp-hosted".into())
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(scope, move || {
                let host = PinnedHandleHost::new();
                trust_ir::interpret::Interpreter::with_module(module)
                    .with_options(common::run_options())
                    .with_host(&host)
                    .execute_func(id, args)
                    .map(|outcome| (outcome.returns, outcome.host_calls))
                    .map_err(|e| format!("{:?}: {e}", e.code))
            })
            .map_err(|e| format!("spawn interpreter thread: {e}"))?
            .join()
            .map_err(|_| "interpreter thread panicked".to_string())?
    })
}

// ===========================================================================
// Closely related rows discovered while reading the source
// ===========================================================================

fn int_binding(name: &str, sort: ClauseSort, place: ClausePlace) -> (String, ClauseBinding) {
    (name.to_string(), ClauseBinding { sort, place })
}

/// `nat_program()` with the Lean-side contract of `double` attached to the Clean function:
/// `ensures result = 2 * n`, `decreases n`, the free names bound at `n_sort`.
fn nat_program_with_contract(n_sort: ClauseSort, n_place: ClausePlace) -> Module {
    let mut module = nat_program();
    let mut ensures = ProofFormula::smtlib2("(= result (* 2 n))", "Bool");
    ensures.bindings = vec![
        int_binding("n", n_sort.clone(), n_place),
        int_binding(
            "result",
            n_sort.clone(),
            ClausePlace::ResultSlot { index: 0 },
        ),
    ];
    let mut measure = ProofFormula::smtlib2("n", "Int");
    measure.bindings = vec![int_binding("n", n_sort, n_place)];
    let mut summary = FunctionSummary::new()
        .with_params(vec!["n".to_string()])
        .ensuring(ensures);
    summary.decreases.push(measure);
    function_mut(&mut module, "nat_double").summary = Some(summary);
    module
}

/// The three always-on binding refusals a contract over `nat_double` draws at `sort`: `n` at
/// `Param{0}` and `result` at `ResultSlot{0}` in the ensures clause, and `n` in the measure.
/// Each is an `InvalidFunctionSummary` naming the sort and the `handle<"Nat", ..>` place.
fn every_nat_binding_refused(errors: &[ValidationError], sort: &ClauseSort) -> bool {
    let nat = "handle<\"Nat\", \"trust_bignum::Nat\">";
    let want = [
        format!("ensures clause 0 binding 'n' has sort {sort:?} but Param 0 is {nat}"),
        format!("ensures clause 0 binding 'result' has sort {sort:?} but ResultSlot 0 is {nat}"),
        format!("decreases clause 0 binding 'n' has sort {sort:?} but Param 0 is {nat}"),
    ];
    errors.len() == want.len()
        && want.iter().all(|needle| {
            errors.iter().any(|e| {
                matches!(e, ValidationError::InvalidFunctionSummary { detail, .. } if detail == needle)
            })
        })
}

/// RATIFIED-OUT (WS1.2, 31814e51; roadmap DG-19 "refuse the handle place now, admit it in the
/// WS3 Nat increment once the handle has an interpreter and Lean origin"). The archived PASS
/// row: a contract over a Nat-typed parameter (mathematical `Int` sort bound to the
/// handle-typed `Param{0}` / `ResultSlot{0}`) validated and round-tripped at v43. WS1.2 types
/// every binding against its place, and `Ty::Handle` admits NO sort at this version (an opaque
/// runtime word has no machine sort), so the `Int` reading is refused on all three bindings.
/// Held exactly: the carrier is untouched (the summary still round-trips losslessly in
/// bin/json/msgpack at v43), and the mutation control (summary removed) is clean, so the
/// refusal is the binding rule's alone. When WS3 admits the handle place this trips and the
/// row flips back to PASS.
///
/// PASS (closed upstream by WS1.2, 31814e51; F-004): the archived GAP recorded that the SAME
/// clause bound at `BitVec(64)` — "Nat silently u64" on the contract surface — validated.
/// Now each of its three bindings is refused by name.
fn b5_20_contract_over_a_nat_parameter() {
    let module = nat_program_with_contract(ClauseSort::Int, ClausePlace::Param { index: 0 });
    let errors = validate_module(&module);
    let rt = roundtrip_all(&module);
    let kept = [&rt.binary, &rt.json, &rt.msgpack].iter().all(|trip| {
        trip.decoded.as_ref().is_some_and(|m| {
            m.function_by_name("nat_double")
                .and_then(|f| f.summary.as_ref())
                .is_some_and(|s| {
                    s.ensures.len() == 1
                        && s.decreases.len() == 1
                        && s.ensures[0].bindings.len() == 2
                        && s.ensures[0].bindings[0].1.sort == ClauseSort::Int
                })
        })
    });
    // Mutation control: the same module without the summary validates.
    let mut bare = module.clone();
    function_mut(&mut bare, "nat_double").summary = None;
    let bare_errors = validate_module(&bare);
    assert!(feature_ratified(
        "b5.contract_over_nat_param.int_sorted_bindings",
        Expect::refused_with(
            "InvalidFunctionSummary",
            &["ensures clause 0 binding 'n' has sort Int but Param 0 is handle<"],
        )
        .with_follow_ons(&["InvalidFunctionSummary", "InvalidFunctionSummary"]),
        Outcome::of(&errors).given(&[
            (
                "all three bindings refused as Int on a handle place",
                every_nat_binding_refused(&errors, &ClauseSort::Int),
            ),
            (
                "the summary still round-trips losslessly at v43",
                rt.lossless_production() && rt.binary_version == 43 && kept,
            ),
            (
                "without the summary the module validates",
                bare_errors.is_empty()
            ),
        ]),
        &format!(
            "Int-sorted contract over handle<Nat>: validate={errors:?} {} | summary kept in bin/json/msgpack={kept} | summary removed => {bare_errors:?}",
            rt.summary()
        ),
    ));

    // negative twin: bind `n` to a parameter the Nat -> Nat signature does not have. An
    // unresolved index keeps exactly its arity error (no sort refusal for that binding).
    let dangling = nat_program_with_contract(ClauseSort::Int, ClausePlace::Param { index: 3 });
    let errors = validate_module(&dangling);
    let arity = |e: &ValidationError| {
        matches!(
            e,
            ValidationError::InvalidFunctionSummary { detail, .. }
                if detail.contains("binding 'n' names parameter 3 but the signature declares 1 parameter(s)")
        )
    };
    assert!(feature_check(
        "b5.contract_over_nat_param.twin_dangling_param_binding",
        has(&errors, arity)
            && errors.iter().all(|e| {
                arity(e)
                    || matches!(
                        e,
                        ValidationError::InvalidFunctionSummary { detail, .. }
                            if detail.contains("binding 'result' has sort Int but ResultSlot 0 is handle<")
                    )
            }),
        &format!("{errors:?}"),
    ));

    // FLIPPED. Single change from the module above: sort `BitVec(64)`.
    let as_u64 = nat_program_with_contract(ClauseSort::BitVec(64), ClausePlace::Param { index: 0 });
    let errors = validate_module(&as_u64);
    assert!(feature_check(
        "b5.gap.clause_sort_bitvec64_accepted_on_nat_param",
        every_nat_binding_refused(&errors, &ClauseSort::BitVec(64)) && bare_errors.is_empty(),
        &format!(
            "closed upstream by WS1.2 (31814e51): ClauseSort::BitVec(64) bound to a handle<Nat> Param/ResultSlot => validate_module={errors:?}; summary removed => {bare_errors:?}"
        ),
    ));
}

/// Related (linkage, surfaced by the weak-declaration forgery row). PASS (closed upstream by
/// WS3.15, dc416921; F-058): the archived ratchet recorded that only `Linkage::External` could
/// be bodyless, so the v41 `Linkage::ExternalWeak` — "a declaration that may be absent at link
/// time" — was `EmptyFunction`. A bodyless weak import now validates AND is an FFI boundary:
/// without `target_info` it is exactly `TargetInfoRequired` naming the weak declaration, like
/// its `External` baseline. Negative twin (right reason): a `Ty::Func` global initialised with
/// `Constant::FnDef` of the weak import claims a callable non-null function and is exactly
/// `WeakDeclarationAsFnDef`, while the SAME global over the `External` import validates
/// (closeness control: one change, the linkage).
fn b5_21_related_gap_extern_weak_declaration() {
    let build = |linkage: Linkage, target_info: bool, fn_def_global: bool| {
        let mut m = Module::new("b5_extern_weak");
        if target_info {
            m.target_info = Some(target());
        }
        let id = push_c_declaration(&mut m, "optional_hook", None, vec![Ty::U64], vec![Ty::U64]);
        m.function_by_id_mut(id).unwrap().linkage = linkage;
        if fn_def_global {
            let sig = m.function_by_id(id).unwrap().ty;
            let mut g = global("OPTIONAL_HOOK_FN", Ty::Func(sig));
            g.initializer = Some(Constant::FnDef(id));
            m.globals.push(g);
        }
        m
    };
    let baseline = validate_module(&build(Linkage::External, true, false));
    let weak = validate_module(&build(Linkage::ExternalWeak, true, false));
    let is_boundary = |errors: &[ValidationError], needle: &str| {
        matches!(errors, [ValidationError::TargetInfoRequired { boundary }]
            if boundary.contains(needle) && boundary.contains("optional_hook"))
    };
    let weak_untargeted = validate_module(&build(Linkage::ExternalWeak, false, false));
    let strong_untargeted = validate_module(&build(Linkage::External, false, false));
    let strong_fn_def = validate_module(&build(Linkage::External, true, true));
    let weak_fn_def = validate_module(&build(Linkage::ExternalWeak, true, true));
    let twin_named = matches!(
        weak_fn_def.as_slice(),
        [ValidationError::WeakDeclarationAsFnDef { name, .. }] if name == "optional_hook"
    );
    assert!(feature_check(
        "b5.related.gap.extern_weak_bodyless_declaration_is_empty_function",
        baseline.is_empty()
            && weak.is_empty()
            && is_boundary(&weak_untargeted, "external_weak")
            && is_boundary(&strong_untargeted, "external")
            && strong_fn_def.is_empty()
            && twin_named,
        &format!(
            "closed upstream by WS3.15 (dc416921): External={baseline:?} ExternalWeak={weak:?}; \
             without target_info: ExternalWeak => {weak_untargeted:?}, External => \
             {strong_untargeted:?}; twin: Func global = FnDef(weak) => {weak_fn_def:?}, \
             FnDef(External) => {strong_fn_def:?}"
        ),
    ));
}

/// UNEXPECTED — a validator hole in the v43 origin invariant, found while reading
/// TB/validate.rs:11228-11255 (the archived ratchet): the function-return type check existed
/// ONLY under the `Inst::Return` arm. `Inst::CoroSuspend { value, .. }` is a terminator that
/// "returns `value` to the resumer" (normatively the macro-expansion GEP + Store + **Return**),
/// but its `value` was never compared with `FuncTy::returns`, and the handle transport rule
/// did not fire either, because no operand/result/inline type of that node reaches a handle
/// when `value` is a `Ptr`. So
///
/// ```text
/// fn forge(frame: Ptr, p: Ptr) -> Nat { coro_suspend frame[0] := 1, yield p }
/// fn user(frame: Ptr, p: Ptr) -> bool { trust_bignum_nat_is_zero(forge(frame, p)) }
/// ```
///
/// validated (also for codegen): the pinned runtime received an arbitrary pointer typed as a
/// `Nat`.
///
/// PASS (closed upstream by WS2.1, d8e403d4 + e1c09924; F-028): the yield is held to the
/// signature by the same check as `Return` (`check_return_values`). Named forgeries: the `Ptr`
/// yield is exactly `ReturnTypeMismatch { block: 0, expected: handle<"Nat", ..>, actual: "ptr" }`
/// under both `validate_module` and `validate_module_for_codegen`, and a `U64` yield exactly the
/// same with `actual: "u64"`. Mutation control: the `Return` spelling of the same laundering
/// gets the identical finding (one change, the terminator). Positive baseline: the same
/// `CoroSuspend` shape in a `-> u64` function yielding a `u64` through the `Ptr` frame
/// validates, so the refusal is about the yielded type, not the suspend. A `CoroSuspend`
/// yielding a REAL `Nat` stays `InvalidHandleUse` (transport-only).
fn b5_22_gap_coro_suspend_launders_a_pointer_into_a_nat() {
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Exit {
        Return,
        CoroSuspend,
    }
    // `ret` is the forge's return type; the `user` caller (which hands the result to the
    // pinned `is_zero`) exists only for a `-> Nat` forge.
    let build_ret = |value_ty: Ty, exit: Exit, ret: Ty| -> Module {
        let with_user = ret == nat();
        let mut mb = ModuleBuilder::new_with_target_info("b5_coro_forge", target());
        let decls = mb.declare_handle_runtime(nat_pin()).unwrap();
        let forge_sig = mb.add_func_type(vec![Ty::Ptr, value_ty.clone()], vec![ret]);
        let user_sig = mb.add_func_type(vec![Ty::Ptr, value_ty.clone()], vec![Ty::Bool]);
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        let forge_id = next_func_id(&m);
        let mut forge = Function::new(forge_id, "forge", forge_sig, BlockId::new(0));
        forge.producer = Some(Producer::TRust);
        forge.body_gate = Some(rust_gate());
        let mut bb0 = Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), Ty::Ptr)
            .with_param(ValueId::new(1), value_ty.clone());
        bb0.body.push(InstrNode::new(match exit {
            Exit::Return => Inst::Return {
                values: vec![ValueId::new(1)],
            },
            Exit::CoroSuspend => Inst::CoroSuspend {
                frame: ValueId::new(0),
                state_slot: 0,
                next_state: 1,
                value: ValueId::new(1),
            },
        }));
        forge.blocks.push(bb0);
        m.try_add_function(forge)
            .expect("Module::try_add_function: test fixture");
        if !with_user {
            return m;
        }

        let mut user = Function::new(next_func_id(&m), "user", user_sig, BlockId::new(0));
        user.producer = Some(Producer::TRust);
        user.body_gate = Some(rust_gate());
        let mut bb0 = Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), Ty::Ptr)
            .with_param(ValueId::new(1), value_ty);
        bb0.body.push(
            InstrNode::new(Inst::Call {
                callee: forge_id,
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
        );
        bb0.body.push(
            InstrNode::new(Inst::Call {
                callee: decls.entry("is_zero").unwrap(),
                args: vec![ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
        );
        bb0.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }));
        user.blocks.push(bb0);
        m.try_add_function(user)
            .expect("Module::try_add_function: test fixture");
        m
    };
    let build = |value_ty: Ty, exit: Exit| build_ret(value_ty, exit, nat());
    let named = |errors: &[ValidationError], want_actual: &str| {
        matches!(
            errors,
            [ValidationError::ReturnTypeMismatch { block: 0, expected, actual }]
                if *expected == nat().to_string() && actual == want_actual
        )
    };

    // Positive baseline: the same suspend shape, well typed (`-> u64` yielding a u64).
    let honest_u64 = build_ret(Ty::U64, Exit::CoroSuspend, Ty::U64);
    let positive = validate_module(&honest_u64);
    let positive_codegen = validate_module_for_codegen(&honest_u64);
    // Mutation control: the same laundering through `Return` gets the identical finding.
    let via_return = validate_module(&build(Ty::Ptr, Exit::Return));
    // Context: a CoroSuspend that yields a REAL Nat is refused (transport-only).
    let honest = validate_module(&build(nat(), Exit::CoroSuspend));
    let honest_refused = invalid_handle_use_naming(&honest, "CoroSuspend");

    let forged_ptr = build(Ty::Ptr, Exit::CoroSuspend);
    let forged_u64 = build(Ty::U64, Exit::CoroSuspend);
    let ptr_errors = validate_module(&forged_ptr);
    let ptr_codegen = validate_module_for_codegen(&forged_ptr);
    let u64_errors = validate_module(&forged_u64);
    let rt = roundtrip_all(&forged_ptr);
    assert!(feature_check(
        "b5.gap.UNEXPECTED.coro_suspend_value_not_checked_against_return_type_forges_a_nat",
        positive.is_empty()
            && positive_codegen.is_empty()
            && named(&ptr_errors, "ptr")
            && named(&ptr_codegen, "ptr")
            && named(&u64_errors, "u64")
            && via_return == ptr_errors
            && honest_refused
            && rt.lossless_production(),
        &format!(
            "closed upstream by WS2.1 (d8e403d4/e1c09924): `-> u64` suspend yielding a u64 => \
             validate_module={positive:?} validate_module_for_codegen={positive_codegen:?}; \
             CoroSuspend yielding a Ptr from `-> Nat`: validate_module={ptr_errors:?} \
             validate_module_for_codegen={ptr_codegen:?}; yielding a U64: {u64_errors:?}; \
             via Return => {via_return:?}; CoroSuspend yielding a real Nat => \
             InvalidHandleUse={honest_refused}; the refused module still round-trips (wire v{})",
            rt.binary_version
        ),
    ));
}

// ===========================================================================
// WS3.22 (F-060): `Dealloc` cannot state a free — the ratified workaround
// (G18-1) and its one open edge
// ===========================================================================

/// Rows `trust-ir-self-declared/dealloc-cannot-state-a-free` and
/// `consumer-trust-cg/18-dealloc`. The format half is a ratification plus a refusal:
/// `Dealloc { ptr }` names neither the `AllocOrigin` whose runtime owns the region nor the
/// layout being released, so it is wire-legal, interpreter-executable, and refused for
/// codegen by name; the free is spelled as a CALL to the owning runtime's pinned release
/// entry point. The open edge: that call is opaque to the interpreter unless the callee is
/// KNOWN to be a release — `trust_ir_build::pinned_release_entry_points()` is the ONE place
/// that names them (`trust_bignum_nat_drop`, `clean_dec`), and the reference host model
/// (`PinnedHandleHost`, WS2.13) keys its dead-marking on it. `RustHeap` frees
/// (`__rust_dealloc`) are pinned by no table and stay opaque: stated, not hidden.
fn b5_23_dealloc_cannot_state_a_free() {
    use trust_ir::inst::AllocOrigin;
    use trust_ir::interpret::{
        HostCalls, HostRcOp, HostState, InterpretErrorCode, InterpretResult, Interpreter,
    };
    use trust_ir_build::{
        PinnedReleaseSubject, pinned_release_entry_for_symbol, pinned_release_entry_points,
    };

    let gate = |module: &mut Module| {
        for f in &mut module.functions {
            if !f.is_declaration() {
                f.body_gate = Some(rust_gate());
            }
        }
    };
    // `f() -> u64 { p = HeapAlloc(RustHeap, u64); *p = 7; v = *p; Dealloc p; ret v }`
    let dealloc_module = || -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_dealloc", target());
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", sig);
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, p, seven);
        let v = fb.load(Ty::U64, p);
        fb.dealloc(p);
        fb.ret(vec![v]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        gate(&mut m);
        m
    };
    // The SAME free through the pinned release entry point of the owning runtime, with
    // `drops` releases of the one handle:
    // `f() -> bool { n = from_u64(7); z = is_zero(n); drop(n) x drops; ret z }`
    let drop_module = |drops: usize| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_drop", target());
        let decls = mb
            .declare_handle_runtime_roles(nat_pin(), &["from_u64", "is_zero", "drop"])
            .unwrap();
        let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
        let mut fb = mb.function("f", sig);
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let seven = fb.uconst(Ty::U64, 7);
        let n = fb.call(decls.entry("from_u64").unwrap(), vec![seven]);
        let z = fb.call(decls.entry("is_zero").unwrap(), vec![n]);
        for _ in 0..drops {
            fb.call_void(decls.entry("drop").unwrap(), vec![n]);
        }
        fb.ret(vec![z]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        gate(&mut m);
        m
    };
    // A `CleanHeap` cell freed through the pinned `clean_dec`, `decs` times.
    let clean_dec_module = |decs: usize| -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_clean_dec", target());
        let release = pinned_release_entry_for_symbol("clean_dec").expect("pinned");
        let dec_ty = mb.add_func_type(
            release.func_ty.params.clone(),
            release.func_ty.returns.clone(),
        );
        let dec = mb.declare_function(release.symbol, dec_ty);
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", sig);
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::CleanHeap);
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, p, seven);
        let v = fb.load(Ty::U64, p);
        for _ in 0..decs {
            fb.call_void(dec, vec![p]);
        }
        fb.ret(vec![v]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        gate(&mut m);
        m
    };
    // The unpinned Rust free: a bodyless `__rust_dealloc(ptr, size, align)`.
    let rust_dealloc_module = || -> Module {
        let mut mb = ModuleBuilder::new_with_target_info("b5_rust_dealloc", target());
        let dealloc_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Usize, Ty::Usize], vec![]);
        let dealloc = mb.declare_function("__rust_dealloc", dealloc_ty);
        let sig = mb.add_func_type(vec![], vec![Ty::U64]);
        let mut fb = mb.function("f", sig);
        let bb0 = fb.create_block();
        fb.switch_to_block(bb0);
        let p = fb.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let seven = fb.uconst(Ty::U64, 7);
        fb.store(Ty::U64, p, seven);
        let v = fb.load(Ty::U64, p);
        let size = fb.uconst(Ty::Usize, 8);
        let align = fb.uconst(Ty::Usize, 8);
        fb.call_void(dealloc, vec![p, size, align]);
        fb.ret(vec![v]);
        fb.build();
        let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
        gate(&mut m);
        m
    };
    let run_under =
        |module: &Module, host: &dyn HostCalls| -> Result<Vec<InterpretValue>, String> {
            Interpreter::with_module(module)
                .with_host(host)
                .execute_func(func_id(module, "f"), Vec::new())
                .map(|o| o.returns)
                .map_err(|e| format!("{:?}: {e}", e.code))
        };

    // ---- the G18-1 state ----------------------------------------------------------------
    let dealloc = dealloc_module();
    let plain = validate_module(&dealloc);
    let executed = run_nullary(&dealloc, "f");
    let codegen = validate_module_for_codegen(&dealloc);
    let seven = executed
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128)
        == Some(7);
    assert!(feature_check(
        "b5.dealloc_cannot_state_a_free",
        plain.is_empty()
            && seven
            && matches!(
                codegen.as_slice(),
                [ValidationError::UnlowerableForCodegen { inst: "Dealloc", detail, .. }]
                    if detail.contains("AllocOrigin") && detail.contains("layout")
            ),
        &format!(
            "G18-1 (ratified 2026-09-01, kept by WS3.22): HeapAlloc(RustHeap)+Dealloc => \
             validate_module={plain:?}, interpreter f()={executed:?}, \
             validate_module_for_codegen={codegen:?}"
        ),
    ));

    // Close twin: the same free spelled as a call to the pinned release entry point of the
    // owning runtime validates AND is lowerable — for a Nat (`trust_bignum_nat_drop`) and for
    // a CleanHeap cell (`clean_dec`); each callee is a row of the one-place table.
    let drop_once = drop_module(1);
    let clean = clean_dec_module(1);
    let drop_plain = validate_module(&drop_once);
    let drop_codegen = validate_module_for_codegen(&drop_once);
    let clean_plain = validate_module(&clean);
    let clean_codegen = validate_module_for_codegen(&clean);
    let release_calls = |m: &Module| -> usize {
        m.functions
            .iter()
            .flat_map(|f| f.blocks.iter())
            .flat_map(|b| b.body.iter())
            .filter(|node| match &node.inst {
                Inst::Call { callee, .. } => m
                    .function_by_id(*callee)
                    .is_some_and(|c| pinned_release_entry_for_symbol(&c.name).is_some()),
                _ => false,
            })
            .count()
    };
    assert!(feature_check(
        "b5.dealloc_cannot_state_a_free.twin_free_spelled_as_pinned_release_is_lowerable",
        drop_plain.is_empty()
            && drop_codegen.is_empty()
            && clean_plain.is_empty()
            && clean_codegen.is_empty()
            && release_calls(&drop_once) == 1
            && release_calls(&clean) == 1,
        &format!(
            "from_u64+is_zero+trust_bignum_nat_drop => validate_module={drop_plain:?} \
             validate_module_for_codegen={drop_codegen:?}; HeapAlloc(CleanHeap)+clean_dec => \
             validate_module={clean_plain:?} validate_module_for_codegen={clean_codegen:?}"
        ),
    ));

    // ---- the ONE place --------------------------------------------------------------
    let table: Vec<(&str, &PinnedReleaseSubject)> = pinned_release_entry_points()
        .iter()
        .map(|e| (e.symbol, &e.subject))
        .collect();
    let named_once = table
        == vec![
            (
                "trust_bignum_nat_drop",
                &PinnedReleaseSubject::Handle(HandleTy::new("Nat", "trust_bignum::Nat")),
            ),
            (
                "clean_dec",
                &PinnedReleaseSubject::RcCell(AllocOrigin::CleanHeap),
            ),
        ]
        && pinned_release_entry_points().iter().all(|e| {
            e.func_ty.params.len() == 1 && e.func_ty.returns.is_empty() && !e.func_ty.is_vararg
        })
        && nat_pin()
            .release_entry()
            .is_some_and(|e| e.symbol == "trust_bignum_nat_drop")
        && [
            "__rust_dealloc",
            "free",
            "clean_inc",
            "trust_bignum_nat_add",
        ]
        .iter()
        .all(|s| pinned_release_entry_for_symbol(s).is_none());
    assert!(feature_check(
        "b5.release_entry_points_named_once",
        named_once,
        &format!(
            "trust_ir_build::pinned_release_entry_points() = {table:?}; \
             __rust_dealloc/free/clean_inc/add are not releases"
        ),
    ));

    // Negative twin: the unpinned RustHeap free stays OPAQUE — it validates and is lowerable
    // (an ordinary call), the table does not name it, and neither without a host nor under
    // the reference model does the interpreter serve it (fail closed by name, never a silent
    // no-op).
    let rust_free = rust_dealloc_module();
    let rust_plain = validate_module(&rust_free);
    let rust_codegen = validate_module_for_codegen(&rust_free);
    let rust_run = Interpreter::with_module(&rust_free)
        .execute_func(func_id(&rust_free, "f"), Vec::new())
        .map(|o| o.returns);
    let rust_hosted = run_under(&rust_free, &PinnedHandleHost::new());
    let opaque = matches!(
        &rust_run,
        Err(e) if e.code == InterpretErrorCode::UnsupportedCall
            && e.unhosted_callee() == Some("__rust_dealloc")
    ) && rust_hosted
        .as_ref()
        .is_err_and(|m| m.starts_with("UnsupportedCall") && m.contains("__rust_dealloc"));
    assert!(feature_check(
        "b5.release_entry_points_named_once.twin_rust_heap_free_is_opaque",
        rust_plain.is_empty()
            && rust_codegen.is_empty()
            && pinned_release_entry_for_symbol("__rust_dealloc").is_none()
            && opaque,
        &format!(
            "HeapAlloc(RustHeap)+call __rust_dealloc => validate_module={rust_plain:?} \
             validate_module_for_codegen={rust_codegen:?}; interpreter (no host) => \
             {rust_run:?}; under PinnedHandleHost => {rust_hosted:?}"
        ),
    ));

    // ---- the open edge, executable: a pinned release is a dead-marking step ------------
    /// The MUTANT of the reference model: a call to a symbol the one-place table names is a
    /// NO-OP; everything else is `PinnedHandleHost`. What a host that does not key its
    /// dead-marking on the table would do.
    struct NoOpRelease;
    impl HostCalls for NoOpRelease {
        fn call(
            &self,
            callee: &Function,
            sig: &FuncTy,
            args: &[InterpretValue],
            host: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            if pinned_release_entry_for_symbol(&callee.name).is_some() {
                return Some(Ok(Vec::new()));
            }
            PinnedHandleHost::new().call(callee, sig, args, host)
        }
        fn rc_op(&self, callee: &Function, sig: &FuncTy) -> Option<HostRcOp> {
            if pinned_release_entry_for_symbol(&callee.name).is_some() {
                return None;
            }
            PinnedHandleHost::new().rc_op(callee, sig)
        }
    }
    let marking = PinnedHandleHost::new();
    let drop_twice = drop_module(2);
    let dec_twice = clean_dec_module(2);
    let twice_plain = validate_module(&drop_twice);
    let dec_twice_plain = validate_module(&dec_twice);
    let single_run = run_under(&drop_once, &marking);
    let double_run = run_under(&drop_twice, &marking);
    let mutant_run = run_under(&drop_twice, &NoOpRelease);
    let dec_single_run = run_under(&clean, &marking);
    let dec_double_run = run_under(&dec_twice, &marking);
    let dec_mutant_run = run_under(&dec_twice, &NoOpRelease);
    let single_clean = single_run
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(|v| v.as_bool())
        == Some(false);
    let double_faults = matches!(
        &double_run,
        Err(m) if m.starts_with("UndefinedBehavior")
            && m.contains("used after release")
            && m.contains("trust_bignum_nat_drop")
    );
    let dec_single_clean = dec_single_run
        .as_ref()
        .ok()
        .and_then(|v| v.first())
        .and_then(common::as_u128)
        == Some(7);
    let dec_double_faults = matches!(
        &dec_double_run,
        Err(m) if m.starts_with("UndefinedBehavior")
            && m.contains("freed allocation")
            && m.contains("clean_dec")
    );
    assert!(feature_check(
        "b5.double_drop_faults_under_a_release_marking_host",
        twice_plain.is_empty()
            && dec_twice_plain.is_empty()
            && single_clean
            && double_faults
            && mutant_run == single_run
            && dec_single_clean
            && dec_double_faults
            && dec_mutant_run == dec_single_run,
        &format!(
            "first executable witness of TRUST.md item 9(c), host-assisted (a trusted model, \
             never in-format evidence): the double-drop module validates ({twice_plain:?}); \
             one drop => {single_run:?}; two drops under PinnedHandleHost => {double_run:?}; \
             mutation control, a host treating drop as a no-op => {mutant_run:?}; CleanHeap \
             twin (item 13): one clean_dec => {dec_single_run:?}; two => {dec_double_run:?}; \
             mutant => {dec_mutant_run:?}"
        ),
    ));
}
#[test]
fn two_language_b5() {
    common::run_target(
        "b5",
        &[
            (
                "b5_01_handle_type_and_pinned_declarations",
                b5_01_handle_type_and_pinned_declarations,
            ),
            (
                "b5_02_clean_nat_function_called_from_rust_validates",
                b5_02_clean_nat_function_called_from_rust_validates,
            ),
            (
                "b5_03_wire_v43_and_four_format_round_trip",
                b5_03_wire_v43_and_four_format_round_trip,
            ),
            (
                "b5_04_every_forgery_is_a_named_error",
                b5_04_every_forgery_is_a_named_error,
            ),
            (
                "b5_05_derived_mul_is_a_defined_function",
                b5_05_derived_mul_is_a_defined_function,
            ),
            (
                "b5_06_laundering_a_pointer_into_a_nat_is_refused",
                b5_06_laundering_a_pointer_into_a_nat_is_refused,
            ),
            (
                "b5_07_function_pointer_forgeries_of_a_nat",
                b5_07_function_pointer_forgeries_of_a_nat,
            ),
            (
                "b5_10_gap_unpinned_nat_entry_points",
                b5_10_gap_unpinned_nat_entry_points,
            ),
            (
                "b5_15_pin_table_gap_is_validator_only",
                b5_15_pin_table_gap_is_validator_only,
            ),
            (
                "b5_16_one_nat_carrier_across_producers",
                b5_16_one_nat_carrier_across_producers,
            ),
            (
                "b5_11_handle_as_an_aggregate_payload",
                b5_11_handle_as_an_aggregate_payload,
            ),
            ("b5_12_handle_in_memory", b5_12_handle_in_memory),
            (
                "b5_13_gap_cross_crate_user_function_over_nat",
                b5_13_gap_cross_crate_user_function_over_nat,
            ),
            (
                "b5_14_reference_interpreter_executes_handles_host_assisted",
                b5_14_reference_interpreter_executes_handles_host_assisted,
            ),
            (
                "b5_20_contract_over_a_nat_parameter",
                b5_20_contract_over_a_nat_parameter,
            ),
            (
                "b5_21_related_gap_extern_weak_declaration",
                b5_21_related_gap_extern_weak_declaration,
            ),
            (
                "b5_22_gap_coro_suspend_launders_a_pointer_into_a_nat",
                b5_22_gap_coro_suspend_launders_a_pointer_into_a_nat,
            ),
            (
                "b5_23_dealloc_cannot_state_a_free",
                b5_23_dealloc_cannot_state_a_free,
            ),
        ],
    );
}
