// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.20 (F-057): the validator's rules for the bulk-memory pair and the bit
// intrinsics. Positive fixture; negative twins each one mutation away with a
// NAMED refusal; mutation controls showing the new rules cause the refusal
// and do not over-refuse. Companion of `crates/trust-ir/tests/bulk_memory_ops.rs`
// (the interpreter half) and the Lean `ExecutableFixtures` locks.

use trust_ir::inst::{BinOp, Inst, UnOp};
use trust_ir::proof::{
    ObligationKind, ObligationSite, ProofAnnotation, ProofObligation, ProofStatus,
};
use trust_ir::value::BlockId;
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::validate::codegen_lowerability_errors;
use trust_ir_build::{ModuleBuilder, TRUSTED_HANDLE_RUNTIMES, ValidationError, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn names(errors: &[ValidationError]) -> Vec<String> {
    errors
        .iter()
        .map(|e| {
            let s = format!("{e:?}");
            s.split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .next()
                .unwrap_or("")
                .to_string()
        })
        .collect()
}

fn assert_refused(errors: &[ValidationError], variant: &str, needle: &str) {
    assert!(
        errors
            .iter()
            .any(|e| format!("{e:?}").starts_with(variant) && format!("{e:?}").contains(needle)),
        "expected `{variant}` mentioning `{needle}`, got {errors:#?}"
    );
}

/// `copy(dst, src, n)`: the positive fixture. `count_ty` is the byte-count
/// type (`Usize` under target info, `U64` without); `with_target` picks the
/// module flavour.
fn memcopy_module(with_target: bool, count_ty: Ty, overlap: bool) -> Module {
    let mut mb = if with_target {
        ModuleBuilder::new_with_target_info("bulk", target())
    } else {
        ModuleBuilder::new("bulk")
    };
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, count_ty.clone()], vec![]);
    let mut fb = mb.function("copy", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let dst = fb.add_block_param(entry, Ty::Ptr);
    let src = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, count_ty);
    fb.memcopy(dst, src, n, overlap);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn memset_module(with_target: bool, byte_ty: Ty, count_ty: Ty) -> Module {
    let mut mb = if with_target {
        ModuleBuilder::new_with_target_info("bulk", target())
    } else {
        ModuleBuilder::new("bulk")
    };
    let ft = mb.add_func_type(vec![Ty::Ptr, byte_ty.clone(), count_ty.clone()], vec![]);
    let mut fb = mb.function("fill", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let dst = fb.add_block_param(entry, Ty::Ptr);
    let byte = fb.add_block_param(entry, byte_ty);
    let n = fb.add_block_param(entry, count_ty);
    fb.memset(dst, byte, n);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// MemCopy / MemSet operand typing
// ---------------------------------------------------------------------------

#[test]
fn memcopy_and_memset_validate_with_the_exact_count_and_fill_types() {
    // With target info the count is exactly `Usize`; without, exactly `U64`.
    for (with_target, count_ty) in [(true, Ty::Usize), (false, Ty::U64)] {
        for overlap in [false, true] {
            let module = memcopy_module(with_target, count_ty.clone(), overlap);
            let errors = validate_module(&module);
            assert!(
                errors.is_empty(),
                "memcopy({with_target}, {count_ty}, {overlap}): {errors:#?}"
            );
            // The pair is lowerable: the format states everything a backend
            // needs (two addresses, a byte count, the overlap contract), so it
            // is NOT on the `UnlowerableForCodegen` list beside `Dealloc`.
            // (Only the lowerability leg is asserted: the full codegen
            // validator also demands a v41 body licence, which this fixture
            // does not claim, and subset admission is a separate contract.)
            assert!(
                codegen_lowerability_errors(&module).is_empty(),
                "memcopy is not on the codegen-unlowerable list"
            );
        }
        let module = memset_module(with_target, Ty::U8, count_ty.clone());
        let errors = validate_module(&module);
        assert!(
            errors.is_empty(),
            "memset({with_target}, {count_ty}): {errors:#?}"
        );
    }
}

/// Negative twins: the count type is EXACT — `U64` under target info (where
/// `Usize` is the spelling) and `Usize` without it are both refused, as is any
/// other integer, each as `OperandTypeMismatch { role: "bytes" }`.
#[test]
fn memcopy_count_type_is_exact_negative_twins() {
    for (with_target, bad) in [
        (true, Ty::U64),
        (true, Ty::U32),
        (true, Ty::Isize),
        (false, Ty::Usize),
        (false, Ty::U32),
        (false, Ty::I64),
        (false, Ty::Bool),
    ] {
        let errors = validate_module(&memcopy_module(with_target, bad.clone(), false));
        assert_refused(&errors, "OperandTypeMismatch", "role: \"bytes\"");
        assert_refused(&errors, "OperandTypeMismatch", "op: \"memcopy\"");
        let errors = validate_module(&memset_module(with_target, Ty::U8, bad.clone()));
        assert_refused(&errors, "OperandTypeMismatch", "op: \"memset\"");
    }
}

/// Negative twin: the fill byte is exactly `U8`.
#[test]
fn memset_fill_byte_must_be_u8() {
    for bad in [Ty::I8, Ty::U16, Ty::U64, Ty::Bool] {
        let errors = validate_module(&memset_module(false, bad.clone(), Ty::U64));
        assert_refused(&errors, "OperandTypeMismatch", "role: \"byte\"");
        assert_refused(&errors, "OperandTypeMismatch", "expected: \"u8\"");
    }
}

/// Negative twin: `dst` / `src` must be pointer-like (`OperandNotPointer`).
#[test]
fn memcopy_pointers_must_be_pointer_like() {
    let mut mb = ModuleBuilder::new("bulk");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function("copy", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let dst = fb.add_block_param(entry, Ty::U64);
    let src = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    fb.memcopy(dst, src, n, false);
    fb.memcopy(src, dst, n, false);
    fb.ret(vec![]);
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    let pointer_refusals = errors
        .iter()
        .filter(|e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "memcopy"))
        .count();
    assert_eq!(
        pointer_refusals, 2,
        "one refusal per non-pointer operand: {errors:#?}"
    );
    // Mutation control: a `Ref`/`RefMut`/raw-pointer operand IS pointer-like.
    let mut mb = ModuleBuilder::new("bulk");
    let ft = mb.add_func_type(
        vec![
            Ty::RefMut(Box::new(Ty::U8)),
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::U64,
        ],
        vec![],
    );
    let mut fb = mb.function("copy", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let dst = fb.add_block_param(entry, Ty::RefMut(Box::new(Ty::U8)));
    let src = fb.add_block_param(entry, Ty::PtrConst(Box::new(Ty::U8)));
    let n = fb.add_block_param(entry, Ty::U64);
    fb.memcopy(dst, src, n, false);
    fb.ret(vec![]);
    fb.build();
    assert!(validate_module(&mb.build().expect("ModuleBuilder::build: test fixture")).is_empty());
}

/// A `MemCopy` targeting a sealed handle slot is refused as `InvalidHandleUse`
/// (WS3.7 forbidden use): the nominal transport rule admits copy / select /
/// exact-typed call / return / branch only, and a bulk copy is none of them.
#[test]
fn memcopy_of_a_sealed_handle_slot_is_invalid_handle_use() {
    let pin = TRUSTED_HANDLE_RUNTIMES
        .iter()
        .find(|pin| pin.runtime == "trust_bignum::Nat")
        .expect("v1 pins trust_bignum::Nat");
    let mut mb = ModuleBuilder::new_with_target_info("bulk_handle", target());
    let decls = mb.declare_handle_runtime(pin).unwrap();
    let nat = decls.handle.clone();
    let ft = mb.add_func_type(vec![nat.clone(), nat.clone(), Ty::Usize], vec![]);
    let mut fb = mb.function("copy_handle", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let dst = fb.add_block_param(entry, nat.clone());
    let src = fb.add_block_param(entry, nat);
    let n = fb.add_block_param(entry, Ty::Usize);
    fb.memcopy(dst, src, n, false);
    fb.ret(vec![]);
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert_refused(
        &errors,
        "InvalidHandleUse",
        "`MemCopy` cannot produce, consume",
    );
    // A handle is one pointer word but NOT pointer-like, so the typing rule
    // refuses each operand independently as well (both are named).
    assert_eq!(
        errors
            .iter()
            .filter(
                |e| matches!(e, ValidationError::OperandNotPointer { op, .. } if op == "memcopy")
            )
            .count(),
        2,
        "{errors:#?}"
    );
    // The same module with `Ptr` operands is the mutation control (validates).
    assert!(validate_module(&memcopy_module(true, Ty::Usize, false)).is_empty());
}

/// The obligation leg: an `InBounds` claim on the MemCopy node, backed by a
/// `ProofRef` to a `MemorySafety` obligation SITED on that node, BINDS (the
/// fast-1 rule: kind-compatible, exact site); the same reference sited one
/// instruction away is `ProofRefSiteMismatch`. Binding is not authority: the
/// row is `Pending` and no certificate is replayed, so the ONLY remaining
/// finding on the exact site is `ProofRefUnresolved { missing: false }` —
/// the claim stays unbacked until a kernel-replayed certificate exists,
/// exactly as for every other `ProofRef` (`fast1_proof_ref.rs`).
#[test]
fn memcopy_in_bounds_claim_is_backed_by_a_sited_memory_safety_obligation() {
    let build = |site_index: u32| {
        let mut mb = ModuleBuilder::new("bulk");
        let obligation = mb
            .add_proof_obligation(|id| {
                ProofObligation::new(
                    id,
                    ObligationKind::MemorySafety,
                    ProofStatus::Pending,
                    "memcopy dst/src ranges in bounds",
                )
            })
            .expect("a fresh obligation id");
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
        let mut fb = mb.function("copy", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let dst = fb.add_block_param(entry, Ty::Ptr);
        let src = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::U64);
        fb.memcopy(dst, src, n, false);
        fb.annotate_last(ProofAnnotation::InBounds).unwrap();
        fb.annotate_last(ProofAnnotation::ProofRef(obligation))
            .unwrap();
        fb.ret(vec![]);
        let func = fb.build();
        assert!(mb.set_obligation_site(
            obligation,
            ObligationSite {
                function: func,
                block: BlockId::new(0),
                inst_index: site_index,
            }
        ));
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let errors = validate_module(&build(0));
    assert!(
        !errors.is_empty()
            && errors.iter().all(|e| matches!(
                e,
                ValidationError::ProofRefUnresolved { missing: false, .. }
            )),
        "sited on the memcopy node the reference binds and only authority is missing: \
         {errors:#?}"
    );
    let errors = validate_module(&build(1));
    assert_refused(&errors, "ProofRefSiteMismatch", "");
}

// ---------------------------------------------------------------------------
// Bit intrinsics: integer-only / float-only typing
// ---------------------------------------------------------------------------

fn unop_module(op: UnOp, ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("bits");
    let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let x = fb.add_block_param(entry, ty.clone());
    let r = fb.unop(op, ty, x);
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn binop_module(op: BinOp, ty: Ty) -> Module {
    let mut mb = ModuleBuilder::new("bits");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let x = fb.add_block_param(entry, ty.clone());
    let y = fb.add_block_param(entry, ty.clone());
    let r = fb.binop(op, ty, x, y);
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn bit_intrinsics_validate_at_integer_types_and_vectors() {
    let v4 = Ty::Vector(Box::new(Ty::U32), 4);
    for ty in [Ty::U8, Ty::I32, Ty::U128, Ty::Usize, v4.clone()] {
        for op in [UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
            let errors = validate_module(&unop_module(op, ty.clone()));
            assert!(errors.is_empty(), "{op} at {ty}: {errors:#?}");
        }
        for op in [BinOp::RotL, BinOp::RotR] {
            let errors = validate_module(&binop_module(op, ty.clone()));
            assert!(errors.is_empty(), "{op} at {ty}: {errors:#?}");
        }
    }
    for ty in [Ty::F32, Ty::F64, Ty::Vector(Box::new(Ty::F32), 4)] {
        let errors = validate_module(&binop_module(BinOp::FCopySign, ty.clone()));
        assert!(errors.is_empty(), "fcopysign at {ty}: {errors:#?}");
    }
}

/// NEGATIVE TWIN (the roadmap's): `ctlz f32` is refused as
/// `BinOpRequiresInteger` — and so is every other bit intrinsic and rotate at a
/// float type, while `fcopysign` at an integer type is `BinOpRequiresFloat`.
#[test]
fn ctlz_on_f32_is_refused_as_binop_requires_integer() {
    let errors = validate_module(&unop_module(UnOp::CtLz, Ty::F32));
    assert_refused(&errors, "BinOpRequiresInteger", "ctlz");
    for op in [UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
        let errors = validate_module(&unop_module(op, Ty::F64));
        assert_refused(&errors, "BinOpRequiresInteger", &op.to_string());
    }
    for op in [BinOp::RotL, BinOp::RotR] {
        let errors = validate_module(&binop_module(op, Ty::F32));
        assert_refused(&errors, "BinOpRequiresInteger", &op.to_string());
    }
    let errors = validate_module(&binop_module(BinOp::FCopySign, Ty::U32));
    assert_refused(&errors, "BinOpRequiresFloat", "fcopysign");
    // Mutation control: the refusal names the new op, and `ctpop f32` (the
    // pre-existing rule) is refused the same way — one rule, not a new class.
    let errors = validate_module(&unop_module(UnOp::CtPop, Ty::F32));
    assert_refused(&errors, "BinOpRequiresInteger", "ctpop");
    assert!(!names(&errors).iter().any(|n| n == "BinOpRequiresFloat"));
}

/// The bulk ops carry no result: a result-bearing `MemCopy` node is refused
/// by the arity rule like a result-bearing `Store`.
#[test]
fn bulk_ops_produce_no_result() {
    let mut module = memcopy_module(false, Ty::U64, false);
    let node = &mut module.functions[0].blocks[0].body[0];
    assert!(matches!(node.inst, Inst::MemCopy { .. }));
    node.results.push(trust_ir::value::ValueId::new(9));
    let errors = validate_module(&module);
    assert!(!errors.is_empty(), "a result on a memcopy must be refused");
}

// ---------------------------------------------------------------------------
// A wire identity since the INST wire batch (v51)
// ---------------------------------------------------------------------------

/// The nine WS3.20 variants carry the tags the INST wire batch landed (v51):
/// `MemCopy` / `MemSet` at Inst tags 61 / 62, the bit intrinsics at UnOp tags
/// 9..=12, the rotates and copySign at BinOp tags 23..=25. Before it the
/// canonical writer panicked on each, so every digest-keyed entry point had
/// to refuse the module by name (`ModuleHasNoWireIdentity`); now each module
/// has a wire identity — no blocker, a stable digest, a lossless binary round
/// trip at the batch version — and the linked walk hashes it like any other.
#[test]
fn a_module_carrying_a_ws3_20_op_has_a_wire_identity() {
    use trust_ir::proof::RejectingModuleProofAuthority;
    use trust_ir_build::{ModuleSet, validate_linked_module, wire_identity_blocker};

    let mut modules: Vec<(String, Module)> = vec![
        ("memcopy".into(), memcopy_module(true, Ty::Usize, false)),
        ("memmove".into(), memcopy_module(true, Ty::Usize, true)),
        ("memset".into(), memset_module(true, Ty::U8, Ty::Usize)),
    ];
    for op in [UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
        modules.push((op.to_string(), unop_module(op, Ty::U32)));
    }
    for op in [BinOp::RotL, BinOp::RotR] {
        modules.push((op.to_string(), binop_module(op, Ty::U32)));
    }
    modules.push(("fcopysign".into(), binop_module(BinOp::FCopySign, Ty::F64)));

    let none = ModuleSet::new(std::iter::empty::<&Module>());
    for (label, module) in &modules {
        assert!(
            validate_module(module).is_empty(),
            "{label}: the structural validator admits the module"
        );
        assert_eq!(
            wire_identity_blocker(module),
            None,
            "{label}: the op has a wire tag"
        );
        let digest = module.stable_digest();
        assert_eq!(module.stable_digest(), digest, "{label}");
        // Root of a linked walk: hashed and validated, nothing refused.
        let linked = validate_linked_module(module, &none, &RejectingModuleProofAuthority);
        assert!(linked.is_ok(), "{label}: {:?}", linked.errors());
        #[cfg(feature = "binary")]
        {
            let bytes =
                trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture");
            let (decoded, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
                .unwrap_or_else(|e| panic!("{label}: {e:?}"));
            assert_eq!(
                version.get(),
                trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION,
                "{label}: the op selects the batch version"
            );
            assert_eq!(&decoded, module, "{label}");
            assert_eq!(decoded.stable_digest(), digest, "{label}");
        }
    }

    // Control: the pre-existing ops on the same fixtures keep their older
    // header — the batch raises only a module that carries one of its tags.
    for module in [
        unop_module(UnOp::CtPop, Ty::U32),
        binop_module(BinOp::Shl, Ty::U32),
        binop_module(BinOp::FMin, Ty::F64),
    ] {
        assert!(wire_identity_blocker(&module).is_none());
        let _ = module.stable_digest();
        #[cfg(feature = "binary")]
        {
            let bytes = trust_ir::binary::serialize_module(&module)
                .expect("serialize_module: test fixture");
            let (_, version) = trust_ir::binary::deserialize_module_with_wire_version(&bytes)
                .expect("pre-batch op decodes");
            assert!(version.get() < trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION);
        }
    }
}
