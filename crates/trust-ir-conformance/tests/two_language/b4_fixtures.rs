//! Fixtures of the b4 cross-crate rows, shared by the `two_language_b4`
//! target and by `trust-ir-cli`'s `two_language_cli` target (which links the
//! pair with the real CLI). Only trust-ir / trust-ir-build are used here.
#![allow(dead_code)]

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofCertificate, ProofEvidence,
    ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    BodyGate, Endianness, ExternRef, FunctionSummary, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::ModuleBuilder;

pub const SCALE: &str = "dep_scale";
pub const ADDMUL: &str = "dep_addmul";

pub fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

pub fn scale_clause() -> ProofFormula {
    let mut clause = ProofFormula::smtlib2("(>= result 0)", "Bool");
    clause.bindings = vec![(
        "result".to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::ResultSlot { index: 0 },
        },
    )];
    clause
}

pub fn addmul_clause() -> ProofFormula {
    ProofFormula::smtlib2("(<= 1 2)", "Bool")
}

pub fn scale_contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(scale_clause())
}

pub fn addmul_contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["a".to_string(), "b".to_string()])
        .ensuring(addmul_clause())
}

/// A kernel-CERTIFIED Postcondition `id`, scoped to `function`, stating
/// `clause`, with the `CleanCic` certificate the in-process kernel re-checks.
/// Minted with `module` in scope: since WS1.1 (0aeae341) a free-name nonneg
/// clause grounds only once its binding resolves to an unsigned IR place.
pub fn certified_postcondition(
    module: &Module,
    id: u32,
    function: FuncId,
    clause: ProofFormula,
    text: &str,
) -> (ProofObligation, ProofCertificate) {
    let obligation = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        text,
    )
    .with_function(function)
    .with_formula(clause);
    let certificate = contract_clean_cic_certificate_in(module, &obligation, "b4-contract-prover")
        .expect("the clause is kernel-provable over its bound u64 place");
    (obligation, certificate)
}

/// The MIXED dependency crate. `factor` is `dep_scale`'s multiplier (3 in the
/// honest build); a rebuilt dependency with another factor is "the same crate,
/// one byte different".
pub fn build_dep(factor: u128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("b4_dep", target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);

    let scale = {
        let mut fb = mb.function(SCALE, unary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("b4_dep::scale");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let k = fb.uconst(Ty::U64, factor);
        let out = fb.mul(Ty::U64, x, k);
        fb.ret(vec![out]);
        fb.build()
    };
    let addmul = {
        let mut fb = mb.function(ADDMUL, binary);
        fb.set_producer(Producer::Clean);
        fb.set_display_path("B4Dep.addmul");
        fb.set_body_gate(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::U64);
        let b = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let ab = fb.mul(Ty::U64, a, b);
        let out = fb.add(Ty::U64, ab, a);
        fb.ret(vec![out]);
        fb.build()
    };

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.function_by_id_mut(scale).unwrap().summary = Some(scale_contract().proved());
    module.function_by_id_mut(addmul).unwrap().summary = Some(addmul_contract().proved());
    for (id, function, clause, text) in [
        (0, scale, scale_clause(), "dep_scale ensures (>= result 0)"),
        (1, addmul, addmul_clause(), "dep_addmul ensures (<= 1 2)"),
    ] {
        let (obligation, certificate) =
            certified_postcondition(&module, id, function, clause, text);
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
    }
    module
}

/// Ids of the importer's interesting rows.
#[derive(Debug, Clone, Copy)]
pub struct RootIds {
    pub rust_row: ImportId,
    pub clean_row: ImportId,
    pub scale: FuncId,
    pub addmul: FuncId,
}

/// The importer crate. `with_program = false` leaves only the two body-less
/// declarations + proof rows (used by the twins that skew a declaration, so the
/// ONLY refusal is the cross-crate one and not a local call-site mismatch).
pub fn build_root(dep: &Module, with_program: bool) -> (Module, RootIds) {
    let mut mb = ModuleBuilder::new_with_target_info("b4_root", target());
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);

    mb.set_default_producer(Producer::TRust);
    let scale = mb.declare_function(SCALE, unary);
    mb.set_default_producer(Producer::Clean);
    let addmul = mb.declare_function(ADDMUL, binary);

    if with_program {
        let mut fb = mb.function("program", nullary);
        fb.set_producer(Producer::TRust);
        fb.set_display_path("b4_root::program");
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".into(),
            evidence: None,
        });
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let two = fb.uconst(Ty::U64, 2);
        let seven = fb.uconst(Ty::U64, 7);
        let scaled = fb.call(scale, vec![two]);
        let out = fb.call(addmul, vec![scaled, seven]);
        fb.ret(vec![out]);
        fb.build();
    }

    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let digest = dep.stable_digest();
    let rust_row = m
        .intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let clean_row = m
        .intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(Producer::Clean))
        .expect("Module::intern_import: test fixture");

    // backed_by: the Rust declaration's `proved` rests on the far #0.
    m.function_by_id_mut(scale).unwrap().summary = Some(
        scale_contract()
            .proved()
            .backed_by(ExternRef::new(rust_row, SCALE).relying_on(ProofId::new(0))),
    );
    // inheritance: the Clean declaration restates the far contract (NOT
    // `proved` locally) and a local Discharged row inherits the far #1.
    m.function_by_id_mut(addmul).unwrap().summary = Some(addmul_contract());
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited: dep_addmul ensures (<= 1 2)",
        )
        .with_function(addmul)
        .with_formula(addmul_clause()),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "b4-compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: addmul,
            obligation: ProofId::new(0),
            external: Some(ExternRef::new(clean_row, ADDMUL).relying_on(ProofId::new(1))),
        },
        assurance: None,
    });

    (
        m,
        RootIds {
            rust_row,
            clean_row,
            scale,
            addmul,
        },
    )
}

/// The dependency with `dep_scale`'s constant changed 3 -> 2: same name, same
/// symbols, same contracts, same certificates — a different BODY.
pub fn tampered_dep() -> Module {
    build_dep(2)
}

/// Re-point both import rows of `root` at `dep` (after `dep` was deliberately
/// changed, so the DIGEST check passes and a LATER rule does the refusing).
pub fn repin(root: &mut Module, dep: &Module) {
    let digest = dep.stable_digest();
    for import in &mut root.imports {
        import.digest = digest;
        import.name = dep.name.clone();
    }
}
