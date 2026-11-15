// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{BLOCK, Claim, FUNCTION, checker};
use clean_kernel::{BinderInfo, Expr, KernelTypeError, Level, Name, TypeChecker};
use trust_ir::Module;
use trust_ir_build::{
    core_execution::{
        Assembler, Catalog, Coordinate, EntryTarget, Limits, MachineModel, NatTerm,
        PendingEquality, PendingProof, RootReturnFrame, ScalarPremises,
    },
    core_reflection::reflect_core_module_v1,
    scoped_local::{LocalScope, ScopedLocal},
};

pub(super) fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
pub(super) fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
pub(super) fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
pub(super) fn scalar(word: Expr) -> Expr {
    app("IRScalar.int_", [word])
}
pub(super) fn result(value: Expr) -> Expr {
    app("IRStepResult.value", [value])
}
pub(super) fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}
pub(super) fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}
pub(super) fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
pub(super) fn quotient(word: Expr) -> Expr {
    app(
        "ir_dm_quot",
        [app(
            "ir_dm_go",
            [
                nat(1),
                word.clone(),
                nat(64),
                nat(8),
                app("IRDivMod.mk", [word, nat(0)]),
            ],
        )],
    )
}
pub(super) fn bound(word: Expr) -> Expr {
    app("Nat.lt", [word, app("ir_nat_pow2", [nat(64)])])
}
pub(super) fn bounded(word: u64) -> PendingProof {
    PendingProof::candidate(
        bound(nat(word)),
        app(
            "Nat.le_add_right",
            [app("Nat.succ", [nat(word)]), nat(u64::MAX - word)],
        ),
    )
}
pub(super) fn limits() -> Limits {
    Limits {
        max_operations: 1_000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 32,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn strict_checker() -> TypeChecker<'static> {
    budgeted_checker(limits().lookup_heartbeats)
}
fn budgeted_checker(heartbeats: u32) -> TypeChecker<'static> {
    let mut tc = TypeChecker::new(checker().environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.set_heartbeat_limit(heartbeats);
    tc.set_max_cache_entries(limits().lookup_cache_entries);
    tc
}
/// Strictly replay `term : claim` on a fresh checker holding `heartbeats`, and
/// return the kernel work it took. A budget stop is an `Err`, never a verdict.
///
/// The budget is what makes this a guard: once spent, the kernel stops
/// reducing, so a replay whose work depends on an operand's MAGNITUDE (the
/// reference semantics evaluated instead of its derived law) fails here in
/// seconds instead of running for hours under the default budget, whose
/// heartbeats a long reduction spends ever more slowly.
pub(super) fn replay_work(term: &Expr, claim: &Expr, heartbeats: u32) -> Result<u64, String> {
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let mut tc = budgeted_checker(heartbeats);
    tc.enable_heartbeat_profiler();
    tc.check_type(claim, &Expr::sort(Level::zero()))
        .map_err(|error| format!("claim is not a proposition: {error:?}"))?;
    let checked = tc.check_type(term, claim);
    let work = tc.heartbeat_profile().map_or(0, |profile| profile.total());
    if tc.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
        return Err(format!(
            "budget of {heartbeats} heartbeats spent ({work} used)"
        ));
    }
    checked.map_err(|error| format!("refused after {work} heartbeats: {error:?}"))?;
    Ok(work)
}
fn close(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    claim: &Expr,
) -> (Expr, Expr) {
    let term = parameters
        .iter()
        .rev()
        .fold(term.clone(), |body, local| local.lam(body));
    let claim = parameters
        .iter()
        .rev()
        .fold(claim.clone(), |body, local| local.pi(body));
    (scope.close(&term).unwrap(), scope.close(&claim).unwrap())
}
fn unspent(tc: &TypeChecker<'_>) {
    assert!(!tc.heartbeat_spent(), "no proof-budget stop is a verdict");
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
}
pub(super) fn certify(term: &Expr, claim: &Expr, law: Option<&str>) {
    assert!(!term.has_fvar_quick() && !claim.has_fvar_quick());
    let tc = strict_checker();
    tc.check_type(claim, &Expr::sort(Level::zero())).unwrap();
    tc.check_type(term, claim).unwrap();
    unspent(&tc);
    let env = checker().environment();
    let audit = env.audit_certification(claim, term);
    assert!(
        audit.is_certified(),
        "actual rooted authority closure: {audit:#?}"
    );
    if let Some(law) = law {
        let name = Name::from_string(law);
        assert!(
            audit.dependencies.contains(&name),
            "operation root retained in DAG"
        );
        assert!(env.axiom_deps(&name).unwrap().is_empty());
        assert!(env.trust_marker_deps(&name).unwrap().is_empty());
    }
}
pub(super) fn replay(
    scope: &LocalScope,
    parameters: &[ScopedLocal],
    term: &Expr,
    claim: &Expr,
    law: Option<&str>,
) {
    let (term, claim) = close(scope, parameters, term, claim);
    certify(&term, &claim, law);
    let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap();
    assert_eq!(
        decoded, term,
        "retain the whole graph, not a claimed answer"
    );
    certify(&decoded, &claim, law);
}
pub(super) fn refuses(scope: &LocalScope, parameters: &[ScopedLocal], term: &Expr, claim: &Expr) {
    let (term, claim) = close(scope, parameters, term, claim);
    let tc = strict_checker();
    tc.check_type(&claim, &Expr::sort(Level::zero())).unwrap();
    let error = tc.check_type(&term, &claim).unwrap_err();
    unspent(&tc);
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "mathematical/type refusal, never resource or lookup: {error:?}"
    );
}
pub(super) fn rejects(claim: &Claim, module: &Module, bytes: &[u8]) {
    let error = checker().recheck_dag_v2(claim, module, bytes).unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
        "unknown constant",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{error}"
        );
    }
}
pub(super) fn providers() -> Expr {
    lam(
        c("Nat"),
        lam(
            app("IRList", [c("IRScalar")]),
            lam(
                c("IRByteMemoryV1"),
                lam(
                    c("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            app("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}
pub(super) fn memory(byte: u64) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                &[
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(16), nat(16), nat(0), c("Bool.true")],
                    ),
                    app(
                        "IRByteAllocationV1.mk",
                        [nat(80), nat(8), nat(7), c("Bool.false")],
                    ),
                ],
            ),
            lam(c("Nat"), app("IROption.some", [c("Nat"), nat(byte)])),
            nat(128),
        ],
    )
}
pub(super) fn world(byte: u64, host: u64, owners: &[Expr], next: u64) -> Expr {
    app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            memory(byte),
            nat(host),
            list("Nat", owners),
            nat(next),
        ],
    )
}
fn truth(assembler: &mut Assembler<'_>, left: Expr) -> PendingEquality {
    assembler
        .conversion(c("Bool"), left, c("Bool.true"))
        .unwrap()
}

pub(super) fn assemble(module: &Module, claim: Claim, terminal_override: Option<Expr>) -> Vec<u8> {
    let reflected = reflect_core_module_v1(module, &[(FUNCTION, 4096)]).unwrap();
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let mut catalog = Catalog::new(checker().environment(), &reflected, limits()).unwrap();
    let entry = catalog.entry(FUNCTION).unwrap();
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits()).unwrap();
    let arguments = list("IRScalar", &[scalar(nat(claim.word))]);
    let memory_guard = truth(&mut assembler, EntryTarget::memory_admission(memory(173)));
    let entry_guard = truth(
        &mut assembler,
        entry.admission(&model, arguments.clone()).unwrap(),
    );
    let initialized = entry
        .initialize(
            &mut assembler,
            &model,
            arguments,
            memory(173),
            nat(37),
            memory_guard,
            entry_guard,
        )
        .unwrap();
    let original = initialized.current().clone();
    let mut current = original.clone();
    let mut valid = initialized.valid().clone();
    let mut prefix = assembler.zero(&model, current.running(&model)).unwrap();
    for pc in 0..2 {
        let site = catalog
            .fetch(Coordinate {
                function: FUNCTION,
                block: BLOCK,
                instruction: pc,
            })
            .unwrap();
        let value = scalar(nat(if pc == 0 { 3 } else { claim.answer }));
        let checks = site.scalar_checks(&model, &current, value.clone()).unwrap();
        let evaluated = if pc == 0 {
            assert_eq!(*site.instruction.get_app_fn(), c("IRInst.const_"));
            assembler
                .conversion(c("IRStepResult"), checks.evaluation, result(value.clone()))
                .unwrap()
        } else {
            assert_eq!(*site.instruction.get_app_fn(), c("IRInst.binop"));
            let (_, operation) =
                claim
                    .shift
                    .derive(&mut assembler, nat(claim.word), bounded(claim.word));
            let computed = assembler
                .conversion(
                    c("IRStepResult"),
                    operation.right().clone(),
                    result(value.clone()),
                )
                .unwrap();
            let operation = assembler.compose(operation, computed).unwrap();
            // Only lookup substitution/definitional conversion connects the
            // derived operation to the ACTUAL fetched BinOp expression.
            assembler
                .convert_endpoints(operation, checks.evaluation, result(value.clone()))
                .unwrap()
        };
        // These are separate actual carrier/result guards, not consequences
        // silently assumed from the successful pure evaluator equation.
        let operands = truth(&mut assembler, checks.operands);
        let result_guard = truth(&mut assembler, checks.result);
        let transfer = site
            .scalar_value(
                &mut assembler,
                &model,
                &current,
                value,
                ScalarPremises {
                    evaluated,
                    operands,
                    result: result_guard,
                    before: valid,
                },
            )
            .unwrap();
        assert_eq!(transfer.current().world, original.world);
        assert_eq!(transfer.current().tail, original.tail);
        assert_eq!(transfer.current().legacy_memory, original.legacy_memory);
        assert_eq!(transfer.current().legacy_cursor, original.legacy_cursor);
        prefix = assembler
            .concatenate(prefix, transfer.run().clone())
            .unwrap();
        current = transfer.current().clone();
        valid = transfer.valid().clone();
    }
    let owner = app("ir_byte_fresh_owner_v1", [memory(173)]);
    let frame = RootReturnFrame {
        returning: current.frame.clone(),
        legacy_memory: current.legacy_memory.clone(),
        legacy_cursor: current.legacy_cursor.clone(),
        memory: memory(173),
        host: nat(37),
        owner: owner.clone(),
        next: app("Nat.succ", [owner]),
    };
    assert_eq!(
        frame.current(&model).running(&model),
        current.running(&model)
    );
    let returning = catalog
        .fetch(Coordinate {
            function: FUNCTION,
            block: BLOCK,
            instruction: 2,
        })
        .unwrap();
    assert_eq!(*returning.instruction.get_app_fn(), c("IRInst.ret"));
    let fields = returning.instruction.get_app_args();
    let [arguments] = fields.as_slice() else {
        panic!("actual fetched Return IDs")
    };
    let resolved = assembler
        .conversion(
            app("IRList", [c("IRScalar")]),
            app("ir_resolve", [current.machine(), (*arguments).clone()]),
            claim.values(),
        )
        .unwrap();
    let target = catalog.call_target(FUNCTION).unwrap();
    let admitted = truth(
        &mut assembler,
        returning
            .root_return_admission(&model, &target, &frame, claim.values())
            .unwrap(),
    );
    let returned = returning
        .return_from_root(
            &mut assembler,
            &model,
            &target,
            &frame,
            resolved,
            admitted,
            valid,
        )
        .unwrap();
    let execution = assembler
        .concatenate(prefix, returned.run().clone())
        .unwrap();
    let mapped = assembler
        .congruence(
            initialized.equality().clone(),
            model.config_type(),
            |state| model.run(execution.fuel(), state),
        )
        .unwrap();
    let start = assembler
        .conversion(
            model.config_type(),
            model.run(&NatTerm::literal(3), claim.initial(&model)),
            mapped.left().clone(),
        )
        .unwrap();
    let middle = assembler
        .conversion(
            model.config_type(),
            mapped.right().clone(),
            execution.equality().left().clone(),
        )
        .unwrap();
    let complete = assembler.compose(start, mapped).unwrap();
    let complete = assembler.compose(complete, middle).unwrap();
    let complete = assembler
        .compose(complete, execution.equality().clone())
        .unwrap();
    let terminal = claim.terminal(terminal_override.unwrap_or_else(|| world(173, 37, &[], 9)));
    let end = assembler
        .conversion(model.config_type(), complete.right().clone(), terminal)
        .unwrap();
    let complete = assembler.compose(complete, end).unwrap();
    let closed = scope.close(complete.term()).unwrap();
    assert!(
        !closed.has_fvar_quick(),
        "no successful evaluation or final-world premise"
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&closed).unwrap()
}
