// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Canonical whole-execution consumer, separate from untrusted assembly.
//! No native, source-language, provider or body-license authority is returned.
use super::*;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::Module;

/// A closed initializer-to-halt equality replayed in the canonical ByteV1
/// environment. The original immutable module is retained by borrow. This
/// receipt concerns exactly its two-function execution, not native emission.
pub struct CheckedDefinedConstantCallEntry<'module> {
    module: &'module Module,
    caller: FuncId,
    callee: FuncId,
    word: u64,
    argument: Option<u64>,
    judgment: Expr,
    proof: Expr,
    config_type: Expr,
    execution: Expr,
    world_type: Expr,
    terminal_world: Expr,
}
impl CheckedDefinedConstantCallEntry<'_> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        if !std::ptr::eq(module, self.module) {
            return Err("checked defined call belongs to another immutable module".into());
        }
        Ok((self.caller, self.callee))
    }
    pub(crate) fn captured_argument(&self) -> Option<u64> {
        self.argument
    }
    pub fn word(&self) -> u64 {
        self.word
    }
    pub fn judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
    // A candidate goal, not new authority: the source-call consumer must
    // replay it in the canonical environment with the actual checked island.
    pub(crate) fn entry_claim_with_word(&self, word: Expr) -> Expr {
        eq(
            &self.config_type,
            self.execution.clone(),
            app(
                "IRByteConfigV1.halted",
                [
                    self.world_type.clone(),
                    app(
                        "IROutcome.ret",
                        [list("IRScalar", &[app("IRScalar.int_", [word])])],
                    ),
                    self.terminal_world.clone(),
                ],
            ),
        )
    }
}

impl<'module> DefinedConstantCall<'module> {
    /// Independently derive the complete exact claim; only the serialized
    /// proposed proof is consumed. Candidate run/result/world fields and the
    /// assembler's Environment are never evidence. The actual initializer must
    /// accept the supplied memory, and both activation retirements must preserve
    /// it for this exact claim to hold. HOST is preserved, the root owner stack
    /// is cleared, and NEXT is successor(successor(fresh_owner(memory))).
    ///
    /// The host type/value, memory and import model are explicit closed terms,
    /// not an assertion that an external provider or native allocation exists.
    /// Exactly four fetched steps execute CALL/CONST/RETURN/RETURN. This does not
    /// reinterpret initialized bytes as access permission or a global variable.
    pub fn check_entry_proof(
        &self,
        world_type: Expr,
        providers: Expr,
        memory: Expr,
        host: Expr,
        encoded_proof: &[u8],
    ) -> Result<CheckedDefinedConstantCallEntry<'module>> {
        if encoded_proof.len() > 16 * 1024 * 1024 {
            return Err("defined call proof exceeds consumer byte budget".into());
        }
        let proof = trust_ir::proof::decode_clean_expr_dag_v2(encoded_proof)
            .map_err(|error| format!("defined call proof codec: {error:?}"))?;
        let model = MachineModel::new(world_type.clone(), self.reflected, providers);
        let initial = app(
            "ir_byte_init_v1",
            [
                world_type.clone(),
                self.reflected.context_term().clone(),
                nat(u64::from(self.caller.index())),
                self.arguments(),
                memory.clone(),
                host.clone(),
            ],
        );
        let next = app(
            "Nat.succ",
            [app(
                "Nat.succ",
                [app("ir_byte_fresh_owner_v1", [memory.clone()])],
            )],
        );
        let terminal_world = app(
            "IRByteWorldV1.mk",
            [world_type.clone(), memory, host, list("Nat", &[]), next],
        );
        let terminal = app(
            "IRByteConfigV1.halted",
            [
                world_type.clone(),
                app(
                    "IROutcome.ret",
                    [list("IRScalar", &[app("IRScalar.int_", [nat(self.word)])])],
                ),
                terminal_world.clone(),
            ],
        );
        let config_type = model.config_type();
        let execution = model.run(
            &NatTerm::literal(if self.parameters.is_some() { 3 } else { 4 }),
            initial,
        );
        let judgment = eq(&config_type, execution.clone(), terminal);
        let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|error| format!("canonical defined call specification: {error:?}"))?;
        // Existing strict replay checks closedness, Prop typing, unsafe/partial
        // refusal, kernel result, authority audit and axiom/trust-marker closure,
        // followed by lossless DAG codec round-trip and a second actual replay.
        crate::source_value_operational::strict_replay(specification.env(), &judgment, &proof)?;
        Ok(CheckedDefinedConstantCallEntry {
            module: self.reflected.module(),
            caller: self.caller,
            callee: self.callee,
            word: self.word,
            argument: self.parameters.map(|_| self.word),
            judgment,
            proof,
            config_type,
            execution,
            world_type,
            terminal_world,
        })
    }
}

/// Independently checked pointwise initializer/run-three/halt owner.
/// The actual argument is retained; it never licenses a different invocation.
pub struct CheckedDefinedWordForwardCallEntry<'module> {
    inner: CheckedDefinedConstantCallEntry<'module>,
}
impl<'module> CheckedDefinedWordForwardCallEntry<'module> {
    pub fn argument(&self) -> u64 {
        self.inner.word()
    }
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        self.inner.functions_in(module)
    }
    pub fn judgment(&self) -> &Expr {
        self.inner.judgment()
    }
    pub fn proof(&self) -> &Expr {
        self.inner.proof()
    }
    pub(crate) fn common(&self) -> &CheckedDefinedConstantCallEntry<'module> {
        &self.inner
    }
}
impl<'module> DefinedWordForwardCall<'module> {
    pub fn check_entry_proof(
        &self,
        world_type: Expr,
        providers: Expr,
        memory: Expr,
        host: Expr,
        encoded_proof: &[u8],
    ) -> Result<CheckedDefinedWordForwardCallEntry<'module>> {
        Ok(CheckedDefinedWordForwardCallEntry {
            inner: self.inner.check_entry_proof(
                world_type,
                providers,
                memory,
                host,
                encoded_proof,
            )?,
        })
    }
}
