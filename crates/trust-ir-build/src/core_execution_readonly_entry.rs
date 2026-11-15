// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent closed initializer-to-halt consumer for an original pointer
//! forwarding caller and its load-only leaf. Logical initialized bytes and
//! access are checked by execution; native data permissions remain separate.
use super::*;
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{CallingConv, Inst, Linkage, Module, Ty};

/// Exact original two-function C(Ptr)->U64 call/load/return/return profile.
/// Selection alone grants no execution, source-language or native authority.
pub struct ReadonlyEightForwardCall<'module> {
    reflected: &'module ReflectedCoreModuleV1<'module>,
    caller: FuncId,
    callee: FuncId,
}

impl<'env, 'module> Catalog<'env, 'module> {
    pub fn readonly_eight_forward_call(
        &mut self,
        caller: FuncId,
        callee: FuncId,
    ) -> Result<ReadonlyEightForwardCall<'module>> {
        let module = self.reflected.module();
        if caller == callee || module.functions.len() != 2 || !module.imports.is_empty() {
            return Err("readonly entry requires two distinct closed original functions".into());
        }
        // Reuse the complete existing leaf/body/ABI refusal, including hidden
        // effects, volatility, alignment and the exact loaded return operand.
        self.readonly_eight_callee(callee)?;
        let source = self
            .reflected
            .function(caller)
            .ok_or("readonly entry caller missing")?;
        let signature = module
            .func_type(source.ty)
            .ok_or("readonly entry signature missing")?;
        if source.calling_conv != CallingConv::C
            || !source.attrs.is_empty()
            || signature.abi.is_some()
            || signature.is_vararg
            || signature.params != [Ty::Ptr]
            || signature.returns != [Ty::U64]
            || source.blocks.len() != 1
            || source.blocks[0].id != source.entry
            || module.func_type(self.reflected.function(callee).unwrap().ty) != Some(signature)
            || self.reflected.function(callee).unwrap().linkage != Linkage::Internal
        {
            return Err("readonly entry requires exact original C(Ptr)->U64 signatures".into());
        }
        let block = &source.blocks[0];
        let [(parameter, Ty::Ptr)] = block.params.as_slice() else {
            return Err("readonly entry caller pointer parameter differs".into());
        };
        let [call, ret] = block.body.as_slice() else {
            return Err("readonly entry caller must contain only call and return".into());
        };
        let [result] = call.results.as_slice() else {
            return Err("readonly entry caller result arity differs".into());
        };
        if !matches!(&call.inst, Inst::Call { callee: target, args } if *target == callee && args == &[*parameter])
            || !ret.results.is_empty()
            || !matches!(&ret.inst, Inst::Return { values } if values == &[*result])
        {
            return Err("readonly entry changed actual target, argument or returned load".into());
        }
        Ok(ReadonlyEightForwardCall {
            reflected: self.reflected,
            caller,
            callee,
        })
    }
}

/// A checked, pointwise Core execution with the exact logical pointer, result,
/// memory and HOST. This is not a callable pointer, physical data borrow,
/// independent source-language correspondence or a universal argument theorem.
pub struct CheckedReadonlyEightCallEntry<'module> {
    module: &'module Module,
    caller: FuncId,
    callee: FuncId,
    address: u64,
    word: u64,
    judgment: Expr,
    proof: Expr,
    world_type: Expr,
    memory: Expr,
    context: Expr,
    config_type: Expr,
    run: Expr,
    final_world: Expr,
}
impl<'module> CheckedReadonlyEightCallEntry<'module> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        if !std::ptr::eq(module, self.module) {
            return Err("readonly entry belongs to another original module".into());
        }
        Ok((self.caller, self.callee))
    }
    pub fn logical_address(&self) -> u64 {
        self.address
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

    /// Join the actual licensed universal source family to this SAME original
    /// whole-entry execution. The separate closed proof must establish the
    /// complete source memory effect, including unchanged memory, at the exact
    /// context/memory/address retained by the initializer. It cannot replace
    /// the entry result, HOST, owner retirement or NEXT claim.
    pub fn check_source_family<'entry>(
        &'entry self,
        family: &'entry crate::source_readonly_calls::CheckedReadonlySourceFamily<'module>,
        encoded_effect_proof: &[u8],
    ) -> Result<CheckedReadonlyEightLicensedEntry<'entry, 'module>> {
        if family.functions_in(self.module)? != (self.caller, self.callee) {
            return Err("readonly licensed source family and actual entry functions differ".into());
        }
        if encoded_effect_proof.len() > 16 * 1024 * 1024 {
            return Err("readonly source effect proof exceeds consumer byte budget".into());
        }
        let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|e| format!("canonical readonly licensed specification: {e:?}"))?;
        let mut environment = specification.env().clone();
        let names =
            crate::validate::install_operational_island(&mut environment, family.source_island())?;
        let selected = family.source(self.caller)?;
        let name = names
            .into_iter()
            .find(|name| name.to_string() == selected.decl)
            .ok_or("actual licensed readonly source caller absent from its island")?;
        let source_effect = Expr::apps(
            Expr::const_(name, vec![]),
            [self.context.clone(), self.memory.clone(), nat(self.address)],
        );
        let judgment = eq(
            &constant("IRByteMemoryResultV1"),
            source_effect,
            app(
                "IRByteMemoryResultV1.value",
                [app("IRScalar.int_", [nat(self.word)]), self.memory.clone()],
            ),
        );
        let proof = trust_ir::proof::decode_clean_expr_dag_v2(encoded_effect_proof)
            .map_err(|e| format!("readonly source effect proof codec: {e:?}"))?;
        crate::source_value_operational::strict_replay(&environment, &judgment, &proof)?;
        Ok(CheckedReadonlyEightLicensedEntry {
            core: self,
            family,
            environment,
            judgment,
            proof,
        })
    }

    fn entry_claim_with_word(&self, word: Expr) -> Expr {
        eq(
            &self.config_type,
            self.run.clone(),
            app(
                "IRByteConfigV1.halted",
                [
                    self.world_type.clone(),
                    app(
                        "IROutcome.ret",
                        [list("IRScalar", &[app("IRScalar.int_", [word])])],
                    ),
                    self.final_world.clone(),
                ],
            ),
        )
    }

    /// Replay the SAME whole-entry proof with an independently authored checked
    /// Definition applied to this original logical memory and pointer. The
    /// selector and island are consumer inputs; their digest is checked data,
    /// not authentication of a source file or binding to an original frontend.
    /// This pointwise result mints no SOURCE_CALL certificate or body license.
    pub fn check_source_definition<'entry>(
        &'entry self,
        island: &trust_ir::proof::IslandEnvironment,
        source: &trust_ir::proof::SourceDefinitionRef,
    ) -> Result<CheckedReadonlyEightSourceEntry<'entry, 'module>> {
        if source.closure_digest != island.digest {
            return Err("readonly source selector has a different island".into());
        }
        let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|e| format!("canonical readonly source specification: {e:?}"))?;
        let mut environment = specification.env().clone();
        let names = crate::validate::install_operational_island(&mut environment, island)?;
        let name = names
            .into_iter()
            .find(|name| name.to_string() == source.decl)
            .ok_or("readonly source Definition is not declared by this island")?;
        let definition = environment
            .get_const(&name)
            .ok_or("readonly source missing")?;
        if definition.kind != clean_kernel::ConstantKind::Definition
            || !definition.level_params.is_empty()
        {
            return Err("readonly source must be an actual monomorphic Definition".into());
        }
        let source_term = Expr::const_(name, vec![]);
        let source_type = Expr::pi(
            clean_kernel::BinderInfo::Default,
            constant("IRByteMemoryV1"),
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                constant("Nat"),
                constant("Nat"),
            ),
        );
        let mut checker = TypeChecker::new(&environment);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker
            .check_type(&source_term, &source_type)
            .map_err(|_| {
                "readonly source requires exactly logical memory -> address -> Nat".to_owned()
            })?;
        drop(checker);
        let source_value = Expr::apps(source_term, [self.memory.clone(), nat(self.address)]);
        let judgment = self.entry_claim_with_word(source_value);
        crate::source_value_operational::strict_replay(&environment, &judgment, &self.proof)?;
        Ok(CheckedReadonlyEightSourceEntry {
            core: self,
            source: source.clone(),
            environment,
            judgment,
        })
    }
}

/// Independent source-definition and exact original Core entry, checked at one
/// logical input. No universal source semantics, frontend/source-text binding,
/// physical borrow, native call or provider permission follows.
pub struct CheckedReadonlyEightSourceEntry<'entry, 'module> {
    core: &'entry CheckedReadonlyEightCallEntry<'module>,
    source: trust_ir::proof::SourceDefinitionRef,
    environment: Environment,
    judgment: Expr,
}
impl<'entry, 'module> CheckedReadonlyEightSourceEntry<'entry, 'module> {
    pub fn core_entry(&self) -> &'entry CheckedReadonlyEightCallEntry<'module> {
        self.core
    }
    pub fn source(&self) -> &trust_ir::proof::SourceDefinitionRef {
        &self.source
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn proof(&self) -> &Expr {
        self.core.proof()
    }
}

impl<'module> ReadonlyEightForwardCall<'module> {
    /// Reconstruct the actual initializer/run-four/halt judgment independently.
    /// Only serialized proof bytes are consumed, never candidate run/result or
    /// assembler-environment fields. The claimed word and pointer are inputs
    /// to the closed judgment and must be proved, not trusted observations.
    /// Both retirements must preserve the original memory, HOST is preserved,
    /// owners are cleared and NEXT advances twice from fresh_owner(memory).
    pub fn check_entry_proof(
        &self,
        world_type: Expr,
        providers: Expr,
        memory: Expr,
        host: Expr,
        address: u64,
        word: u64,
        encoded_proof: &[u8],
    ) -> Result<CheckedReadonlyEightCallEntry<'module>> {
        if encoded_proof.len() > 16 * 1024 * 1024 {
            return Err("readonly entry proof exceeds consumer byte budget".into());
        }
        let proof = trust_ir::proof::decode_clean_expr_dag_v2(encoded_proof)
            .map_err(|e| format!("readonly entry proof codec: {e:?}"))?;
        let model = MachineModel::new(world_type.clone(), self.reflected, providers);
        let initial = app(
            "ir_byte_init_v1",
            [
                world_type.clone(),
                self.reflected.context_term().clone(),
                nat(u64::from(self.caller.index())),
                list("IRScalar", &[app("IRScalar.ptr_", [nat(address)])]),
                memory.clone(),
                host.clone(),
            ],
        );
        let world = app(
            "IRByteWorldV1.mk",
            [
                world_type.clone(),
                memory.clone(),
                host,
                list("Nat", &[]),
                app(
                    "Nat.succ",
                    [app(
                        "Nat.succ",
                        [app("ir_byte_fresh_owner_v1", [memory.clone()])],
                    )],
                ),
            ],
        );
        let terminal = app(
            "IRByteConfigV1.halted",
            [
                world_type.clone(),
                app(
                    "IROutcome.ret",
                    [list("IRScalar", &[app("IRScalar.int_", [nat(word)])])],
                ),
                world.clone(),
            ],
        );
        let config_type = model.config_type();
        let run = model.run(&NatTerm::literal(4), initial);
        let judgment = eq(&config_type, run.clone(), terminal);
        let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|e| format!("canonical readonly entry specification: {e:?}"))?;
        crate::source_value_operational::strict_replay(specification.env(), &judgment, &proof)?;
        Ok(CheckedReadonlyEightCallEntry {
            module: self.reflected.module(),
            caller: self.caller,
            callee: self.callee,
            address,
            word,
            judgment,
            proof,
            world_type,
            memory,
            context: self.reflected.context_term().clone(),
            config_type,
            run,
            final_world: world,
        })
    }
}

/// Both complete original Core execution and the licensed original source
/// memory effect. This logical owner grants no physical borrow, frontend text
/// authentication, machine call, stack installation or native entry permission.
pub struct CheckedReadonlyEightLicensedEntry<'entry, 'module> {
    core: &'entry CheckedReadonlyEightCallEntry<'module>,
    family: &'entry crate::source_readonly_calls::CheckedReadonlySourceFamily<'module>,
    environment: Environment,
    judgment: Expr,
    proof: Expr,
}
impl<'entry, 'module> CheckedReadonlyEightLicensedEntry<'entry, 'module> {
    pub fn core_entry(&self) -> &'entry CheckedReadonlyEightCallEntry<'module> {
        self.core
    }
    pub fn source_family(
        &self,
    ) -> &'entry crate::source_readonly_calls::CheckedReadonlySourceFamily<'module> {
        self.family
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn effect_judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn effect_proof(&self) -> &Expr {
        &self.proof
    }
}
