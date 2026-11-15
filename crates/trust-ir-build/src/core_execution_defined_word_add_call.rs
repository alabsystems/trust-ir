// Copyright 2026 Andrew Yates | Apache-2.0
//! Derived original forward/Add CALL execution. Candidates never replace either
//! body or mint native/ABI/provider permission. Universal consumers replay the
//! complete initializer/run-five/halt claim in the maintained arithmetic owner.
use super::*;

#[derive(Clone)]
pub(super) struct ForwardAdd {
    pub(super) argument: Expr,
    pub(super) offset: u64,
    add: FetchedSite,
    argument_bound: WrappedWordBound,
    result_bound: WrappedWordBound,
}
fn and(left: PendingEquality, right: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        constant("Bool"),
        app("Bool.and", [left.left.clone(), right.left.clone()]),
        constant("Bool.true"),
        app(
            "ir_byte_function_and_true_v1",
            [left.left, right.left, left.term, right.term],
        ),
    )
}
fn truth() -> PendingEquality {
    PendingEquality::candidate(
        constant("Bool"),
        constant("Bool.true"),
        constant("Bool.true"),
        refl(&constant("Bool"), constant("Bool.true")),
    )
}
fn value_fit(model: &MachineModel, word: Expr, fit: PendingEquality) -> PendingEquality {
    PendingEquality::candidate(
        constant("Bool"),
        app(
            "ir_byte_value_matches_v1",
            [
                model.context().clone(),
                app("IRTy.uint_", [nat(64)]),
                app("IRScalar.int_", [word.clone()]),
            ],
        ),
        constant("Bool.true"),
        app(
            "ir_byte_u64_value_fits_v1",
            [model.context().clone(), word, fit.term],
        ),
    )
}
impl ForwardAdd {
    pub(super) fn result_word(&self) -> Expr {
        self.result_bound.word.clone()
    }
    pub(super) fn argument_admission(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        guard: Expr,
    ) -> Result<PendingEquality> {
        let fit = value_fit(
            model,
            self.argument.clone(),
            self.argument_bound.fits.clone(),
        );
        a.ascribe_endpoints(and(fit, truth()), guard, constant("Bool.true"))
    }
    pub(super) fn result_admission(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        guard: Expr,
    ) -> Result<PendingEquality> {
        let fit = value_fit(model, self.result_word(), self.result_bound.fits.clone());
        // The singleton return list contributes (fit && true). Both actual
        // return guards additionally check their frame destination count.
        // Prove that outer conjunction too: for a symbolic fit, flattening
        // (fit && true) && true is not definitional equality.
        a.ascribe_endpoints(
            and(and(fit, truth()), truth()),
            guard,
            constant("Bool.true"),
        )
    }
    pub(super) fn execute(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        current: &Current,
        before: PendingEquality,
    ) -> Result<ScalarTransfer> {
        let limit = app("ir_nat_pow2", [nat(64)]);
        let k = nat(self.offset);
        let k_fit = a.conversion(
            constant("Bool"),
            app("ir_nat_ltb", [k.clone(), limit.clone()]),
            constant("Bool.true"),
        )?;
        let k_bound = PendingProof::candidate(
            app("Nat.lt", [k.clone(), limit.clone()]),
            app(
                "ir_byte_separation_lt_of_ltb_v1",
                [k.clone(), limit, k_fit.term().clone()],
            ),
        );
        let (_conditional, evaluated, _) = a.byte_add_u64_canonical(
            self.argument.clone(),
            k.clone(),
            self.argument_bound.strict_bound.clone(),
            k_bound.clone(),
        )?;
        let (_raw, raw_to_conditional, _) = a.byte_add_word64_canonical(
            self.argument.clone(),
            k.clone(),
            self.argument_bound.strict_bound.clone(),
            k_bound,
        )?;
        let reverse = PendingEquality::candidate(
            constant("Nat"),
            raw_to_conditional.right().clone(),
            raw_to_conditional.left().clone(),
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.symm"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    constant("Nat"),
                    raw_to_conditional.left().clone(),
                    raw_to_conditional.right().clone(),
                    raw_to_conditional.term().clone(),
                ],
            ),
        );
        let result = a.congruence(reverse, constant("IRStepResult"), |word| {
            app("IRStepResult.value", [app("IRScalar.int_", [word])])
        })?;
        // Congruence deliberately retains beta-redex endpoints. Convert its
        // left endpoint to the exact scalar evaluator result before the
        // syntactic composition; final closed replay checks this transport.
        let result = a
            .convert_endpoints(
                result,
                evaluated.right().clone(),
                app(
                    "IRStepResult.value",
                    [app("IRScalar.int_", [self.result_word()])],
                ),
            )
            .map_err(|e| format!("word Add scalar result beta transport: {e}"))?;
        let evaluated = a
            .compose(evaluated, result)
            .map_err(|e| format!("word Add scalar evaluation composition: {e}"))?;
        let value = app("IRScalar.int_", [self.result_word()]);
        let checks = self.add.scalar_checks(model, current, value.clone())?;
        let evaluated = a.ascribe_endpoints(
            evaluated,
            checks.evaluation,
            app("IRStepResult.value", [value.clone()]),
        )?;
        let operands = and(
            value_fit(
                model,
                self.argument.clone(),
                self.argument_bound.fits.clone(),
            ),
            value_fit(model, k, k_fit),
        );
        let operands = a.ascribe_endpoints(operands, checks.operands, constant("Bool.true"))?;
        let fit = value_fit(model, self.result_word(), self.result_bound.fits.clone());
        let result = a.ascribe_endpoints(
            and(truth(), and(fit, truth())),
            checks.result,
            constant("Bool.true"),
        )?;
        self.add.scalar_value(
            a,
            model,
            current,
            value,
            ScalarPremises {
                evaluated,
                operands,
                result,
                before,
            },
        )
    }
}

#[cfg(feature = "source-value-operational")]
pub struct DefinedWordAddCall<'module> {
    prototype: DefinedConstantCall<'module>,
    offset: u64,
    add: FetchedSite,
}
#[cfg(feature = "source-value-operational")]
impl<'e, 'm> Catalog<'e, 'm> {
    /// Exact original attribute-free C(U64)->U64 caller forwarding its actual
    /// parameter to an internal CONST/U64-ADD/RETURN leaf. No argument or
    /// expected answer is supplied. Extra effects/widths/source operands refuse.
    pub fn defined_word_add_call(
        &mut self,
        caller: FuncId,
        callee: FuncId,
    ) -> Result<DefinedWordAddCall<'m>> {
        let module = self.reflected.module();
        if caller == callee || module.functions.len() != 2 || !module.imports.is_empty() {
            return Err("word Add call requires two distinct closed original functions".into());
        }
        let cf = self
            .reflected
            .function(caller)
            .ok_or("missing original Add caller")?;
        let lf = self
            .reflected
            .function(callee)
            .ok_or("missing original Add leaf")?;
        let valid = |f: &trust_ir::Function| -> Result<()> {
            let s = module.func_type(f.ty).ok_or("missing word Add signature")?;
            if f.calling_conv != CallingConv::C
                || !f.attrs.is_empty()
                || s.abi.is_some()
                || s.is_vararg
                || s.params != [Ty::U64]
                || s.returns != [Ty::U64]
                || f.blocks.len() != 1
                || f.blocks[0].id != f.entry
            {
                return Err("word Add call requires exact attribute-free C(U64)->U64".into());
            }
            Ok(())
        };
        valid(cf)?;
        valid(lf)?;
        if lf.linkage != Linkage::Internal {
            return Err("word Add leaf is not internal".into());
        }
        let [(cp, Ty::U64)] = cf.blocks[0].params.as_slice() else {
            return Err("word Add caller parameter differs".into());
        };
        let [(lp, Ty::U64)] = lf.blocks[0].params.as_slice() else {
            return Err("word Add callee parameter differs".into());
        };
        let [call, ret] = cf.blocks[0].body.as_slice() else {
            return Err("word Add caller must be actual call/return".into());
        };
        let [konst, add, leafret] = lf.blocks[0].body.as_slice() else {
            return Err("word Add leaf must be actual constant/add/return".into());
        };
        let ([cr], [kr], [ar]) = (
            call.results.as_slice(),
            konst.results.as_slice(),
            add.results.as_slice(),
        ) else {
            return Err("word Add result arity differs".into());
        };
        let Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(k),
        } = &konst.inst
        else {
            return Err("word Add offset is not U64 literal".into());
        };
        let k = u64::try_from(*k).map_err(|_| "word Add offset outsideU64")?;
        if !matches!(&call.inst,Inst::Call{callee:f,args} if *f==callee && args==&[*cp])
            || !matches!(&ret.inst,Inst::Return{values} if values==&[*cr])
            || !matches!(&add.inst,Inst::BinOp{op:trust_ir::BinOp::Add,ty:Ty::U64,lhs,rhs} if lhs==lp && rhs==kr)
            || !matches!(&leafret.inst,Inst::Return{values} if values==&[*ar])
            || !ret.results.is_empty()
            || !leafret.results.is_empty()
        {
            return Err("word Add original target/argument/operands/returnedvalue differ".into());
        }
        let (ce, le, cp, lp, cr, ar) = (cf.entry, lf.entry, *cp, *lp, *cr, *ar);
        Ok(DefinedWordAddCall {
            offset: k,
            add: self.fetch(Coordinate {
                function: callee,
                block: le,
                instruction: 1,
            })?,
            prototype: DefinedConstantCall {
                reflected: self.reflected,
                caller,
                caller_entry: ce,
                callee,
                word: k,
                parameters: Some((cp, lp)),
                forward_add: None,
                call: self.fetch(Coordinate {
                    function: caller,
                    block: ce,
                    instruction: 0,
                })?,
                constant: Some(self.fetch(Coordinate {
                    function: callee,
                    block: le,
                    instruction: 0,
                })?),
                leaf_return: self.fetch(Coordinate {
                    function: callee,
                    block: le,
                    instruction: 2,
                })?,
                caller_return: self.fetch(Coordinate {
                    function: caller,
                    block: ce,
                    instruction: 1,
                })?,
                leaf: self.internal_target(callee)?,
                caller_target: self.call_target(caller)?,
                entry: self.entry(caller)?,
                leaf_result: ar,
                caller_result: cr,
            },
        })
    }
}
#[cfg(feature = "source-value-operational")]
impl<'module> DefinedWordAddCall<'module> {
    pub fn offset(&self) -> u64 {
        self.offset
    }
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        self.prototype.functions_in(module)
    }
    fn recipe(&self, a: &mut Assembler<'_>, raw: Expr) -> Result<DefinedConstantCall<'module>> {
        let argument_bound = a.wrapped_word_bound(64, raw)?;
        let argument = argument_bound.word.clone();
        let result_bound =
            a.wrapped_word_bound(64, app("Nat.add", [argument.clone(), nat(self.offset)]))?;
        let mut result = self.prototype.clone();
        let add = self.add.clone();
        result.forward_add = Some(ForwardAdd {
            argument,
            offset: self.offset,
            add,
            argument_bound,
            result_bound,
        });
        Ok(result)
    }
}

#[cfg(feature = "source-value-operational")]
fn limits() -> Limits {
    Limits {
        max_operations: 100_000,
        max_locals: 10_000,
        max_list_items: 1000,
        max_lookup_candidates: 1000,
        lookup_heartbeats: 2_000_000,
        lookup_cache_entries: 100_000,
    }
}
#[cfg(feature = "source-value-operational")]
pub(super) fn canonical_environment() -> Result<&'static Environment> {
    use std::sync::OnceLock;
    static E: OnceLock<Result<Environment>> = OnceLock::new();
    E.get_or_init(|| {
        clean_verify::eval_ir::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
            .map(|spec| spec.env().clone())
            .map_err(|e| e.to_string())
    })
    .as_ref()
    .map_err(Clone::clone)
}
#[cfg(feature = "source-value-operational")]
fn memory() -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", &[]),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("Nat"),
                app("IROption.none", [constant("Nat")]),
            ),
            nat(1),
        ],
    )
}
#[cfg(feature = "source-value-operational")]
fn providers() -> Expr {
    Expr::lam(
        clean_kernel::BinderInfo::Default,
        constant("Nat"),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            app("IRList", [constant("IRScalar")]),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                constant("IRByteMemoryV1"),
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    constant("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            constant("Nat"),
                            app("IROutcome.stuck", [constant("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}

/// Bound diagnostics without rendering a whole failed proof into stderr.
#[cfg(all(test, feature = "source-value-operational"))]
fn bounded_kernel_error(error: &clean_kernel::KernelTypeError) -> String {
    struct Bounded(String);
    impl std::fmt::Write for Bounded {
        fn write_str(&mut self, value: &str) -> std::fmt::Result {
            let room = 6000usize.saturating_sub(self.0.len());
            if value.len() <= room {
                self.0.push_str(value);
                return Ok(());
            }
            let mut end = room.min(value.len());
            while !value.is_char_boundary(end) {
                end -= 1;
            }
            self.0.push_str(&value[..end]);
            Err(std::fmt::Error)
        }
    }
    let mut output = Bounded(String::new());
    let truncated = std::fmt::write(&mut output, format_args!("{error:?}")).is_err();
    if truncated {
        output.0.push_str(" [bounded diagnostic truncated]");
    }
    if let clean_kernel::KernelTypeError::TypeMismatch {
        expected, inferred, ..
    } = error
    {
        output.0.push_str(&format!(
            " [expected cached-hash {:08x}; inferred cached-hash {:08x}]",
            expected.hash_cached(),
            inferred.hash_cached()
        ));
    }
    output.0
}

/// Strictly checked forall-raw-Nat entry. Logical arguments are canonical
/// wrap64(raw), hence this one theorem covers every supported U64 word. The
/// independently checked codec retains its exact canonical-word bound premise.
/// Original module custody and both closed propositions survive consumption.
#[cfg(feature = "source-value-operational")]
pub struct CheckedDefinedWordAddCallEntry<'module> {
    module: &'module Module,
    caller: FuncId,
    callee: FuncId,
    offset: u64,
    judgment: Expr,
    proof: Expr,
    environment: Environment,
    codec_claim: Expr,
    codec_proof: Expr,
}
#[cfg(feature = "source-value-operational")]
impl CheckedDefinedWordAddCallEntry<'_> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        if !std::ptr::eq(module, self.module) {
            return Err("universal word Add entry belongs to another original module".into());
        }
        Ok((self.caller, self.callee))
    }
    pub fn offset(&self) -> u64 {
        self.offset
    }
    pub fn judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
    pub fn argument_codec_claim(&self) -> &Expr {
        &self.codec_claim
    }
    pub fn argument_codec_proof(&self) -> &Expr {
        &self.codec_proof
    }
    pub(crate) fn input_at(&self, raw: Expr) -> Expr {
        app("ir_wrap", [nat(64), raw])
    }
    pub(crate) fn result_at(&self, raw: Expr) -> Expr {
        app(
            "ir_wrap",
            [
                nat(64),
                app("Nat.add", [self.input_at(raw), nat(self.offset)]),
            ],
        )
    }
    pub(crate) fn terminal_with_word(&self, word: Expr) -> Expr {
        terminal(word)
    }
}
#[cfg(feature = "source-value-operational")]
fn terminal(word: Expr) -> Expr {
    app(
        "IRByteConfigV1.halted",
        [
            constant("Nat"),
            app(
                "IROutcome.ret",
                [list("IRScalar", &[app("IRScalar.int_", [word])])],
            ),
            app(
                "IRByteWorldV1.mk",
                [constant("Nat"), memory(), nat(0), list("Nat", &[]), nat(3)],
            ),
        ],
    )
}
#[cfg(feature = "source-value-operational")]
impl<'module> DefinedWordAddCall<'module> {
    fn execution_at(&self, raw: Expr) -> Expr {
        let input = app("ir_wrap", [nat(64), raw]);
        let model = MachineModel::new(constant("Nat"), self.prototype.reflected, providers());
        model.run(
            &NatTerm::literal(5),
            app(
                "ir_byte_init_v1",
                [
                    constant("Nat"),
                    self.prototype.reflected.context_term().clone(),
                    nat(u64::from(self.prototype.caller.index())),
                    list("IRScalar", &[app("IRScalar.int_", [input])]),
                    memory(),
                    nat(0),
                ],
            ),
        )
    }
    fn claim_at(&self, raw: Expr) -> Expr {
        let input = app("ir_wrap", [nat(64), raw.clone()]);
        eq(
            &app("IRByteConfigV1", [constant("Nat")]),
            self.execution_at(raw),
            terminal(app(
                "ir_wrap",
                [nat(64), app("Nat.add", [input, nat(self.offset)])],
            )),
        )
    }
    /// Ignore candidate endpoints and reconstruct the exact closed universal
    /// initializer/run-five/halt claim from original bodies and fixed world.
    /// Codec/closure/kernel/audit checks run before this owner can be returned.
    pub fn check_universal_entry_proof(
        &self,
        encoded: &[u8],
    ) -> Result<CheckedDefinedWordAddCallEntry<'module>> {
        if encoded.len() > 16 * 1024 * 1024 {
            return Err("universal word Add proof exceeds consumer byte budget".into());
        }
        let proof = trust_ir::proof::decode_clean_expr_dag_v2(encoded)
            .map_err(|e| format!("universal word Add proof codec: {e:?}"))?;
        let judgment = Expr::pi(
            clean_kernel::BinderInfo::Default,
            constant("Nat"),
            self.claim_at(Expr::bvar(0)),
        );
        let environment = canonical_environment()?;
        #[cfg(test)]
        {
            // Preserve the exact kernel cause before the canonical codec/audit
            // consumer deliberately summarizes refusal categories. This is an
            // test-only diagnostic, never a duplicate production replay.
            let mut checker = TypeChecker::new(environment);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker
                .check_type(&judgment, &Expr::sort(Level::zero()))
                .map_err(|e| {
                    format!(
                        "universal word Core reconstructed claim kernel: {}",
                        bounded_kernel_error(&e)
                    )
                })?;
            checker.check_type(&proof, &judgment).map_err(|e| {
                format!(
                    "universal word Core candidate kernel: {}",
                    bounded_kernel_error(&e)
                )
            })?;
            drop(checker);
        }
        crate::source_value_operational::strict_replay(environment, &judgment, &proof)?;
        let mut scope = Scope::new();
        let mut a = Assembler::new(&mut scope, limits())?;
        let codec = a.byte_word64_codec()?;
        crate::source_value_operational::strict_replay(
            environment,
            codec.proposition(),
            codec.term(),
        )?;
        Ok(CheckedDefinedWordAddCallEntry {
            module: self.prototype.reflected.module(),
            caller: self.prototype.caller,
            callee: self.prototype.callee,
            offset: self.offset,
            judgment,
            proof,
            environment: environment.clone(),
            codec_claim: codec.proposition().clone(),
            codec_proof: codec.term().clone(),
        })
    }
    /// Assemble one closed forall proof, not a host loop over sample arguments.
    pub fn derive_universal_entry(&self) -> Result<CheckedDefinedWordAddCallEntry<'module>> {
        let environment = canonical_environment()?;
        let mut scope = Scope::new();
        let raw = scope
            .try_local(constant("Nat"))
            .map_err(|e| e.to_string())?;
        let mut a = Assembler::new(&mut scope, limits())?;
        let recipe = self.recipe(&mut a, raw.term().clone())?;
        let model = MachineModel::new(constant("Nat"), self.prototype.reflected, providers());
        let mem = memory();
        let root = recipe.entry_root(mem.clone(), nat(0));
        let ready = a.conversion(
            constant("Bool"),
            EntryTarget::memory_admission(mem.clone()),
            constant("Bool.true"),
        )?;
        let guard = recipe.entry_admission(&model)?;
        let admitted = recipe.admission_evidence(&mut a, &model, guard)?;
        let retire = |a: &mut Assembler<'_>, owner| {
            a.conversion(
                constant("IRByteMemoryV1"),
                app("ir_byte_retire_v1", [owner, mem.clone()]),
                mem.clone(),
            )
        };
        let leaf = retire(&mut a, root.next.clone())?;
        let caller = retire(&mut a, root.owner.clone())?;
        let candidate = recipe
            .execute_entry(&mut a, &model, mem, nat(0), ready, admitted, leaf, caller)
            .map_err(|e| format!("universal word Core fetched execution: {e}"))?;
        let closed = scope
            .close(&raw.lam(candidate.run.equality().term().clone()))
            .map_err(|e| e.to_string())?;
        let encoded =
            trust_ir::proof::encode_clean_expr_dag_v2(&closed).map_err(|e| e.to_string())?;
        let _ = environment;
        self.check_universal_entry_proof(&encoded)
            .map_err(|e| format!("universal word Core closed replay: {e}"))
    }
}

/// Ordinary report-bound empty-memory/Nat-HOST0 universal derivation. Original
/// SOURCE_CALL tables remain attached and independently replayed; reflection
/// does not strip them. Logical addresses are nonzero IDs, never native pointers.
#[cfg(feature = "source-value-operational")]
pub fn derive_defined_word_add_call_entry<'module>(
    report: &crate::ModuleValidationReport<'module>,
    caller: FuncId,
    callee: FuncId,
) -> Result<CheckedDefinedWordAddCallEntry<'module>> {
    let module: &'module Module = report
        .validated_module()
        .ok_or("universal word Add needs successful original report")?;
    let addresses = module
        .functions
        .iter()
        .map(|f| (f.id, u64::from(f.id.index()) + 1))
        .collect::<Vec<_>>();
    let reflected =
        crate::source_call_operational::reflect_source_call_core_module_v1(report, &addresses)
            .map_err(|e| e.to_string())?;
    let mut catalog = Catalog::new(canonical_environment()?, &reflected, limits())?;
    let owner = catalog.defined_word_add_call(caller, callee)?;
    let checked = owner.derive_universal_entry()?;
    checked.functions_in(module)?;
    // Reborrow the SAME original report's module, never a clone/digest stand-in.
    // All other fields are the closed independently checked owned terms.
    Ok(CheckedDefinedWordAddCallEntry {
        module,
        caller: checked.caller,
        callee: checked.callee,
        offset: checked.offset,
        judgment: checked.judgment,
        proof: checked.proof,
        environment: checked.environment,
        codec_claim: checked.codec_claim,
        codec_proof: checked.codec_proof,
    })
}
