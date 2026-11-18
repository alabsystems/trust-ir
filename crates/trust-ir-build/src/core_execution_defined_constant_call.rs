// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Assemble the original two-function CALL/CONST/RETURN/RETURN execution.
//! No replacement constant caller, new evaluator or assumed callee summary is
//! used. These remain untrusted candidates until complete closed kernel replay.
//! Native BL/frame, source-language correspondence and provider permissions are
//! separate contracts. Root return clears its owner stack; it does not leave
//! the entire world unchanged. The internal call advances NEXT exactly once.
use super::*;
use trust_ir::{CallingConv, Constant, Inst, Linkage, Module, Ty};

#[derive(Clone)]
pub struct DefinedConstantCall<'module> {
    reflected: &'module ReflectedCoreModuleV1<'module>,
    caller: FuncId,
    caller_entry: BlockId,
    callee: FuncId,
    word: u64,
    call: FetchedSite,
    constant: Option<FetchedSite>,
    parameters: Option<(ValueId, ValueId)>,
    forward_add: Option<word_add::ForwardAdd>,
    leaf_return: FetchedSite,
    caller_return: FetchedSite,
    leaf: InternalTarget,
    caller_target: CallTarget,
    entry: EntryTarget,
    leaf_result: ValueId,
    caller_result: ValueId,
}

impl<'e, 'm> Catalog<'e, 'm> {
    /// First profile: exactly two defined, attribute-free C () -> I64/U64
    /// functions, an internal constant leaf and its real direct caller.
    /// Negative Int literals and recorded frontend ABIs require another owner.
    pub fn defined_constant_call(
        &mut self,
        caller: FuncId,
        callee: FuncId,
    ) -> Result<DefinedConstantCall<'m>> {
        let module = self.reflected.module();
        if caller == callee || module.functions.len() != 2 {
            return Err("defined constant call requires two distinct original functions".into());
        }
        let cf = self
            .reflected
            .function(caller)
            .ok_or("missing original caller")?;
        let lf = self
            .reflected
            .function(callee)
            .ok_or("missing original callee")?;
        let signature = |f: &trust_ir::Function| -> Result<&trust_ir::FuncTy> {
            let s = module
                .func_type(f.ty)
                .ok_or("missing defined call signature")?;
            if f.calling_conv != CallingConv::C
                || !f.attrs.is_empty()
                || s.abi.is_some()
                || s.is_vararg
                || !s.params.is_empty()
                || !matches!(s.returns.as_slice(), [Ty::U64] | [Ty::I64])
                || f.blocks.len() != 1
                || f.blocks[0].id != f.entry
                || !f.blocks[0].params.is_empty()
            {
                return Err(
                    "defined constant call requires exact zero-argument word C bodies".into(),
                );
            }
            Ok(s)
        };
        let cs = signature(cf)?;
        let ls = signature(lf)?;
        if cs != ls || lf.linkage != Linkage::Internal {
            return Err("defined constant call ABI or local leaf differs".into());
        }
        let [cn, cr] = cf.blocks[0].body.as_slice() else {
            return Err("caller must contain the original call then return only".into());
        };
        let [ln, lr] = lf.blocks[0].body.as_slice() else {
            return Err("leaf must contain the original constant then return only".into());
        };
        let ([caller_result], [leaf_result]) = (cn.results.as_slice(), ln.results.as_slice())
        else {
            return Err("defined call result arity differs".into());
        };
        let Inst::Const {
            ty,
            value: Constant::Int(word),
        } = &ln.inst
        else {
            return Err("defined leaf lacks its original scalar literal".into());
        };
        let word = u64::try_from(*word)
            .map_err(|_| "defined leaf literal is outside unsigned word slice")?;
        if ty != &ls.returns[0]
            || !matches!(&cn.inst, Inst::Call { callee: f, args } if *f == callee && args.is_empty())
            || !matches!(&cr.inst, Inst::Return { values } if values == &[*caller_result])
            || !matches!(&lr.inst, Inst::Return { values } if values == &[*leaf_result])
            || !cr.results.is_empty()
            || !lr.results.is_empty()
        {
            return Err("defined call target, literal or original returned value differs".into());
        }
        let caller_entry = cf.entry;
        let leaf_entry = lf.entry;
        let caller_result = *caller_result;
        let leaf_result = *leaf_result;
        Ok(DefinedConstantCall {
            reflected: self.reflected,
            caller,
            caller_entry,
            callee,
            word,
            call: self.fetch(Coordinate {
                function: caller,
                block: caller_entry,
                instruction: 0,
            })?,
            parameters: None,
            forward_add: None,
            constant: Some(self.fetch(Coordinate {
                function: callee,
                block: leaf_entry,
                instruction: 0,
            })?),
            leaf_return: self.fetch(Coordinate {
                function: callee,
                block: leaf_entry,
                instruction: 1,
            })?,
            caller_return: self.fetch(Coordinate {
                function: caller,
                block: caller_entry,
                instruction: 1,
            })?,
            leaf: self.internal_target(callee)?,
            caller_target: self.call_target(caller)?,
            entry: self.entry(caller)?,
            leaf_result,
            caller_result,
        })
    }
}

pub struct DefinedConstantCallCandidate {
    pub run: ExactRun,
    pub result: Expr,
    pub terminal_memory: Expr,
    pub terminal_world: Expr,
}

// ReturnFrame retains the actual saved caller through explicit list/world
// constructors. Those endpoints can be definitionally equal without having
// identical Rust Expr trees. Supply an explicit proof candidate at each join;
// strict ExactRun composition is never weakened.
fn join(a: &mut Assembler<'_>, first: ExactRun, second: ExactRun) -> Result<ExactRun> {
    let model = &first.model;
    model.same(&second.model)?;
    let boundary = a.conversion(
        model.config_type(),
        first.reached.clone(),
        second.initial.clone(),
    )?;
    let lifted = a.congruence_function(
        boundary,
        model.config_type(),
        model.run_function(&second.fuel),
    )?;
    let lifted = a.convert_endpoints(
        lifted,
        model.run(&second.fuel, first.reached.clone()),
        second.equality.left.clone(),
    )?;
    let proof = a.compose(lifted, second.equality.clone())?;
    let second = ExactRun::candidate(
        model.clone(),
        first.reached.clone(),
        second.reached,
        second.fuel,
        proof,
    )?;
    a.concatenate(first, second)
}

impl DefinedConstantCall<'_> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        if !std::ptr::eq(module, self.reflected.module()) {
            return Err("defined call belongs to another immutable module".into());
        }
        Ok((self.caller, self.callee))
    }
    pub fn word(&self) -> u64 {
        self.word
    }
    fn argument_word(&self) -> Expr {
        self.forward_add
            .as_ref()
            .map_or_else(|| nat(self.word), |add| add.argument.clone())
    }
    fn result_word(&self) -> Expr {
        self.forward_add
            .as_ref()
            .map_or_else(|| nat(self.word), |add| add.result_word())
    }
    fn admission_evidence(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        guard: Expr,
    ) -> Result<PendingEquality> {
        match &self.forward_add {
            Some(add) => add.argument_admission(a, model, guard),
            None => a.conversion(constant("Bool"), guard, constant("Bool.true")),
        }
    }
    fn return_evidence(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        guard: Expr,
    ) -> Result<PendingEquality> {
        match &self.forward_add {
            Some(add) => add.result_admission(a, model, guard),
            None => a.conversion(constant("Bool"), guard, constant("Bool.true")),
        }
    }
    fn arguments(&self) -> Expr {
        list(
            "IRScalar",
            &self
                .parameters
                .map(|_| app("IRScalar.int_", [self.argument_word()]))
                .into_iter()
                .collect::<Vec<_>>(),
        )
    }
    fn initial_bindings(&self) -> Expr {
        list(
            "IRBinding",
            &self
                .parameters
                .map(|(caller, _)| {
                    app(
                        "IRBinding.mk",
                        [
                            nat(u64::from(caller.index())),
                            app("IRScalar.int_", [self.argument_word()]),
                        ],
                    )
                })
                .into_iter()
                .collect::<Vec<_>>(),
        )
    }
    fn argument_ids(&self) -> Expr {
        list(
            "Nat",
            &self
                .parameters
                .map(|(caller, _)| nat(u64::from(caller.index())))
                .into_iter()
                .collect::<Vec<_>>(),
        )
    }
    fn initial_frame(&self) -> Expr {
        app(
            "IRFrame.mk",
            [
                nat(u64::from(self.caller.index())),
                nat(u64::from(self.caller_entry.index())),
                nat(0),
                self.initial_bindings(),
                list("Nat", &[]),
            ],
        )
    }
    pub fn root(&self, memory: Expr, host: Expr, owner: Expr, next: Expr) -> RootReturnFrame {
        RootReturnFrame {
            returning: self.initial_frame(),
            legacy_memory: list("IRMemSlot", &[]),
            legacy_cursor: nat(0),
            memory,
            host,
            owner,
            next,
        }
    }
    /// The real Core initializer chooses the root owner from the original
    /// memory. This expression supplies no initialization/validity evidence.
    pub fn entry_root(&self, memory: Expr, host: Expr) -> RootReturnFrame {
        let owner = app("ir_byte_fresh_owner_v1", [memory.clone()]);
        self.root(memory, host, owner.clone(), app("Nat.succ", [owner]))
    }
    pub fn entry_admission(&self, model: &MachineModel) -> Result<Expr> {
        self.entry.admission(model, self.arguments())
    }
    /// Complete execution beginning at the ACTUAL initializer, not an assumed
    /// pre-existing activation. Its memory/value guards and two retirement
    /// facts are independently checked premises of the final closed query.
    pub fn execute_entry(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        memory: Expr,
        host: Expr,
        initial_memory: PendingEquality,
        admitted: PendingEquality,
        leaf_retired_same: PendingEquality,
        root_retired_same: PendingEquality,
    ) -> Result<DefinedConstantCallCandidate> {
        let initialization = self.entry.initialize(
            a,
            model,
            self.arguments(),
            memory.clone(),
            host.clone(),
            initial_memory,
            admitted,
        )?;
        let root = self.entry_root(memory, host);
        let before = a.convert_endpoints(
            initialization.valid().clone(),
            root.current(model).valid(model),
            constant("Bool.true"),
        )?;
        let mut candidate = self.execute_root(
            a,
            model,
            &root,
            before,
            leaf_retired_same,
            root_retired_same,
        )?;
        let initial = initialization.equality().left().clone();
        let ready = a.convert_endpoints(
            initialization.equality().clone(),
            initial.clone(),
            candidate.run.initial().clone(),
        )?;
        let lifted = a.congruence_function(
            ready,
            model.config_type(),
            model.run_function(candidate.run.fuel()),
        )?;
        let lifted = a.convert_endpoints(
            lifted,
            model.run(candidate.run.fuel(), initial.clone()),
            candidate.run.equality().left().clone(),
        )?;
        let equality = a.compose(lifted, candidate.run.equality().clone())?;
        candidate.run = ExactRun::candidate(
            model.clone(),
            initial,
            candidate.run.reached().clone(),
            candidate.run.fuel().clone(),
            equality,
        )?;
        Ok(candidate)
    }
    /// Exact independently replayable retirement endpoints. Initialized memory
    /// is not permission to retire an owner, and root-owned live allocations
    /// cannot satisfy the second equality merely by matching these endpoints.
    pub fn retirement_obligations(&self, root: &RootReturnFrame) -> [Expr; 2] {
        [root.next.clone(), root.owner.clone()].map(|owner| {
            eq(
                &constant("IRByteMemoryV1"),
                app("ir_byte_retire_v1", [owner, root.memory.clone()]),
                root.memory.clone(),
            )
        })
    }

    pub fn execute_root(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        root: &RootReturnFrame,
        before: PendingEquality,
        leaf_retired_same: PendingEquality,
        root_retired_same: PendingEquality,
    ) -> Result<DefinedConstantCallCandidate> {
        require_same(
            model.context(),
            self.reflected.context_term(),
            "defined call model context",
        )?;
        require_same(
            &root.returning,
            &self.initial_frame(),
            "defined call exact original root entry",
        )?;
        let obligations = self.retirement_obligations(root);
        require_same(
            &leaf_retired_same.proposition(),
            &obligations[0],
            "defined leaf retirement",
        )?;
        require_same(
            &root_retired_same.proposition(),
            &obligations[1],
            "defined caller retirement",
        )?;
        let caller = root.current(model);
        let values = self.arguments();
        let checks = self.leaf.checks(model, &self.call, values.clone())?;
        let dispatch = self
            .leaf
            .call_target()
            .direct(a, model, &caller, &self.call)?;
        let resolved = a.conversion(
            app("IRList", [constant("IRScalar")]),
            app("ir_resolve", [caller.machine(), self.argument_ids()]),
            values,
        )?;
        let local_binding = a.conversion(
            constant("Bool"),
            checks.local_binding,
            constant("Bool.false"),
        )?;
        let arity = a.conversion(constant("Bool"), checks.arity, constant("Bool.true"))?;
        let admitted = self.admission_evidence(a, model, checks.admitted)?;
        let entered = self.call.call_internal(
            a,
            model,
            &self.leaf,
            &caller,
            InternalCallPremises {
                dispatch,
                resolved,
                local_binding,
                arity,
                admitted,
                before,
            },
        )?;
        let value = app("IRScalar.int_", [self.result_word()]);
        let loaded = if let Some(fetched_constant) = &self.constant {
            let constant_value = self.forward_add.as_ref().map_or_else(
                || value.clone(),
                |add| app("IRScalar.int_", [nat(add.offset)]),
            );
            let checks =
                fetched_constant.scalar_checks(model, entered.current(), constant_value.clone())?;
            let evaluated = a.conversion(
                constant("IRStepResult"),
                checks.evaluation,
                app("IRStepResult.value", [constant_value.clone()]),
            )?;
            let operands =
                a.conversion(constant("Bool"), checks.operands, constant("Bool.true"))?;
            let result = a.conversion(constant("Bool"), checks.result, constant("Bool.true"))?;
            let loaded = fetched_constant.scalar_value(
                a,
                model,
                entered.current(),
                constant_value.clone(),
                ScalarPremises {
                    evaluated,
                    operands,
                    result,
                    before: entered.valid().clone(),
                },
            )?;
            Some(loaded)
        } else {
            None
        };
        let added = if let Some(add) = &self.forward_add {
            let loaded = loaded
                .as_ref()
                .ok_or("word add requires actual preceding constant")?;
            Some(add.execute(a, model, loaded.current(), loaded.valid().clone())?)
        } else {
            None
        };
        let leaf_current = added
            .as_ref()
            .map(|step| step.current())
            .or_else(|| loaded.as_ref().map(|step| step.current()))
            .unwrap_or(entered.current());
        let leaf_valid = added
            .as_ref()
            .map(|step| step.valid())
            .or_else(|| loaded.as_ref().map(|step| step.valid()))
            .unwrap_or(entered.valid());
        let values = list("IRScalar", std::slice::from_ref(&value));
        let mut leaf_frame = entered.return_frame().clone();
        leaf_frame.returning = leaf_current.frame.clone();
        let resolved = a.conversion(
            app("IRList", [constant("IRScalar")]),
            app(
                "ir_resolve",
                [
                    leaf_frame.current(model).machine(),
                    list("Nat", &[nat(u64::from(self.leaf_result.index()))]),
                ],
            ),
            values.clone(),
        )?;
        let guard = self.leaf_return.return_admission(
            model,
            self.leaf.call_target(),
            &leaf_frame,
            values.clone(),
        )?;
        let admitted = self.return_evidence(a, model, guard)?;
        let before = a.convert_endpoints(
            leaf_valid.clone(),
            leaf_frame.current(model).valid(model),
            constant("Bool.true"),
        )?;
        let returned = self.leaf_return.return_to_caller(
            a,
            model,
            self.leaf.call_target(),
            &leaf_frame,
            resolved,
            admitted,
            before,
        )?;
        let leaf_memory = app(
            "ir_byte_retire_v1",
            [root.next.clone(), root.memory.clone()],
        );
        let terminal_root = RootReturnFrame {
            returning: returned.resumed().frame.clone(),
            legacy_memory: returned.resumed().legacy_memory.clone(),
            legacy_cursor: returned.resumed().legacy_cursor.clone(),
            memory: leaf_memory,
            host: root.host.clone(),
            owner: root.owner.clone(),
            next: app("Nat.succ", [root.next.clone()]),
        };
        let before = a.convert_endpoints(
            returned.valid().clone(),
            terminal_root.current(model).valid(model),
            constant("Bool.true"),
        )?;
        let resolved = a.conversion(
            app("IRList", [constant("IRScalar")]),
            app(
                "ir_resolve",
                [
                    terminal_root.current(model).machine(),
                    list("Nat", &[nat(u64::from(self.caller_result.index()))]),
                ],
            ),
            values.clone(),
        )?;
        let guard = self.caller_return.root_return_admission(
            model,
            &self.caller_target,
            &terminal_root,
            values.clone(),
        )?;
        let admitted = self.return_evidence(a, model, guard)?;
        let halted = self.caller_return.return_from_root(
            a,
            model,
            &self.caller_target,
            &terminal_root,
            resolved,
            admitted,
            before,
        )?;
        let run = if let Some(loaded) = &loaded {
            join(a, entered.run().clone(), loaded.run().clone())
                .map_err(|e| format!("call/constant join: {e}"))?
        } else {
            entered.run().clone()
        };
        let run = if let Some(added) = &added {
            join(a, run, added.run().clone())?
        } else {
            run
        };
        let run =
            join(a, run, returned.run().clone()).map_err(|e| format!("leaf return join: {e}"))?;
        let run =
            join(a, run, halted.run().clone()).map_err(|e| format!("root return join: {e}"))?;
        let memory = a.congruence(leaf_retired_same, constant("IRByteMemoryV1"), |memory| {
            app("ir_byte_retire_v1", [root.owner.clone(), memory])
        })?;
        let memory = a.convert_endpoints(
            memory,
            app(
                "ir_byte_retire_v1",
                [
                    root.owner.clone(),
                    app(
                        "ir_byte_retire_v1",
                        [root.next.clone(), root.memory.clone()],
                    ),
                ],
            ),
            root_retired_same.left.clone(),
        )?;
        let memory = a.compose(memory, root_retired_same)?;
        let world = |memory| {
            app(
                "IRByteWorldV1.mk",
                [
                    model.world_type().clone(),
                    memory,
                    root.host.clone(),
                    list("Nat", &[]),
                    app("Nat.succ", [root.next.clone()]),
                ],
            )
        };
        let terminal_world = world(root.memory.clone());
        let normalize = a.congruence(memory, model.config_type(), |memory| {
            app(
                "IRByteConfigV1.halted",
                [
                    model.world_type().clone(),
                    app("IROutcome.ret", [values.clone()]),
                    world(memory),
                ],
            )
        })?;
        let normalize = a.convert_endpoints(
            normalize,
            run.reached().clone(),
            app(
                "IRByteConfigV1.halted",
                [
                    model.world_type().clone(),
                    app("IROutcome.ret", [values]),
                    terminal_world.clone(),
                ],
            ),
        )?;
        let equality = a.compose(run.equality().clone(), normalize)?;
        let run = ExactRun::candidate(
            model.clone(),
            caller.running(model),
            equality.right().clone(),
            run.fuel().clone(),
            equality,
        )?;
        Ok(DefinedConstantCallCandidate {
            run,
            result: value,
            terminal_memory: root.memory.clone(),
            terminal_world,
        })
    }
}

/// Pointwise original one-word forward call. Its actual u64 argument is part
/// of the closed initializer claim; this is never a universal callable permit.
pub struct DefinedWordForwardCall<'module> {
    inner: DefinedConstantCall<'module>,
}
impl<'e, 'm> Catalog<'e, 'm> {
    pub fn defined_word_forward_call(
        &mut self,
        caller: FuncId,
        callee: FuncId,
        argument: u64,
    ) -> Result<DefinedWordForwardCall<'m>> {
        let module = self.reflected.module();
        if caller == callee || module.functions.len() != 2 {
            return Err("word forward call requires two distinct original functions".into());
        }
        let cf = self
            .reflected
            .function(caller)
            .ok_or("missing original forward caller")?;
        let lf = self
            .reflected
            .function(callee)
            .ok_or("missing original forward callee")?;
        let signature = |f: &trust_ir::Function| -> Result<&trust_ir::FuncTy> {
            let signature = module
                .func_type(f.ty)
                .ok_or("missing forward call signature")?;
            if f.calling_conv != CallingConv::C
                || !f.attrs.is_empty()
                || signature.abi.is_some()
                || signature.is_vararg
                || signature.params != [Ty::U64]
                || signature.returns != [Ty::U64]
                || f.blocks.len() != 1
                || f.blocks[0].id != f.entry
            {
                return Err(
                    "word forward call requires exact attribute-free C(U64)->U64 bodies".into(),
                );
            }
            Ok(signature)
        };
        if signature(cf)? != signature(lf)? || lf.linkage != Linkage::Internal {
            return Err("word forward call ABI/local leaf differs".into());
        }
        let [(cp, Ty::U64)] = cf.blocks[0].params.as_slice() else {
            return Err("forward caller parameter differs".into());
        };
        let [(lp, Ty::U64)] = lf.blocks[0].params.as_slice() else {
            return Err("forward leaf parameter differs".into());
        };
        let [call, ret] = cf.blocks[0].body.as_slice() else {
            return Err("forward caller requires actual call/return only".into());
        };
        let [leaf_ret] = lf.blocks[0].body.as_slice() else {
            return Err("forward leaf requires actual parameter return only".into());
        };
        let [result] = call.results.as_slice() else {
            return Err("forward call result arity differs".into());
        };
        if !matches!(&call.inst, Inst::Call{callee:f,args} if *f==callee && args==&[*cp])
            || !matches!(&ret.inst,Inst::Return{values} if values==&[*result])
            || !matches!(&leaf_ret.inst,Inst::Return{values} if values==&[*lp])
            || !ret.results.is_empty()
            || !leaf_ret.results.is_empty()
        {
            return Err("forward call target/argument/original return differs".into());
        }
        let (ce, le, cp, lp, result) = (cf.entry, lf.entry, *cp, *lp, *result);
        Ok(DefinedWordForwardCall {
            inner: DefinedConstantCall {
                reflected: self.reflected,
                caller,
                caller_entry: ce,
                callee,
                word: argument,
                call: self.fetch(Coordinate {
                    function: caller,
                    block: ce,
                    instruction: 0,
                })?,
                constant: None,
                parameters: Some((cp, lp)),
                forward_add: None,
                leaf_return: self.fetch(Coordinate {
                    function: callee,
                    block: le,
                    instruction: 0,
                })?,
                caller_return: self.fetch(Coordinate {
                    function: caller,
                    block: ce,
                    instruction: 1,
                })?,
                leaf: self.internal_target(callee)?,
                caller_target: self.call_target(caller)?,
                entry: self.entry(caller)?,
                leaf_result: lp,
                caller_result: result,
            },
        })
    }
}
impl DefinedWordForwardCall<'_> {
    pub fn argument(&self) -> u64 {
        self.inner.word
    }
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId)> {
        self.inner.functions_in(module)
    }
    pub fn entry_root(&self, memory: Expr, host: Expr) -> RootReturnFrame {
        self.inner.entry_root(memory, host)
    }
    pub fn entry_admission(&self, model: &MachineModel) -> Result<Expr> {
        self.inner.entry_admission(model)
    }
    pub fn retirement_obligations(&self, root: &RootReturnFrame) -> [Expr; 2] {
        self.inner.retirement_obligations(root)
    }
    pub fn execute_entry(
        &self,
        a: &mut Assembler<'_>,
        model: &MachineModel,
        memory: Expr,
        host: Expr,
        initial_memory: PendingEquality,
        admitted: PendingEquality,
        leaf_retired_same: PendingEquality,
        root_retired_same: PendingEquality,
    ) -> Result<DefinedConstantCallCandidate> {
        self.inner.execute_entry(
            a,
            model,
            memory,
            host,
            initial_memory,
            admitted,
            leaf_retired_same,
            root_retired_same,
        )
    }
}

#[cfg(test)]
#[path = "core_execution_defined_constant_call_tests.rs"]
mod tests;

#[cfg(feature = "source-value-operational")]
#[path = "core_execution_defined_constant_call_checked.rs"]
mod checked;
#[cfg(feature = "source-value-operational")]
pub use checked::{CheckedDefinedConstantCallEntry, CheckedDefinedWordForwardCallEntry};

#[cfg(all(test, feature = "source-value-operational"))]
#[path = "core_execution_word_forward_call_tests.rs"]
mod word_forward_tests;

#[path = "core_execution_defined_word_add_call.rs"]
mod word_add;
#[cfg(feature = "source-value-operational")]
pub use word_add::{
    CheckedDefinedWordAddCallEntry, DefinedWordAddCall, derive_defined_word_add_call_entry,
};
