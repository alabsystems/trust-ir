// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Derived candidates for a defined, load-only pointer-argument callee.
//! Publication bytes, access, actual call/return execution and retirement are
//! distinct obligations. Nothing here grants native/provider or global-data
//! publication authority; all candidates require independent closed replay.
use super::*;
use trust_ir::{CallingConv, Inst, Linkage, Module, Ty};

/// Exact immutable source/reflection binding. First profile: internal C
/// (Ptr)->U64/I64, one aligned nonvolatile load then return. No annotations
/// substitute for the complete original body.
pub struct ReadonlyEightCallee<'module> {
    reflected: &'module ReflectedCoreModuleV1<'module>,
    function: FuncId,
    ty: Ty,
    parameter: ValueId,
    loaded: ValueId,
    target: InternalTarget,
    load: FetchedSite,
    returning: FetchedSite,
}
impl<'env, 'module> Catalog<'env, 'module> {
    pub fn readonly_eight_callee(&mut self, fid: FuncId) -> Result<ReadonlyEightCallee<'module>> {
        let source = self
            .reflected
            .function(fid)
            .ok_or("readonly callee missing exact function")?;
        let signature = self
            .reflected
            .module()
            .func_type(source.ty)
            .ok_or("readonly callee missing signature")?;
        if source.linkage != Linkage::Internal
            || source.calling_conv != CallingConv::C
            || !source.attrs.is_empty()
            || signature.abi.is_some()
            || signature.is_vararg
            || signature.params != [Ty::Ptr]
            || !matches!(signature.returns.as_slice(), [Ty::U64] | [Ty::I64])
            || source.blocks.len() != 1
            || source.blocks[0].id != source.entry
        {
            return Err(
                "readonly callee requires exact internal C pointer/word ABI and one body block"
                    .into(),
            );
        }
        let block = &source.blocks[0];
        let [(parameter, Ty::Ptr)] = block.params.as_slice() else {
            return Err("readonly callee pointer parameter mismatch".into());
        };
        let [load, ret] = block.body.as_slice() else {
            return Err("readonly callee refuses hidden instructions/effects".into());
        };
        let Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: Some(8),
        } = &load.inst
        else {
            return Err("readonly callee requires one nonvolatile align-eight load".into());
        };
        let [loaded] = load.results.as_slice() else {
            return Err("readonly callee load result arity".into());
        };
        if ptr != parameter
            || ty != &signature.returns[0]
            || !ret.results.is_empty()
            || !matches!(&ret.inst,Inst::Return{values} if values==&[*loaded])
        {
            return Err("readonly callee must return exactly its pointer-argument load".into());
        }
        let coordinate = Coordinate {
            function: fid,
            block: source.entry,
            instruction: 0,
        };
        Ok(ReadonlyEightCallee {
            reflected: self.reflected,
            function: fid,
            ty: ty.clone(),
            parameter: *parameter,
            loaded: *loaded,
            target: self.internal_target(fid)?,
            load: self.fetch(coordinate)?,
            returning: self.fetch(Coordinate {
                instruction: 1,
                ..coordinate
            })?,
        })
    }
}
/// Literal slot selection over an actual published initialized-word prefix.
/// The selected-word equality is a candidate about this exact publication,
/// never permission to reinterpret initialized bytes as a live allocation.
pub struct ReadonlyEightSlot<'publication> {
    publication: &'publication InitializedEightRead,
    index: usize,
    selected: PendingEquality,
    word: Expr,
    address: Expr,
}
impl ReadonlyEightSlot<'_> {
    pub fn address(&self) -> &Expr {
        &self.address
    }
    pub fn index(&self) -> usize {
        self.index
    }
    pub fn publication(&self) -> &InitializedEightRead {
        self.publication
    }
}
fn projection(words: Expr, index: usize) -> Expr {
    let sequence = app("IRList", [constant("Nat")]);
    let optional = app("IROption", [constant("Nat")]);
    // Closed standard list eliminators; this is indexing data, not another
    // memory evaluator. Fixed literal count is charged by the caller.
    let tail = Expr::apps(
        Expr::const_(
            Name::from_string("IRList.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                sequence.clone(),
                sequence.clone(),
            ),
            list("Nat", &[]),
            [constant("Nat"), sequence.clone(), sequence.clone()]
                .into_iter()
                .rev()
                .fold(Expr::bvar(1), |b, t| {
                    Expr::lam(clean_kernel::BinderInfo::Default, t, b)
                }),
            words,
        ],
    );
    let mut words = tail;
    // For zero use original input; otherwise apply tail exactly index times.
    // The caller supplies the actual list separately below.
    for _ in 1..index {
        words = tail_of(words, sequence.clone());
    }
    head_of(words, sequence, optional)
}
fn tail_of(words: Expr, sequence: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("IRList.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                sequence.clone(),
                sequence.clone(),
            ),
            list("Nat", &[]),
            [constant("Nat"), sequence.clone(), sequence]
                .into_iter()
                .rev()
                .fold(Expr::bvar(1), |b, t| {
                    Expr::lam(clean_kernel::BinderInfo::Default, t, b)
                }),
            words,
        ],
    )
}
fn head_of(words: Expr, sequence: Expr, optional: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("IRList.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            constant("Nat"),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                sequence.clone(),
                optional.clone(),
            ),
            app("IROption.none", [constant("Nat")]),
            [constant("Nat"), sequence, optional]
                .into_iter()
                .rev()
                .fold(
                    app("IROption.some", [constant("Nat"), Expr::bvar(2)]),
                    |b, t| Expr::lam(clean_kernel::BinderInfo::Default, t, b),
                ),
            words,
        ],
    )
}
impl Assembler<'_> {
    /// The exact proposition a consumer must prove for a literal selected word.
    pub fn readonly_eight_selected(
        &mut self,
        publication: &InitializedEightRead,
        index: usize,
    ) -> Result<Expr> {
        self.charge()?;
        if index >= publication.count() {
            return Err("readonly table index out of published bounds".into());
        }
        self.items(
            index
                .checked_add(1)
                .ok_or("readonly table index overflow")?,
        )?;
        let words = publication.ordered_words().clone();
        Ok(if index == 0 {
            head_of(
                words,
                app("IRList", [constant("Nat")]),
                app("IROption", [constant("Nat")]),
            )
        } else {
            projection(words, index)
        })
    }
    pub fn readonly_eight_slot<'p>(
        &mut self,
        publication: &'p InitializedEightRead,
        index: usize,
        word: Expr,
        selected: PendingEquality,
    ) -> Result<ReadonlyEightSlot<'p>> {
        self.charge()?;
        let offset = u64::try_from(index)
            .ok()
            .and_then(|n| n.checked_mul(8))
            .ok_or("readonly table byte offset overflow")?;
        if publication.extent().is_none() {
            return Err("readonly table requires actual nonempty byte extent".into());
        }
        let selection = self.readonly_eight_selected(publication, index)?;
        selected.endpoints(
            &app("IROption", [constant("Nat")]),
            &selection,
            &app("IROption.some", [constant("Nat"), word.clone()]),
        )?;
        Ok(ReadonlyEightSlot {
            publication,
            index,
            selected,
            word,
            address: app("Nat.add", [publication.base().clone(), nat(offset)]),
        })
    }
}
pub struct ReadonlyEightEntered<'module> {
    callee: ReadonlyEightCallee<'module>,
    caller: Current,
    transfer: InternalCallTransfer,
}
pub struct ReadonlyEightLoaded<'module, 'publication> {
    entered: ReadonlyEightEntered<'module>,
    slot: ReadonlyEightSlot<'publication>,
    codec: ByteEightCodec,
    transfer: MemoryTransfer,
}
impl ReadonlyEightCallee<'_> {
    pub fn function_in(&self, module: &Module) -> Result<FuncId> {
        if !std::ptr::eq(module, self.reflected.module()) {
            return Err("readonly callee belongs to another immutable module".into());
        }
        Ok(self.function)
    }
    pub fn call_target(&self) -> &InternalTarget {
        &self.target
    }
    pub fn load_site(&self) -> &FetchedSite {
        &self.load
    }
}
impl<'m> ReadonlyEightCallee<'m> {
    pub fn enter(
        self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        caller_site: &FetchedSite,
        caller: &Current,
        premises: InternalCallPremises,
    ) -> Result<ReadonlyEightEntered<'m>> {
        require_same(
            model.context(),
            self.reflected.context_term(),
            "readonly actual model context",
        )?;
        // Exact original direct call and ABI; no external/indirect dispatch claim.
        if !matches!(caller_site.instruction.get_app_args().as_slice(),[fid,_] if *fid==&nat(u64::from(self.function.index())))
            || !matches!(caller_site.instruction.get_app_fn().kind(),ExprKind::Const(n,_) if n==&Name::from_string("IRInst.call"))
        {
            return Err(
                "readonly owner requires an actual direct call to its defined callee".into(),
            );
        }
        let transfer =
            caller_site.call_internal(assembler, model, &self.target, caller, premises)?;
        Ok(ReadonlyEightEntered {
            callee: self,
            caller: caller.clone(),
            transfer,
        })
    }
}
impl ReadonlyEightEntered<'_> {
    pub fn current(&self) -> &Current {
        self.transfer.current()
    }
}
impl<'m> ReadonlyEightEntered<'m> {
    /// Derive the actual fetched load from the shared byte-load theorem. Access
    /// and initialization premises concern the exact published memory/address.
    pub fn load<'p>(
        self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        slot: ReadonlyEightSlot<'p>,
        codec: ByteEightCodec,
        premises: ByteLoadEightPremises,
    ) -> Result<ReadonlyEightLoaded<'m, 'p>> {
        require_same(
            &codec.word,
            &slot.word,
            "readonly codec selected publication word",
        )?;
        require_same(
            &codec.context,
            model.context(),
            "readonly codec actual context",
        )?;
        let expected_ty = app(
            if self.callee.ty == Ty::U64 {
                "IRTy.uint_"
            } else {
                "IRTy.int_"
            },
            [nat(64)],
        );
        require_same(&codec.ty, &expected_ty, "readonly callee nominal codec")?;
        let pointer = app(
            "ir_getd",
            [
                self.current().machine(),
                nat(u64::from(self.callee.parameter.index())),
            ],
        );
        let input = ByteLoadEight {
            pointer,
            address: slot.address.clone(),
            requested_align: nat(8),
            memory: slot.publication.memory().clone(),
        };
        let evaluated = assembler.byte_load_eight(&codec, input, premises)?;
        let result = MemoryResult {
            value: codec.value.clone(),
            memory: slot.publication.memory().clone(),
        };
        let checks = self
            .callee
            .load
            .memory_checks(model, self.current(), &result)?;
        let evaluated =
            assembler.convert_endpoints(evaluated, checks.evaluation, result.result())?;
        let incoming_memory = app(
            "ir_byte_world_memory_v1",
            [model.world_type.clone(), self.current().world.clone()],
        );
        let allocations = assembler.conversion(
            app("IRList", [constant("IRByteAllocationV1")]),
            app("ir_byte_mem_allocs_v1", [result.memory.clone()]),
            app("ir_byte_mem_allocs_v1", [incoming_memory]),
        )?;
        let result_guard =
            assembler.conversion(constant("Bool"), checks.result, constant("Bool.true"))?;
        let transfer = self.callee.load.memory_value(
            assembler,
            model,
            self.current(),
            result,
            MemoryPremises {
                evaluated,
                result: result_guard,
                allocations,
                before: self.transfer.valid().clone(),
            },
        )?;
        Ok(ReadonlyEightLoaded {
            entered: self,
            slot,
            codec,
            transfer,
        })
    }
}
/// Complete derived candidate. NEXT owner identity advances once; Memory/HOST,
/// the caller owner stack and tail are retained, not an entire unchanged world.
pub struct ReadonlyEightCallCandidate {
    pub run: ExactRun,
    pub resumed: Current,
    pub publication_and_run: PendingProof,
}
impl ReadonlyEightLoaded<'_, '_> {
    pub fn current(&self) -> &Current {
        self.transfer.current()
    }
    /// The exact remaining return admission and retire(identity) obligations.
    pub fn return_obligations(&self, model: &MachineModel) -> Result<(Expr, Expr)> {
        let frame = self.return_frame();
        let values = list("IRScalar", std::slice::from_ref(&self.codec.value));
        let admitted = self.entered.callee.returning.return_admission(
            model,
            self.entered.callee.target.call_target(),
            &frame,
            values,
        )?;
        let retired = eq(
            &constant("IRByteMemoryV1"),
            app("ir_byte_retire_v1", [frame.owner, frame.memory.clone()]),
            frame.memory,
        );
        Ok((admitted, retired))
    }
    fn return_frame(&self) -> ReturnFrame {
        let entered = self.entered.transfer.return_frame();
        ReturnFrame {
            returning: self.current().frame.clone(),
            caller: entered.caller.clone(),
            tail: entered.tail.clone(),
            legacy_memory: self.current().legacy_memory.clone(),
            legacy_cursor: self.current().legacy_cursor.clone(),
            memory: self.slot.publication.memory().clone(),
            host: entered.host.clone(),
            owner: entered.owner.clone(),
            owners: entered.owners.clone(),
            next: entered.next.clone(),
        }
    }
    pub fn finish(
        self,
        assembler: &mut Assembler<'_>,
        model: &MachineModel,
        admitted: PendingEquality,
        retired_same: PendingEquality,
    ) -> Result<ReadonlyEightCallCandidate> {
        let frame = self.return_frame();
        let (_, retirement) = self.return_obligations(model)?;
        require_same(
            &retired_same.proposition(),
            &retirement,
            "readonly fresh-owner retirement identity",
        )?;
        let values = list("IRScalar", std::slice::from_ref(&self.codec.value));
        let ids = list("Nat", &[nat(u64::from(self.entered.callee.loaded.index()))]);
        let resolved = assembler.conversion(
            app("IRList", [constant("IRScalar")]),
            app("ir_resolve", [frame.current(model).machine(), ids]),
            values,
        )?;
        let before = assembler.convert_endpoints(
            self.transfer.valid().clone(),
            frame.current(model).valid(model),
            constant("Bool.true"),
        )?;
        let returned = self.entered.callee.returning.return_to_caller(
            assembler,
            model,
            self.entered.callee.target.call_target(),
            &frame,
            resolved,
            admitted,
            before,
        )?;
        let return_run = ExactRun::candidate(
            model.clone(),
            self.current().running(model),
            returned.run().reached().clone(),
            returned.run().fuel().clone(),
            assembler.convert_endpoints(
                returned.run().equality().clone(),
                model.run(returned.run().fuel(), self.current().running(model)),
                returned.run().reached().clone(),
            )?,
        )?;
        let run = assembler.concatenate(
            self.entered.transfer.run().clone(),
            self.transfer.run().clone(),
        )?;
        let run = assembler.concatenate(run, return_run)?;
        let mut resumed = returned.resumed().clone();
        resumed.world = app(
            "IRByteWorldV1.mk",
            [
                model.world_type.clone(),
                frame.memory.clone(),
                frame.host.clone(),
                frame.owners.clone(),
                frame.next.clone(),
            ],
        );
        let map = |memory: Expr| {
            let mut after = resumed.clone();
            after.world = app(
                "IRByteWorldV1.mk",
                [
                    model.world_type.clone(),
                    memory,
                    frame.host.clone(),
                    frame.owners.clone(),
                    frame.next.clone(),
                ],
            );
            after.running(model)
        };
        let preservation = assembler.congruence(retired_same, model.config_type(), map)?;
        let preservation = assembler.convert_endpoints(
            preservation,
            returned.resumed().running(model),
            resumed.running(model),
        )?;
        let equality = assembler.compose(run.equality().clone(), preservation)?;
        let run = ExactRun::candidate(
            model.clone(),
            run.initial().clone(),
            resumed.running(model),
            run.fuel().clone(),
            equality,
        )?;
        require_same(
            run.initial(),
            &self.entered.caller.running(model),
            "readonly caller initial configuration",
        )?;
        let mut proof =
            PendingProof::candidate(run.equality().proposition(), run.equality().term().clone());
        for fact in [
            self.slot.selected.proposition(),
            self.slot.publication.readback().proposition(),
            self.slot
                .publication
                .extent()
                .ok_or("readonly missing publication extent")?
                .proposition()
                .clone(),
        ]
        .into_iter()
        .zip([
            self.slot.selected.term().clone(),
            self.slot.publication.readback().term().clone(),
            self.slot.publication.extent().unwrap().term().clone(),
        ]) {
            let proposition = app("And", [fact.0.clone(), proof.proposition.clone()]);
            let term = app("And.intro", [fact.0, proof.proposition, fact.1, proof.term]);
            proof = PendingProof::candidate(proposition, term);
        }
        Ok(ReadonlyEightCallCandidate {
            run,
            resumed,
            publication_and_run: proof,
        })
    }
}

#[cfg(test)]
#[path = "core_execution_readonly_indexed_call_tests.rs"]
mod tests;
