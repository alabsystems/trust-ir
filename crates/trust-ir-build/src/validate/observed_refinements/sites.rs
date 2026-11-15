// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use graph::Flow;
mod fields;
#[derive(Clone, Copy)]
enum IndirectKind {
    Call,
    Invoke,
}
impl<'a> State<'a> {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        self.tables(module, work)?;
        self.occurrences(module, work)?;
        if module.predicates.is_empty() {
            return Ok(());
        }
        for function in &module.functions {
            work.admit(1, size_of::<Flow<'a>>())?;
            let mut flow = Flow::default();
            let result = (|| {
                work.admit(1, size_of::<Option<ObservedValueTypes>>())?;
                flow.values = Some(build_module_value_types_observed(
                    function,
                    module,
                    work.session,
                    work.site,
                )?);
                let signature = work.at(&module.func_types, function.ty.as_usize())?;
                flow.propagate(self, module, function, signature, work)?;
                flow.frames(function, work)?;
                self.function(module, function, signature, &mut flow, work)
            })();
            // Whole child and every partial/replaced fact/frame/edge buffer
            // are owned by flow until this unconditional original retirement.
            flow.retire(work);
            result?;
        }
        Ok(())
    }
    pub(super) fn value<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        flow: &Flow<'_>,
        value: ValueId,
        required: &Ty,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(actual) = flow.value(value, work)? else {
            return Ok(());
        };
        let derived = flow.fact(value.index(), work)?;
        self.consumption(
            module,
            actual,
            required,
            Some(derived),
            &flow.facts,
            Sink::Main,
            work,
        )
    }
    fn edge<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        flow: &Flow<'_>,
        from: u32,
        target: u32,
        args: &[ValueId],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(block) = graph::block(function, target, work)? else {
            return Ok(());
        };
        for (i, (arg, (_, required))) in args.iter().zip(&block.params).enumerate() {
            work.admit(1, 0)?;
            self.base(&function.name, Some(from), work)?;
            work.text(" -> bb", &mut self.base_location)?;
            work.number(target as u128, &mut self.base_location)?;
            work.text(" join arg ", &mut self.base_location)?;
            work.number(i as u128, &mut self.base_location)?;
            self.value(module, flow, *arg, required, work)?;
        }
        Ok(())
    }
    fn call<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        flow: &Flow<'_>,
        block: u32,
        callee: FuncId,
        args: &[ValueId],
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(callee) = consumption::callee(module, callee, work)? else {
            return Ok(());
        };
        let Some(signature) = work.at(&module.func_types, callee.ty.as_usize())? else {
            return Ok(());
        };
        for (i, (arg, required)) in args.iter().zip(&signature.params).enumerate() {
            work.admit(1, 0)?;
            self.base(&function.name, Some(block), work)?;
            work.text(": call @", &mut self.base_location)?;
            work.text(&callee.name, &mut self.base_location)?;
            work.text(" arg ", &mut self.base_location)?;
            work.number(i as u128, &mut self.base_location)?;
            self.value(module, flow, *arg, required, work)?;
        }
        Ok(())
    }
    fn indirect<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        flow: &Flow<'_>,
        block: u32,
        sig: trust_ir::value::FuncTyId,
        args: &[ValueId],
        kind: IndirectKind,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let Some(signature) = work.at(&module.func_types, sig.as_usize())? else {
            return Ok(());
        };
        for (i, (arg, required)) in args.iter().zip(&signature.params).enumerate() {
            work.admit(1, 0)?;
            self.base(&function.name, Some(block), work)?;
            work.text(
                if matches!(kind, IndirectKind::Invoke) {
                    ": invoke_indirect functy."
                } else {
                    ": call_indirect functy."
                },
                &mut self.base_location,
            )?;
            work.number(sig.index() as u128, &mut self.base_location)?;
            work.text(" arg ", &mut self.base_location)?;
            work.number(i as u128, &mut self.base_location)?;
            self.value(module, flow, *arg, required, work)?;
        }
        Ok(())
    }
    fn function<O: ExecutionObserver>(
        &mut self,
        module: &'a Module,
        function: &'a Function,
        signature: Option<&FuncTy>,
        flow: &mut Flow<'a>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        if let Some(signature) = signature {
            let mut entry = None;
            for block in &function.blocks {
                work.admit(1, 0)?;
                if block.id == function.entry {
                    entry = Some(block);
                    break;
                }
            }
            if let Some(entry) = entry {
                for (i, ((_, declared), from_signature)) in
                    entry.params.iter().zip(&signature.params).enumerate()
                {
                    work.admit(1, 0)?;
                    self.base(&function.name, None, work)?;
                    work.text(" entry param ", &mut self.base_location)?;
                    work.number(i as u128, &mut self.base_location)?;
                    self.consumption(
                        module,
                        from_signature,
                        declared,
                        None,
                        &flow.facts,
                        Sink::Main,
                        work,
                    )?;
                }
            }
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            let id = block.id.index();
            for node in &block.body {
                work.admit(1, size_of::<ConsumptionRole>())?;
                let role = match consumption_role(&node.inst) {
                    ConsumptionRole::Checked(site) => site,
                    ConsumptionRole::NoDeclaredRequirement(_)
                    | ConsumptionRole::ConsumesNoValue => continue,
                };
                match role {
                    CheckedConsumption::BranchArgs => {
                        flow.edges(&node.inst, work)?;
                        for edge in &flow.edges {
                            work.admit(1, 0)?;
                            if edge.kind == EdgeKind::Normal {
                                self.edge(
                                    module,
                                    function,
                                    flow,
                                    id,
                                    edge.target.index(),
                                    edge.args,
                                    work,
                                )?;
                            }
                        }
                        work.retire_vec(&mut flow.edges);
                    }
                    CheckedConsumption::DirectCallArgs => {
                        if let Inst::Call { callee, args }
                        | Inst::CallCannotUnwind { callee, args } = &node.inst
                        {
                            self.call(module, function, flow, id, *callee, args, work)?;
                        }
                    }
                    CheckedConsumption::InvokeArgsAndNormalEdge => {
                        if let Inst::Invoke {
                            callee,
                            args,
                            normal_dest,
                            normal_args,
                            ..
                        } = &node.inst
                        {
                            self.call(module, function, flow, id, *callee, args, work)?;
                            self.edge(
                                module,
                                function,
                                flow,
                                id,
                                normal_dest.index(),
                                normal_args,
                                work,
                            )?;
                        }
                    }
                    CheckedConsumption::IndirectCallArgs => {
                        if let Inst::CallIndirect { sig, args, .. }
                        | Inst::CallIndirectCannotUnwind { sig, args, .. } = &node.inst
                        {
                            self.indirect(
                                module,
                                function,
                                flow,
                                id,
                                *sig,
                                args,
                                IndirectKind::Call,
                                work,
                            )?;
                        }
                    }
                    CheckedConsumption::IndirectInvokeArgsAndNormalEdge => {
                        if let Inst::InvokeIndirect {
                            sig,
                            args,
                            normal_dest,
                            normal_args,
                            ..
                        } = &node.inst
                        {
                            self.indirect(
                                module,
                                function,
                                flow,
                                id,
                                *sig,
                                args,
                                IndirectKind::Invoke,
                                work,
                            )?;
                            self.edge(
                                module,
                                function,
                                flow,
                                id,
                                normal_dest.index(),
                                normal_args,
                                work,
                            )?;
                        }
                    }
                    CheckedConsumption::ReturnValues => {
                        let (values, what) = match &node.inst {
                            Inst::Return { values } => (values.as_slice(), "return value"),
                            Inst::CoroSuspend { value, .. } => {
                                (core::slice::from_ref(value), "coro_suspend yield")
                            }
                            _ => continue,
                        };
                        if let Some(signature) = signature {
                            for (i, (value, required)) in
                                values.iter().zip(&signature.returns).enumerate()
                            {
                                work.admit(1, 0)?;
                                self.base(&function.name, Some(id), work)?;
                                work.text(": ", &mut self.base_location)?;
                                work.text(what, &mut self.base_location)?;
                                work.text(" ", &mut self.base_location)?;
                                work.number(i as u128, &mut self.base_location)?;
                                self.value(module, flow, *value, required, work)?;
                            }
                        }
                    }
                    CheckedConsumption::StoreValue => {
                        let (ty, value, what) = match &node.inst {
                            Inst::Store { ty, value, .. } => (ty, *value, "store"),
                            Inst::AtomicStore { ty, value, .. } => (ty, *value, "atomic_store"),
                            Inst::AtomicRMW { ty, value, .. } => (ty, *value, "atomic_rmw"),
                            Inst::CmpXchg { ty, desired, .. } => (ty, *desired, "cmpxchg"),
                            _ => continue,
                        };
                        self.base(&function.name, Some(id), work)?;
                        work.text(": ", &mut self.base_location)?;
                        work.text(what, &mut self.base_location)?;
                        work.text(" value", &mut self.base_location)?;
                        self.value(module, flow, value, ty, work)?;
                    }
                    CheckedConsumption::FieldWrite => {
                        self.field_write(module, function, flow, id, &node.inst, work)?
                    }
                    CheckedConsumption::FieldRead => {
                        self.field_read(module, function, flow, id, &node.inst, work)?
                    }
                }
            }
        }
        Ok(())
    }
}
