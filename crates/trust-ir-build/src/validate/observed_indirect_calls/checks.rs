// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::while_let_loop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Clone, Copy)]
pub(super) struct Edge<'a> {
    pub(super) callee: ValueId,
    pub(super) sig: trust_ir::FuncTyId,
    pub(super) args: &'a [ValueId],
    pub(super) conv: CallingConv,
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        context: &mut ObservedIndirectCalls<'_, '_>,
        physical_block: usize,
        index: usize,
        values: &ObservedValueTypes,
        nominal: Option<&ObservedNominalTypeReachability<'_>>,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let block = work
            .at(&context.function.blocks, physical_block)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let node = work
            .at(&block.body, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        work.admit(16, size_of::<Edge<'_>>())?;
        let edge = match &node.inst {
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            }
            | Inst::CallIndirectCannotUnwind {
                callee,
                sig,
                args,
                calling_conv,
            }
            | Inst::InvokeIndirect {
                callee,
                sig,
                args,
                calling_conv,
                ..
            } => Edge {
                callee: *callee,
                sig: *sig,
                args,
                conv: *calling_conv,
            },
            _ => return Ok(()),
        };
        let Some(signature) = work.at(
            &context.catalog.source_module().func_types,
            edge.sig.as_usize(),
        )?
        else {
            return self.push(
                ValidationError::CallIndirectSigNotFound {
                    block: block.id.index(),
                    sig_id: edge.sig.index(),
                },
                work,
            );
        };
        work.admit(4, size_of::<bool>())?;
        if let Some(abi) = &signature.abi
            && abi.lowered_convention != edge.conv
        {
            self.ready(work)?;
            work.text("indirect edge in ", &mut self.detail)?;
            work.text(&context.function.name, &mut self.detail)?;
            work.text(" bb", &mut self.detail)?;
            work.number(block.id.index() as usize, &mut self.detail)?;
            work.text(" changes the typed calling convention", &mut self.detail)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::InvalidSignatureAbi {
                signature: edge.sig.index(),
                detail: take(&mut self.detail),
            });
        }
        if signature.is_vararg && matches!(edge.conv, CallingConv::Rust) {
            self.ready(work)?;
            work.text("indirect call edge in bb", &mut self.detail)?;
            work.number(block.id.index() as usize, &mut self.detail)?;
            work.text(
                " declares the Rust calling convention over variadic functy.",
                &mut self.detail,
            )?;
            work.number(edge.sig.index() as usize, &mut self.detail)?;
            work.text(" (", &mut self.detail)?;
            work.number(signature.params.len(), &mut self.detail)?;
            work.text(" fixed parameter(s))", &mut self.detail)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::RustAbiVararg {
                function: context.function.id.index(),
                detail: take(&mut self.detail),
            });
        }
        self.arguments(
            context.function,
            &edge,
            signature,
            values,
            nominal,
            block.id,
            work,
        )?;
        self.function_item(context, &edge, values, block.id, work)?;
        self.closure(context, &edge, signature, values, block.id, work)?;
        self.pointer(context, &edge, signature, block.id, index, work)
    }
    fn function_item<O: ExecutionObserver>(
        &mut self,
        context: &mut ObservedIndirectCalls<'_, '_>,
        edge: &Edge<'_>,
        values: &ObservedValueTypes,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(12, size_of::<Option<FuncId>>() + size_of::<bool>())?;
        let ty = values.get_observed(edge.callee, work.session, work.site)?;
        let id = match ty {
            Some(Ty::FnItem(id)) => Some(*id),
            Some(Ty::Func(_)) if context.has_item_origins(work)? => context
                .pointers
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .resolve_item_for_rejection_observed(edge.callee, work.session, work.site)?,
            _ => None,
        };
        let Some(id) = id else {
            return Ok(());
        };
        let target = context
            .catalog
            .unique_observed(id, work.session, work.site)?;
        let valid = match target {
            Some(target) => work
                .at(
                    &context.catalog.source_module().func_types,
                    target.ty.as_usize(),
                )?
                .is_some(),
            None => false,
        };
        if !valid {
            // The ordinary reified-pointer branch only adds rejection when a
            // nominal source header resolves. Its typed constant/reference
            // rules diagnose malformed origins separately.
            if matches!(ty, Some(Ty::Func(_))) {
                return Ok(());
            }
            self.ready(work)?;
            work.text("function '", &mut self.detail)?;
            work.text(&context.function.name, &mut self.detail)?;
            work.text("' bb", &mut self.detail)?;
            work.number(block.index() as usize, &mut self.detail)?;
            work.text(" indirect callee", &mut self.detail)?;
            work.text("a unique nominal function item", &mut self.expected)?;
            if let Some(target) = target {
                work.text("function item func.", &mut self.actual)?;
                work.number(id.index() as usize, &mut self.actual)?;
                work.text(" has missing signature functy.", &mut self.actual)?;
                work.number(target.ty.index() as usize, &mut self.actual)?;
            } else {
                work.text("missing or ambiguous function item func.", &mut self.actual)?;
                work.number(id.index() as usize, &mut self.actual)?;
            }
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::ConstTypeMismatch {
                location: take(&mut self.detail),
                expected: take(&mut self.expected),
                actual: take(&mut self.actual),
            });
            return Ok(());
        }
        let target = target.ok_or(ObservedValueError::InvalidRange)?;
        if target.ty != edge.sig {
            self.ready(work)?;
            work.text(&target.name, &mut self.name)?;
            work.text("functy.", &mut self.expected)?;
            work.number(edge.sig.index() as usize, &mut self.expected)?;
            work.text("functy.", &mut self.actual)?;
            work.number(target.ty.index() as usize, &mut self.actual)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors
                .push(ValidationError::CallEdgeSignatureMismatch {
                    block: block.index(),
                    callee: take(&mut self.name),
                    declared: take(&mut self.expected),
                    actual: take(&mut self.actual),
                });
        }
        if target.calling_conv != edge.conv {
            self.ready(work)?;
            work.text(&target.name, &mut self.name)?;
            render::convention(edge.conv, &mut self.expected, work)?;
            render::convention(target.calling_conv, &mut self.actual, work)?;
            work.reserve(&mut self.errors)?;
            work.admit(1, size_of::<ValidationError>())?;
            self.errors.push(ValidationError::CallEdgeConvMismatch {
                block: block.index(),
                callee: take(&mut self.name),
                declared: take(&mut self.expected),
                actual: take(&mut self.actual),
            });
        }
        Ok(())
    }
    fn arguments<O: ExecutionObserver>(
        &mut self,
        caller: &Function,
        edge: &Edge<'_>,
        signature: &FuncTy,
        values: &ObservedValueTypes,
        nominal: Option<&ObservedNominalTypeReachability<'_>>,
        block: BlockId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(4, 2 * size_of::<usize>() + size_of::<bool>())?;
        let mismatch = if signature.is_vararg {
            work.admit(1, size_of::<Vec<ValidationError>>())?;
            self.pending = validate_nominal_varargs_observed(
                edge.args,
                signature.params.len(),
                values,
                nominal,
                &caller.name,
                work.session,
                work.site,
            )?;
            self.merge(work)?;
            edge.args.len() < signature.params.len()
        } else {
            edge.args.len() != signature.params.len()
        };
        if mismatch {
            self.push(
                ValidationError::CallIndirectArgCountMismatch {
                    block: block.index(),
                    sig_id: edge.sig.index(),
                    expected: signature.params.len(),
                    actual: edge.args.len(),
                },
                work,
            )?;
        }
        let mut at = 0;
        loop {
            let Some(arg) = work.at(edge.args, at)? else {
                break;
            };
            let Some(expected) = work.at(&signature.params, at)? else {
                break;
            };
            if let Some(actual) = values.get_observed(*arg, work.session, work.site)?
                && !actual.structural_eq_observed(expected, work.session, work.site)?
            {
                work.admit(3, size_of::<bool>())?;
                if !(actual.is_refine() || expected.is_refine()) {
                    self.ready(work)?;
                    self.expected = expected.display_observed(work.session, work.site)?;
                    self.actual = actual.display_observed(work.session, work.site)?;
                    work.reserve(&mut self.errors)?;
                    work.admit(1, size_of::<ValidationError>())?;
                    self.errors
                        .push(ValidationError::CallIndirectArgTypeMismatch {
                            block: block.index(),
                            sig_id: edge.sig.index(),
                            arg_index: at,
                            expected: take(&mut self.expected),
                            actual: take(&mut self.actual),
                        });
                }
            }
            work.next(&mut at)?;
        }
        Ok(())
    }
}
