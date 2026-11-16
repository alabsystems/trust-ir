// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real observed direct-call control frames. The original operation owns the
//! one session, instruction fuel and shared memory; only SSA environments are
//! moved into saved callers. No ordinary executor or Rust recursion is used.
use super::*;

struct Active<'m> {
    function: &'m Function,
    block: &'m Block,
    abi: Option<typed_abi::Plan<'m>>,
    owned: byval::Scope,
    next: usize,
}
#[derive(Clone, Copy)]
enum Target {
    Direct(FuncId),
    Indirect {
        value: ValueId,
        signature: FuncTyId,
        convention: crate::CallingConv,
    },
}

struct Caller<'m> {
    active: Active<'m>,
    values: BTreeMap<ValueId, InterpretValue>,
    node: &'m InstrNode,
    site: InstructionSite,
}

/// Executable call/function-value modules need the same complete type-bearing
/// floor as typed modules. Inspect actual call and function-value metadata
/// under the original observer before ANY instruction, without executing an
/// unsupported node. Other no-call legacy programs retain their type scope.
pub(super) fn preflight<O: ExecutionObserver>(
    interpreter: &Interpreter<'_>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    let module = interpreter
        .module
        .ok_or(Fault::Unsupported("observed direct call module"))?;
    let mut calls = false;
    for ty in &module.types {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        calls |= matches!(ty, Ty::Func(_));
    }
    for signature in &module.func_types {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for ty in signature.params.iter().chain(&signature.returns) {
            event(session, site, ExecutionPhase::Validation, 1, 0)?;
            calls |= matches!(ty, Ty::Func(_));
        }
    }
    for function in &module.functions {
        event(session, site, ExecutionPhase::Validation, 1, 0)?;
        for block in &function.blocks {
            event(session, site, ExecutionPhase::Validation, 1, 0)?;
            for (_, ty) in &block.params {
                event(session, site, ExecutionPhase::Validation, 1, 0)?;
                calls |= matches!(ty, Ty::Func(_));
            }
            for node in &block.body {
                event(session, site, ExecutionPhase::Validation, 1, 0)?;
                calls |= matches!(
                    node.inst,
                    Inst::Call { .. }
                        | Inst::CallIndirect { .. }
                        | Inst::Const {
                            ty: Ty::Func(_),
                            ..
                        }
                        | Inst::Copy {
                            ty: Ty::Func(_),
                            ..
                        }
                        | Inst::Select {
                            ty: Ty::Func(_),
                            ..
                        }
                        | Inst::Load {
                            ty: Ty::Func(_),
                            ..
                        }
                        | Inst::Store {
                            ty: Ty::Func(_),
                            ..
                        }
                        | Inst::Alloca {
                            ty: Ty::Func(_),
                            ..
                        }
                );
            }
        }
    }
    if calls {
        typed_abi::check_module_types(module, session, site)?;
    }
    Ok(())
}

fn arguments<O: ExecutionObserver>(
    ids: &[ValueId],
    state: &ExecState,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<Vec<InterpretValue>> {
    let at = ExecutionSite::Instruction(site);
    let mut values = Vec::new();
    let result = (|| {
        reserve(&mut values, ids.len(), session, at)?;
        for id in ids {
            event(session, at, ExecutionPhase::EntryArguments, 1, 0)?;
            let value = lookup(state, *id, site.block, session, at)?;
            values.push(clone_value_owned(value, &mut session.structural_owned(at))?);
        }
        Ok(())
    })();
    match result {
        Ok(()) => Ok(values),
        Err(error) => {
            retire_values(values, &mut session.structural_owned(at));
            Err(error)
        }
    }
}

fn retire_map<O: ExecutionObserver>(
    values: &mut BTreeMap<ValueId, InterpretValue>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    while !values.is_empty() {
        // Bound the actual std B-tree removal before performing it; retirement
        // remains mandatory and visible after a sticky admission refusal.
        session.retirement_step(site, values.len().saturating_add(1));
        if let Some((_, value)) = values.pop_first() {
            ObservedRopeElem::retire_observed(value, &mut session.structural_owned(site));
        }
    }
    session.retirement_step(site, 1);
}

pub(super) struct Progress<'a> {
    last: &'a mut ExecutionSite,
    dispatched: &'a mut bool,
}

impl<'a> Progress<'a> {
    pub(super) fn new(last: &'a mut ExecutionSite, dispatched: &'a mut bool) -> Self {
        Self { last, dispatched }
    }
}

/// One interpreter control loop for root and actual direct/function-pointer callees. Every
/// active/saved frame has exactly one owner on every return, panic, capacity,
/// fuel, deadline or cancellation exit. `dispatched` records a REAL direct-call instruction,
/// not a capability, caller-controlled switch or permission to publish.
pub(super) fn run<'m, O: ExecutionObserver>(
    interpreter: &Interpreter<'m>,
    function: &'m Function,
    abi: Option<typed_abi::Plan<'m>>,
    input: &mut Vec<InterpretValue>,
    state: &mut ExecState,
    session: &mut ObservedSession<'_, O>,
    progress: Progress<'_>,
) -> RunResult<Vec<InterpretValue>> {
    let Progress { last, dispatched } = progress;
    if function.blocks.len() != 1 || function.blocks[0].id != function.entry {
        return Err(Fault::Unsupported("multi-block observed execution"));
    }
    let entry = ExecutionSite::Entry(function.id);
    let block = &function.blocks[0];
    let mut owned = match &abi {
        Some(abi) => abi.arguments(interpreter, input, state, session, entry, function.entry)?,
        None => byval::Scope::default(),
    };
    let bound = startup::bind_entry(
        interpreter,
        function,
        block,
        abi.as_ref(),
        input,
        state,
        session,
    );
    if let Err(error) = bound {
        owned.retire(&mut state.memory, session, entry).ok();
        return Err(error);
    }
    let mut active = Active {
        function,
        block,
        abi,
        owned,
        next: 0,
    };
    let mut callers = Vec::<Caller<'m>>::new();
    let result: RunResult<Vec<InterpretValue>> = (|| {
        loop {
            let node: &'m InstrNode = active.block.body.get(active.next).ok_or_else(|| {
                Fault::Semantic(err(
                    InterpretErrorCode::MalformedInstruction,
                    active.block.id,
                    "observed block ended without a terminator",
                ))
            })?;
            let site = InstructionSite {
                function: active.function.id,
                block: active.block.id,
                instruction_index: active.next,
            };
            *last = ExecutionSite::Instruction(site);
            match session.begin_instruction(site) {
                Ok(()) => state.steps += 1,
                Err(StepStopped::Admission) => return Err(Fault::Admission),
                Err(StepStopped::Fuel) => {
                    return Err(Fault::Semantic(err(
                        InterpretErrorCode::OutOfFuel,
                        site.block,
                        "original observed fuel exhausted",
                    )));
                }
            }
            active.next = active.next.checked_add(1).ok_or(Fault::Representation)?;
            let target = match &node.inst {
                Inst::Call { callee, args } => Some((Target::Direct(*callee), args.as_slice())),
                Inst::CallIndirect {
                    callee,
                    sig,
                    args,
                    calling_conv,
                } => Some((
                    Target::Indirect {
                        value: *callee,
                        signature: *sig,
                        convention: *calling_conv,
                    },
                    args.as_slice(),
                )),
                _ => None,
            };
            if let Some((target, args)) = target {
                *dispatched = true;
                let at = ExecutionSite::Instruction(site);
                // This node is dispatched HERE rather than through step's
                // fixed scalar diagnostics, so prepay its own bounded errors.
                event(session, at, ExecutionPhase::HostAllocation, 1, 512)?;
                let mut pointer = None;
                let mut supplied = Vec::new();
                let mut owned = byval::Scope::default();
                let prepared: RunResult<(&'m Function, Option<typed_abi::Plan<'m>>)> = (|| {
                    // Ordinary evaluation clones the actual pointer BEFORE the
                    // argument list, and validates it only after that list.
                    if let Target::Indirect { value, .. } = target {
                        let value = lookup(state, value, site.block, session, at)?;
                        pointer = Some(cloned(BindOrigin::OwnedCall, value, session, at)?);
                    }
                    supplied = arguments(args, state, session, site)?;
                    let (function, abi) = match target {
                        Target::Direct(callee) => {
                            event(session, at, ExecutionPhase::EntryArguments, 1, 0)?;
                            let depth =
                                u64::try_from(callers.len()).map_err(|_| Fault::Representation)?;
                            if depth >= session.options.max_call_depth {
                                return Err(Fault::Semantic(err(
                                    InterpretErrorCode::OutOfFuel,
                                    site.block,
                                    "interpreter call depth exhausted",
                                )));
                            }
                            startup::prepare_call(interpreter, callee, &supplied, session, site)?
                        }
                        Target::Indirect {
                            signature,
                            convention,
                            ..
                        } => startup::prepare_indirect(
                            interpreter,
                            pointer.as_ref().ok_or(Fault::Representation)?,
                            &supplied,
                            session,
                            startup::IndirectCall::new(signature, convention, callers.len(), site),
                        )?,
                    };
                    if let Some(abi) = &abi {
                        owned = abi.arguments(
                            interpreter,
                            &mut supplied,
                            state,
                            session,
                            ExecutionSite::Entry(function.id),
                            site.block,
                        )?;
                    }
                    reserve(&mut callers, 1, session, at)?;
                    event(
                        session,
                        at,
                        ExecutionPhase::BlockParameters,
                        1,
                        size_of::<Caller<'_>>(),
                    )?;
                    Ok((function, abi))
                })(
                );
                if let Some(pointer) = pointer {
                    BindOrigin::OwnedCall.retire_value(pointer, session, at);
                }
                let (function, abi) = match prepared {
                    Ok(prepared) if session.first_refusal().is_none() => prepared,
                    Ok(_) => {
                        owned.retire(&mut state.memory, session, at).ok();
                        retire_values(supplied, &mut session.structural_owned(at));
                        return Err(Fault::Admission);
                    }
                    Err(error) => {
                        owned.retire(&mut state.memory, session, at).ok();
                        retire_values(supplied, &mut session.structural_owned(at));
                        return Err(error);
                    }
                };
                let block = &function.blocks[0];
                let previous = core::mem::replace(
                    &mut active,
                    Active {
                        function,
                        block,
                        abi,
                        owned,
                        next: 0,
                    },
                );
                let values = core::mem::take(&mut state.values);
                callers.push(Caller {
                    active: previous,
                    values,
                    node,
                    site,
                });
                let bound = startup::bind_call_entry(
                    interpreter,
                    function,
                    block,
                    active.abi.as_ref(),
                    &mut supplied,
                    state,
                    session,
                );
                retire_values(supplied, &mut session.structural_owned(at));
                bound?;
                continue;
            }
            // Only a real saved caller makes this instruction callee-owned.
            // Root execution retains its original local retirement policy.
            let origin = if callers.is_empty() {
                BindOrigin::Existing
            } else {
                BindOrigin::OwnedCall
            };
            let Some(mut returns) = step::execute(
                interpreter,
                active.abi.as_ref(),
                node,
                state,
                session,
                site,
                origin,
            )?
            else {
                continue;
            };
            let checked = (|| {
                startup::check_returns(
                    interpreter,
                    active.function,
                    active.abi.as_ref(),
                    &returns,
                    session,
                    *last,
                )?;
                if let Some(abi) = &active.abi {
                    abi.returns(
                        interpreter,
                        &mut returns,
                        state,
                        session,
                        *last,
                        active.function.entry,
                    )?;
                }
                Ok(())
            })();
            if let Err(error) = checked {
                if *dispatched {
                    BindOrigin::OwnedCall.retire_values(returns, session, *last);
                } else {
                    BindOrigin::Existing.retire_values(returns, session, *last);
                }
                return Err(error);
            }
            if let Err(error) = active.owned.retire(&mut state.memory, session, *last) {
                BindOrigin::OwnedCall.retire_values(returns, session, *last);
                return Err(error);
            }
            if callers.is_empty() {
                return Ok(returns);
            }
            // Retire only the actual completed callee SSA environment. Memory
            // stays shared, matching ordinary interpreter allocation lifetime;
            // this is not a physical/compiler stack-frame or borrow proof.
            retire_map(&mut state.values, session, *last);
            if session.first_refusal().is_some() {
                retire_values(returns, &mut session.structural_owned(*last));
                return Err(Fault::Admission);
            }
            let restored = (|| {
                event(
                    session,
                    *last,
                    ExecutionPhase::BlockParameters,
                    1,
                    size_of::<Caller<'_>>(),
                )?;
                callers.pop().ok_or(Fault::Representation)
            })();
            let caller = match restored {
                Ok(caller) => caller,
                Err(error) => {
                    retire_values(returns, &mut session.structural_owned(*last));
                    return Err(error);
                }
            };
            state.values = caller.values;
            active = caller.active;
            *last = ExecutionSite::Instruction(caller.site);
            bind_call(state, caller.node, returns, session, caller.site)?;
        }
    })();
    // Copies outlive every callee instruction, but never the frame. Pending
    // scopes before frame installation are drained above; failed active and
    // saved frames are drained here under the same original owner.
    let cleanup = active.owned.retire(&mut state.memory, session, *last);
    let result = match (result, cleanup) {
        (Ok(values), Err(error)) => {
            BindOrigin::OwnedCall.retire_values(values, session, *last);
            Err(error)
        }
        (result, _) => result,
    };
    // On a failed entry/bind or any later exit, drain every saved/active map
    // iteratively. Never recurse through source-controlled frame ownership.
    if *dispatched {
        retire_map(&mut state.values, session, *last);
        while !callers.is_empty() {
            session.retirement_step(*last, 1);
            if let Some(mut caller) = callers.pop() {
                caller
                    .active
                    .owned
                    .retire(&mut state.memory, session, *last)
                    .ok();
                retire_map(&mut caller.values, session, *last);
            }
        }
        memory::retire_call_memory(&mut state.memory, session, *last);
    }
    if callers.capacity() != 0 {
        session.retirement_step(*last, 1);
    }
    if *dispatched && session.first_refusal().is_some() {
        match result {
            Ok(returns) => {
                BindOrigin::OwnedCall.retire_values(returns, session, *last);
            }
            Err(Fault::Semantic(error)) => {
                super::super::value::retire_error_owned(error, session, *last)
            }
            Err(_) => {}
        }
        Err(Fault::Admission)
    } else {
        result
    }
}
