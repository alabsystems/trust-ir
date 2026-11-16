// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive, fail-closed observed execution. Unsupported modes never dispatch
//! to the ordinary interpreter: that would lose the original resource owner.

use super::super::*;
use super::value::{clone_value, clone_value_owned, flat_type, retire_values, scalar_type};
use super::*;
use core::mem::size_of;

mod byval;
mod calls;
mod memory;
mod startup;
mod step;
mod typed_abi;

pub(super) enum Fault {
    Admission,
    Semantic(InterpretError),
    Unsupported(&'static str),
    Representation,
}

impl From<ObservationStopped> for Fault {
    fn from(_: ObservationStopped) -> Self {
        Self::Admission
    }
}

impl From<ObservedValueError> for Fault {
    fn from(error: ObservedValueError) -> Self {
        match error {
            ObservedValueError::AdmissionRefused => Self::Admission,
            ObservedValueError::UnsupportedValue => Self::Unsupported("value representation"),
            _ => Self::Representation,
        }
    }
}

impl From<InterpretError> for Fault {
    fn from(error: InterpretError) -> Self {
        Self::Semantic(error)
    }
}

pub(super) type RunResult<T> = Result<T, Fault>;

pub(super) fn event<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    phase: ExecutionPhase,
    work: usize,
    copy_bytes: usize,
) -> RunResult<()> {
    session
        .admit(ExecutionProgress {
            phase,
            site,
            work,
            copy_bytes,
        })
        .map_err(Fault::from)
}

pub(super) fn reserve<T, O: ExecutionObserver>(
    values: &mut Vec<T>,
    count: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<()> {
    let needed = values
        .len()
        .checked_add(count)
        .ok_or(Fault::Representation)?;
    if needed <= values.capacity() {
        return Ok(());
    }
    let capacity = needed
        .max(
            values
                .capacity()
                .checked_mul(2)
                .ok_or(Fault::Representation)?,
        )
        .max(4);
    let bytes = capacity
        .checked_mul(size_of::<T>())
        .ok_or(Fault::Representation)?;
    let work = capacity.checked_add(1).ok_or(Fault::Representation)?;
    event(session, site, ExecutionPhase::HostAllocation, work, bytes)?;
    values
        .try_reserve_exact(capacity - values.len())
        .map_err(|_| Fault::Representation)
}

pub(super) fn lookup<'a, O: ExecutionObserver>(
    state: &'a ExecState,
    id: ValueId,
    block: BlockId,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<&'a InterpretValue> {
    event(
        session,
        site,
        ExecutionPhase::Instruction,
        map_work(state.values.len())?,
        0,
    )?;
    Ok(state.value(block, id)?)
}

pub(super) fn map_work(len: usize) -> RunResult<usize> {
    Ok(super::btree::population_work(len)?)
}

pub(super) fn map_insert<K, V, O: ExecutionObserver>(
    len: usize,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    phase: ExecutionPhase,
) -> RunResult<()> {
    let cost = super::btree::insertion_cost::<K, V>(len)?;
    event(session, site, phase, cost.work, cost.copy_bytes)
}

/// Keep every source-sized owned prefix in the original cleanup scope on ALL
/// failures, including a failed lookup/clone after many successful elements.
pub(super) fn owned_values<'o, O: ExecutionObserver>(
    capacity: usize,
    origin: BindOrigin,
    session: &mut ObservedSession<'o, O>,
    site: ExecutionSite,
    build: impl FnOnce(&mut Vec<InterpretValue>, &mut ObservedSession<'o, O>) -> RunResult<()>,
) -> RunResult<Vec<InterpretValue>> {
    let mut values = Vec::new();
    let result =
        reserve(&mut values, capacity, session, site).and_then(|()| build(&mut values, session));
    match result {
        Ok(()) => Ok(values),
        Err(error) => {
            origin.retire_values(values, session, site);
            Err(error)
        }
    }
}

pub(super) fn cloned<O: ExecutionObserver>(
    origin: BindOrigin,
    value: &InterpretValue,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> RunResult<InterpretValue> {
    Ok(match origin {
        BindOrigin::Existing => clone_value(value, &mut session.structural(site))?,
        BindOrigin::OwnedCall => clone_value_owned(value, &mut session.structural_owned(site))?,
    })
}

pub(super) fn bind<O: ExecutionObserver>(
    state: &mut ExecState,
    node: &InstrNode,
    values: Vec<InterpretValue>,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    bind_core(state, node, values, session, site, BindOrigin::Existing)
}

pub(super) fn bind_call<O: ExecutionObserver>(
    state: &mut ExecState,
    node: &InstrNode,
    values: Vec<InterpretValue>,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
) -> RunResult<()> {
    bind_core(state, node, values, session, site, BindOrigin::OwnedCall)
}

#[derive(Clone, Copy)]
pub(super) enum BindOrigin {
    Existing,
    OwnedCall,
}
impl BindOrigin {
    fn retire_value<O: ExecutionObserver>(
        self,
        value: InterpretValue,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        match self {
            Self::Existing => {
                value.retire_observed(session, site).ok();
            }
            Self::OwnedCall => {
                ObservedRopeElem::retire_observed(value, &mut session.structural_owned(site))
            }
        }
    }
    fn progress<'s, 'o, O: ExecutionObserver>(
        self,
        session: &'s mut ObservedSession<'o, O>,
        site: ExecutionSite,
    ) -> SessionProgress<'s, 'o, O> {
        match self {
            Self::Existing => session.structural(site),
            Self::OwnedCall => session.structural_owned(site),
        }
    }
    fn retire_values<O: ExecutionObserver>(
        self,
        values: Vec<InterpretValue>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        let allocated = values.capacity() != 0;
        self.retire_backing(allocated, session, site);
        match self {
            Self::Existing => retire_values(values, &mut session.structural(site)),
            Self::OwnedCall => retire_values(values, &mut session.structural_owned(site)),
        }
    }
    fn retire_backing<O: ExecutionObserver>(
        self,
        allocated: bool,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        if allocated && matches!(self, Self::OwnedCall) {
            session.retirement_step(site, 1);
        }
    }
    // These paths previously used an implicit local drop. Only actual new
    // callee execution selects owned retirement; root legacy policy is exact.
    fn retire_temporary<O: ExecutionObserver>(
        self,
        value: InterpretValue,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        match self {
            Self::Existing => drop(value),
            Self::OwnedCall => self.retire_value(value, session, site),
        }
    }
    fn retire_temporaries<O: ExecutionObserver>(
        self,
        values: Vec<InterpretValue>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        match self {
            Self::Existing => drop(values),
            Self::OwnedCall => self.retire_values(values, session, site),
        }
    }
    fn retire_bytes<O: ExecutionObserver>(
        self,
        bytes: Vec<Option<u8>>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) {
        if matches!(self, Self::OwnedCall) {
            for _ in &bytes {
                session.retirement_step(site, 1);
            }
            self.retire_backing(bytes.capacity() != 0, session, site);
        }
        drop(bytes);
    }
}

fn bind_core<O: ExecutionObserver>(
    state: &mut ExecState,
    node: &InstrNode,
    values: Vec<InterpretValue>,
    session: &mut ObservedSession<'_, O>,
    site: InstructionSite,
    origin: BindOrigin,
) -> RunResult<()> {
    if node.results.len() != values.len() {
        origin.retire_values(values, session, ExecutionSite::Instruction(site));
        return Err(Fault::Semantic(err(
            InterpretErrorCode::MalformedInstruction,
            site.block,
            "observed instruction result count mismatch",
        )));
    }
    let at = ExecutionSite::Instruction(site);
    let allocated = values.capacity() != 0;
    let mut values = values.into_iter();
    for id in &node.results {
        let Some(value) = values.next() else {
            break;
        };
        if let Err(error) = map_insert::<ValueId, InterpretValue, O>(
            state.values.len(),
            session,
            at,
            ExecutionPhase::HostAllocation,
        ) {
            origin.retire_value(value, session, at);
            origin.retire_backing(allocated, session, at);
            for remaining in values {
                origin.retire_value(remaining, session, at);
            }
            return Err(error);
        }
        if let Err(error) = check_char_validity(&value, site.block) {
            origin.retire_value(value, session, at);
            origin.retire_backing(allocated, session, at);
            for remaining in values {
                origin.retire_value(remaining, session, at);
            }
            return Err(Fault::Semantic(error));
        }
        if let Some(old) = state.values.insert(*id, value) {
            origin.retire_value(old, session, at);
        }
    }
    origin.retire_backing(allocated, session, at);
    drop(values);
    Ok(())
}

fn fresh_state() -> ExecState {
    ExecState {
        values: BTreeMap::new(),
        provenance: provenance::State::default(),
        memory: MemoryState::default(),
        globals: BTreeMap::new(),
        frames: BTreeSet::new(),
        next_frame_id: 0,
        steps: 0,
        remaining_fuel: 0,
        host: HostState::new(),
        host_calls: 0,
        drop_glue: None,
        unwind: UnwindState::default(),
    }
}

impl Interpreter<'_> {
    /// Execute under the caller's existing session. Fuel, observer refusal and
    /// cumulative debits are retained over every attempt with that session.
    /// Direct and function-value calls share this same session and owned
    /// control stack. Hosts, closure application, unwinding and non-byte
    /// aggregate memory remain unsupported; no ordinary fallback is attempted.
    pub fn execute_func_observed<O: ExecutionObserver>(
        &self,
        function: FuncId,
        mut arguments: Vec<InterpretValue>,
        session: &mut ObservedSession<'_, O>,
    ) -> ObservedReport {
        let _pointer_width = PointerWidthScope::enter(64);
        let entry = ExecutionSite::Entry(function);
        let mut state = fresh_state();
        let mut last = entry;
        let mut calls_dispatched = false;
        let result = (|| {
            // Fixed diagnostic storage is prepaid before any entry error can
            // allocate its String. Recursive/source-sized diagnostics are not
            // part of this observed closure.
            event(session, entry, ExecutionPhase::HostAllocation, 1, 512)?;
            let (function, abi) = startup::prepare(self, function, &arguments, session)?;
            calls::preflight(self, session, entry)?;
            state.memory = self.initial_memory(function.entry)?;
            calls::run(
                self,
                function,
                abi,
                &mut arguments,
                &mut state,
                session,
                calls::Progress::new(&mut last, &mut calls_dispatched),
            )
        })();
        // No successful publication precedes retirement of interpreter-owned
        // values, memory runs and borrowed startup scratch. Cleanup polls the
        // original observer even after the first refusal, never a fresh grant.
        retire_values(arguments, &mut session.structural(last));
        while let Some((_, value)) = state.values.pop_first() {
            session.retirement_poll(last);
            value.retire_observed(session, last).ok();
        }
        memory::retire(&mut state.memory, session, last);
        let exit = match result {
            Ok(returns) => ObservedExit::Returned(InterpretOutcome {
                returns,
                steps: state.steps,
                host_calls: 0,
            }),
            Err(Fault::Admission) => ObservedExit::AdmissionRefused,
            Err(Fault::Unsupported(instruction)) => ObservedExit::UnsupportedObservation {
                site: last,
                instruction,
            },
            Err(Fault::Representation) => ObservedExit::InterpreterLimit {
                site: last,
                error: InterpretError::new(
                    InterpretErrorCode::OutOfMemory,
                    "observed host representation could not be retained",
                ),
            },
            Err(Fault::Semantic(error)) => match last {
                ExecutionSite::Entry(_) => ObservedExit::EntryRejected(error),
                ExecutionSite::Instruction(_)
                    if matches!(
                        error.code,
                        InterpretErrorCode::OutOfFuel | InterpretErrorCode::OutOfMemory
                    ) =>
                {
                    ObservedExit::InterpreterLimit { site: last, error }
                }
                ExecutionSite::Instruction(site) => ObservedExit::ExecutedError { site, error },
            },
        };
        let mut report = ObservedReport {
            exit,
            steps: state.steps,
            host_calls: 0,
        };
        let final_poll = session.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: last,
            work: 0,
            copy_bytes: 0,
        });
        if final_poll.is_err() || session.first_refusal.is_some() {
            if calls_dispatched {
                report.retire_owned(session, last).ok();
            } else {
                report.retire_observed(session, last).ok();
            }
            report = ObservedReport {
                exit: ObservedExit::AdmissionRefused,
                steps: state.steps,
                host_calls: 0,
            };
        }
        report
    }
}
