// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN composition controls; exact ordinary full block is the oracle.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant};
use trust_ir::value::EnumId;
mod original;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
    trigger: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) || self.trigger.as_ref().is_some_and(|a| a.get()) {
            return Err("original full enum stop");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(137))
}
fn row(id: u32) -> EnumDef {
    let mut e = EnumDef::new(
        EnumId::new(id),
        format!("E{id}λ"),
        vec![
            EnumVariant {
                name: "Data".into(),
                fields: vec![Ty::U8],
                field_names: vec![],
            },
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    );
    e.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U8,
        },
        size: 1,
        align: 1,
        variant_field_offsets: vec![vec![0], vec![]],
    });
    e
}
fn fixture() -> Module {
    let mut m = Module::new("full enums");
    m.enums.push(row(7));
    m
}
fn invalid() -> Module {
    let mut m = fixture();
    let e = &mut m.enums[0];
    e.variants[0].field_names = vec!["x".into(), "y".into()];
    let l = e.layout.as_mut().unwrap();
    l.align = 0;
    l.variant_field_offsets[0].push(0);
    l.encoding = EnumTagEncoding::Untagged;
    let second = e.clone();
    m.enums.push(second);
    m
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_enums_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, original::run(m));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
fn private_trace(m: &Module) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.run(m, &mut work).unwrap();
    assert_eq!(state.errors, original::run(m));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State) -> bool {
    s.batch.is_none() && s.pending.is_none() && s.errors.capacity() == 0
}
