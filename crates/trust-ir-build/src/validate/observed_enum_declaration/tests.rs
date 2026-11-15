// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Independent oracle for the ordinary physical declaration checks.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{EnumTagRepr, EnumVariant};
use trust_ir::value::EnumId;
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
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original enum declaration stop");
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
    ExecutionSite::Entry(FuncId::new(133))
}
fn variant(name: &str, fields: Vec<Ty>, names: Vec<String>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: names,
    }
}
fn fixture() -> Module {
    let mut m = Module::new("enum declaration");
    m.enums.push(EnumDef::new(
        EnumId::new(7),
        "fullλ'\nname",
        vec![
            variant("A", vec![], vec![]),
            variant("B", vec![Ty::U8], vec!["b".into()]),
        ],
    ));
    m
}
fn oracle(m: &Module, index: usize) -> Vec<ValidationError> {
    let enm = &m.enums[index];
    let mut errors = Vec::new();
    if m.enums[..index].iter().any(|row| row.id == enm.id) {
        errors.push(ValidationError::DuplicateEnumId(enm.id.index()));
    }
    if enm.effective_discriminants().is_none() {
        errors.push(ValidationError::ConstTypeMismatch {
            location: format!("enum.{} ({})", enm.id.index(), enm.name),
            expected: "resolvable, duplicate-free discriminant assignment".into(),
            actual: "ill-formed discriminants".into(),
        });
    } else if enm.canonical_tag_repr().is_none()
        && !(enm.variants.is_empty()
            && enm.discriminants.is_empty()
            && enm.repr.is_none()
            && enm.layout.is_none())
    {
        errors.push(ValidationError::ConstTypeMismatch {
            location: format!("enum.{} ({})", enm.id.index(), enm.name),
            expected: "a canonical tag repr (non-empty, values fit the hint and the 64-bit cap)"
                .into(),
            actual: "no canonical tag".into(),
        });
    }
    for (variant_index, variant) in enm.variants.iter().enumerate() {
        if !variant.field_names.is_empty() && variant.field_names.len() != variant.fields.len() {
            errors.push(ValidationError::ConstTypeMismatch {
                location: format!(
                    "enum.{} ({}) variant {} ({})",
                    enm.id.index(),
                    enm.name,
                    variant_index,
                    variant.name
                ),
                expected: format!(
                    "field_names empty or exactly {} entries",
                    variant.fields.len()
                ),
                actual: format!("{} field names", variant.field_names.len()),
            });
        }
    }
    errors
}
fn run(m: &Module, index: usize) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_enum_declaration_observed(m, index, &mut s, site()).unwrap();
    assert_eq!(out, oracle(m, index));
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
fn private_trace(m: &Module, index: usize) -> Observer {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.run(m, index, &mut work).unwrap();
    assert_eq!(state.errors, oracle(m, index));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State) -> bool {
    s.values.capacity() == 0
        && s.location.capacity() == 0
        && s.expected.capacity() == 0
        && s.actual.capacity() == 0
        && s.errors.capacity() == 0
}
