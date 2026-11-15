// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; oracle retains the original physical repr block.
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::{FieldDef, StructDef};
use trust_ir::value::StructId;
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
            return Err("original struct ABI stop");
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
    ExecutionSite::Entry(FuncId::new(135))
}
fn strukt(
    id: u32,
    repr: StructRepr,
    fields: Vec<Ty>,
    size: Option<u64>,
    align: Option<u64>,
) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("S{id}"),
        repr,
        size,
        align,
        origin: None,
        fields: fields
            .into_iter()
            .enumerate()
            .map(|(i, ty)| FieldDef {
                name: format!("f{i}"),
                ty,
                offset: None,
            })
            .collect(),
    }
}
fn fixture() -> Module {
    let mut m = Module::new("struct ABI");
    m.structs = vec![
        strukt(
            7,
            StructRepr::Transparent,
            vec![Ty::Unit, Ty::U8, Ty::U8],
            None,
            None,
        ),
        strukt(8, StructRepr::Packed(3), vec![], None, None),
    ];
    m
}
fn oracle(module: &Module) -> Vec<ValidationError> {
    let layouts = module.layout_table();
    let mut errors = Vec::new();
    for sd in &module.structs {
        match sd.repr {
            StructRepr::Transparent => {
                let non_zst = sd
                    .fields
                    .iter()
                    .filter(|f| !ty_is_one_zst_in(&layouts, &f.ty))
                    .count();
                if non_zst > 1 {
                    errors.push(ValidationError::TransparentReprFieldCount {
                        struct_id: sd.id.index(),
                        actual_non_zst: non_zst,
                    });
                }
            }
            StructRepr::Packed(align) => {
                if align == 0 || !align.is_power_of_two() {
                    errors.push(ValidationError::PackedReprInvalidAlign {
                        struct_id: sd.id.index(),
                        align,
                    });
                }
            }
            StructRepr::Rust | StructRepr::C => {}
        }
    }
    errors
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_struct_abi_repr_observed(m, &mut s, site()).unwrap();
    assert_eq!(out, oracle(m));
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
    assert_eq!(state.errors, oracle(m));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State<'_>, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State<'_>) -> bool {
    s.table.is_none() && s.shape.is_none() && s.error.is_none() && s.errors.capacity() == 0
}
