// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; unchanged ordinary stage bodies are retained as the oracle.
#![allow(
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::ty::EnumVariant;
use trust_ir::value::{EnumId, StructId};
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
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original enum encoding stop");
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
#[derive(Clone, Copy)]
enum Stage {
    Prelude,
    Encoding,
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(134))
}
fn target(triple: &str) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}
fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    }
}
fn fixture(repr: EnumTagRepr) -> Module {
    let mut m = Module::new("enum encoding");
    m.target_info = Some(target("aarch64-unknown-linux-gnu"));
    let mut enm = EnumDef::new(
        EnumId::new(9),
        "Eλ",
        vec![variant("Data", vec![repr.ty()]), variant("Empty", vec![])],
    );
    enm.repr = Some(repr);
    enm.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: repr,
        },
        size: repr.size_bytes(),
        align: repr.size_bytes(),
        variant_field_offsets: vec![vec![0], vec![]],
    });
    m.enums.push(enm);
    m
}
fn call<O: ExecutionObserver>(
    m: &Module,
    stage: Stage,
    align: Option<u64>,
    s: &mut ObservedSession<'_, O>,
) -> R<Vec<ValidationError>> {
    let e = &m.enums[0];
    let l = e.layout.as_ref().unwrap();
    match stage {
        Stage::Prelude => validate_enum_layout_prelude_observed(m, e, l, s, site()).map(|x| x.0),
        Stage::Encoding => validate_enum_layout_encoding_observed(m, e, l, align, s, site()),
    }
}
fn run(m: &Module, stage: Stage) -> (Vec<ValidationError>, Observer) {
    let enm = &m.enums[0];
    let layout = enm.layout.as_ref().unwrap();
    let (pre, align) = original::prelude(m, enm, layout);
    let expected = match stage {
        Stage::Prelude => pre,
        Stage::Encoding => original::encoding(m, enm, layout, align),
    };
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = call(m, stage, align, &mut s).unwrap();
    assert_eq!(out, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    (out, o)
}
fn raw<O: ExecutionObserver>(
    state: &mut State<'_>,
    enm: &EnumDef,
    layout: &EnumLayoutDescriptor,
    align: Option<u64>,
    work: &mut Work<'_, '_, O>,
) -> R {
    match &layout.encoding {
        EnumTagEncoding::Direct { tag_offset } => {
            state.direct(enm, layout, *tag_offset, align, work)
        }
        EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => state.niche(
            enm,
            layout,
            Niche {
                untagged: *untagged_variant,
                start: *niche_variants_start,
                end: *niche_variants_end,
                value: *niche_start,
                offset: *niche_offset,
                repr: *niche_ty,
            },
            align,
            work,
        ),
        EnumTagEncoding::Untagged | EnumTagEncoding::SingleInhabited { .. } => {
            unreachable!("private trace fixtures exercise only Direct/Niche dispatch")
        }
    }
}
fn private_trace(m: &Module) -> Observer {
    let enm = &m.enums[0];
    let layout = enm.layout.as_ref().unwrap();
    let (_, align) = original::prelude(m, enm, layout);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.table = Some(LayoutTable::new_observed(m, work.session, work.site).unwrap());
    raw(&mut state, enm, layout, align, &mut work).unwrap();
    assert_eq!(state.errors, original::encoding(m, enm, layout, align));
    drain(&mut state, &mut work);
    assert!(empty(&state));
    o
}
fn drain(state: &mut State<'_>, work: &mut Work<'_, '_, impl ExecutionObserver>) {
    state.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut state.errors), work.session, work.site);
}
fn empty(s: &State<'_>) -> bool {
    s.table.is_none()
        && s.shape.is_none()
        && s.error.is_none()
        && s.location.capacity() == 0
        && s.expected.capacity() == 0
        && s.actual.capacity() == 0
        && s.triple.capacity() == 0
        && s.why.capacity() == 0
        && s.errors.capacity() == 0
}
fn reprs() -> [EnumTagRepr; 10] {
    [
        EnumTagRepr::U8,
        EnumTagRepr::I8,
        EnumTagRepr::U16,
        EnumTagRepr::I16,
        EnumTagRepr::U32,
        EnumTagRepr::I32,
        EnumTagRepr::U64,
        EnumTagRepr::I64,
        EnumTagRepr::U128,
        EnumTagRepr::I128,
    ]
}
