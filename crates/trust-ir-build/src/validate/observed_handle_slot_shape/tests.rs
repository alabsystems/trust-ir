// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Real tables supply full slot-shape parity; synthetic shapes
//! exercise only the private formatter/projection, never an admitted table.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::shape::FieldOffsetShape;
use trust_ir::ty::{FieldDef, StructDef, StructRepr};
use trust_ir::value::{ClosureTyId, EnumId, StructId, TyId};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
pub(super) struct Observer {
    pub(super) events: Vec<ExecutionProgress>,
    pub(super) calls: Rc<Cell<usize>>,
    pub(super) work: Rc<Cell<usize>>,
    pub(super) bytes: Rc<Cell<usize>>,
    pub(super) stop: Option<usize>,
    pub(super) cleanup_after: Option<usize>,
    pub(super) work_cap: Option<usize>,
    pub(super) byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("original slot-shape stop");
        }
        if e.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup_after.is_some_and(|n| self.events.len() > n)
        {
            return Err("cleanup");
        }
        self.work
            .set(self.work.get().checked_add(e.work).ok_or("overflow")?);
        self.bytes.set(
            self.bytes
                .get()
                .checked_add(e.copy_bytes)
                .ok_or("overflow")?,
        );
        if self.work_cap.is_some_and(|n| self.work.get() > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes.get() > n) {
            return Err("copy");
        }
        Ok(())
    }
}

pub(super) fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(1097))
}
fn handle() -> Ty {
    Ty::handle("Name", "rt::Name")
}
fn tuple() -> Ty {
    Ty::Tuple(vec![handle(), Ty::Bool])
}
fn fixture() -> Module {
    let mut m = Module::new("");
    m.structs = vec![StructDef {
        id: StructId::new(0),
        name: "S".into(),
        fields: vec![FieldDef {
            name: "H".into(),
            ty: handle(),
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    }];
    m
}
fn target(m: &mut Module, triple: &str, pointer_size: u32) {
    m.target_info = Some(trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
}
fn setup<'m, O: ExecutionObserver>(
    m: &'m Module,
    s: &mut ObservedSession<'_, O>,
) -> (
    LayoutTable<'m>,
    trust_ir::ObservedNominalTypeReachability<'m>,
) {
    (
        LayoutTable::new_observed(m, s, site()).unwrap(),
        m.nominal_type_reachability_observed(s, site()).unwrap(),
    )
}
fn dispose<O: ExecutionObserver>(
    table: LayoutTable<'_>,
    nominal: trust_ir::ObservedNominalTypeReachability<'_>,
    s: &mut ObservedSession<'_, O>,
) {
    let _ = nominal.retire_observed(s, site());
    // Fresh fixture table + observed-only queries: ordinary memo stays empty.
    // This fixed-header fixture drop is NOT a general table-retirement API.
    s.retirement_step(site(), size_of::<LayoutTable<'_>>() + 1);
    drop(table);
    s.retirement_poll(site());
}
fn dispose_reason<O: ExecutionObserver>(r: Result<u64, String>, s: &mut ObservedSession<'_, O>) {
    if let Err(text) = r {
        Work {
            session: s,
            site: site(),
        }
        .flat(text);
    }
}
fn run(
    m: &Module,
    ty: &Ty,
    count: bool,
    align: Option<u64>,
) -> (Result<u64, String>, Observer, usize, usize) {
    let old_table = LayoutTable::new(m);
    let old_nominal = m.nominal_type_reachability();
    let expected = super::super::handle_slots::slot_shape_test_oracle(
        &old_table,
        &old_nominal,
        ty,
        count,
        align,
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let (table, nominal) = setup(m, &mut s);
    let begin = calls.get();
    let out = slot_shape_observed(&table, &nominal, ty, count, align, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    dispose_reason(out, &mut s);
    dispose(table, nominal, &mut s);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<Result<u64, String>>()
        }
    );
    (expected, o, begin, end)
}
fn field() -> FieldOffsetShape {
    FieldOffsetShape {
        field: u32::MAX,
        name: "raw\0".into(),
        ty_shape: TyShape::Handle,
        offset_bits: Some(u64::MAX),
    }
}
fn kinds() -> Vec<TyLayoutKind> {
    vec![
        TyLayoutKind::Scalar(TyShape::Handle),
        TyLayoutKind::ThinPointer,
        TyLayoutKind::FatPointer(PointerMetadataShape::ContainerVtable),
        TyLayoutKind::Struct {
            id: StructId::new(u32::MAX),
            fields: vec![field()],
        },
        TyLayoutKind::Tuple {
            fields: vec![field()],
        },
        TyLayoutKind::Closure {
            id: ClosureTyId::new(u32::MAX),
            captures: vec![field()],
        },
        TyLayoutKind::Enum {
            id: EnumId::new(u32::MAX),
            variants: usize::MAX,
        },
        TyLayoutKind::Array {
            elem: TyId::new(u32::MAX),
            len: u64::MAX,
            stride_bits: u64::MAX,
        },
        TyLayoutKind::Vector {
            elem_shape: TyShape::Float { bits: u32::MAX },
            lanes: u32::MAX,
            lane_bits: u64::MAX,
        },
        TyLayoutKind::Unit,
        TyLayoutKind::Never,
    ]
}
fn ty_shapes() -> Vec<TyShape> {
    vec![
        TyShape::Int {
            signed: true,
            bits: u32::MAX,
        },
        TyShape::Int {
            signed: false,
            bits: 0,
        },
        TyShape::Float { bits: u32::MAX },
        TyShape::PointerInt { signed: true },
        TyShape::PointerInt { signed: false },
        TyShape::Error,
        TyShape::Bool,
        TyShape::ThinPointer,
        TyShape::FatPointer,
        TyShape::Unit,
        TyShape::Never,
        TyShape::Struct,
        TyShape::Array,
        TyShape::Vector,
        TyShape::Tuple,
        TyShape::Enum,
        TyShape::Function,
        TyShape::Ref,
        TyShape::RefMut,
        TyShape::PtrConst,
        TyShape::PtrMut,
        TyShape::Rc,
        TyShape::Set,
        TyShape::Sequence,
        TyShape::Record,
        TyShape::Closure,
        TyShape::Refine,
        TyShape::Dialect,
        TyShape::Handle,
        TyShape::Tensor,
    ]
}
fn empty(s: &State) -> bool {
    s.shape.is_none() && s.error.is_none() && s.render.capacity() == 0 && s.reason.capacity() == 0
}
fn drain<O: ExecutionObserver>(s: &mut State, work: &mut Work<'_, '_, O>) {
    s.retire_scratch(work);
    work.flat(take(&mut s.reason));
}
