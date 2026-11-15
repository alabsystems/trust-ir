// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN against the actual complete RC namespace/effect rule.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::FuncTyId;
use trust_ir::{ArgExt, Block, InstrNode, ParamAttrs, PassMode};
mod constants;
mod custody;
mod functions;
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
            return Err("original RC stop");
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
    ExecutionSite::Entry(FuncId::new(1091))
}
fn fixture() -> Module {
    let mut m = Module::new("");
    for (i, e) in TRUSTED_RC_RUNTIMES[0].entry_points.iter().enumerate() {
        m.func_types.push(e.func_ty());
        m.functions.push(Function::new(
            FuncId::new(i as u32),
            e.symbol,
            FuncTyId::new(i as u32),
            BlockId::new(0),
        ));
    }
    m
}
fn bad_fixture() -> Module {
    let mut m = fixture();
    m.func_types[0] = FuncTy::unrecorded(vec![Ty::Ptr], vec![Ty::Ptr], true);
    let f = &mut m.functions[0];
    f.calling_conv = CallingConv::Fast;
    f.attrs.naked = true;
    f.attrs.readnone = true;
    f.attrs.readonly = true;
    f.attrs.params = vec![ParamAttrs {
        nonnull: true,
        ..ParamAttrs::default()
    }];
    f.proofs = vec![ProofAnnotation::Pure];
    f.display_path = Some("raw'\"\n\0".into());
    f.linkage = Linkage::Internal;
    f.blocks.push(Block::new(BlockId::new(u32::MAX)));
    m
}
pub(super) fn global(name: &str, initializer: Option<Constant>) -> trust_ir::Global {
    trust_ir::Global {
        name: name.into(),
        ty: Ty::Ptr,
        mutable: false,
        initializer,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    }
}
pub(super) fn address(symbol: &str) -> Constant {
    Constant::SymbolAddr {
        symbol: symbol.into(),
        addend: i64::MIN,
    }
}
fn run(m: &Module) -> (Vec<ValidationError>, Observer, usize) {
    let expected = super::super::validate_rc_entry_points(m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_rc_entry_points_observed(m, &mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(out, expected);
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    assert_eq!(
        o.events[end - 1],
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<Vec<ValidationError>>(),
        }
    );
    (expected, o, end)
}
fn empty(s: &State<'_>) -> bool {
    s.expected_text.capacity() == 0
        && s.actual.capacity() == 0
        && s.piece.capacity() == 0
        && s.render.capacity() == 0
        && s.symbol.capacity() == 0
        && s.other.capacity() == 0
        && s.location.capacity() == 0
        && s.stack.capacity() == 0
        && s.errors.capacity() == 0
}
fn drain<O: ExecutionObserver>(s: &mut State<'_>, work: &mut Work<'_, '_, O>) {
    s.retire_scratch(work);
    let _ = retire_validation_errors_observed(take(&mut s.errors), work.session, work.site);
}
pub(super) fn abi() -> trust_ir::signature_abi::SignatureAbi {
    use trust_ir::signature_abi::*;
    SignatureAbi {
        target: AbiTarget {
            triple: "x".into(),
            data_layout: "e-p:64:64".into(),
            abi: "c".into(),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "raw".into(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "producer".into(),
            revision: "revision".into(),
        },
        convention: "c".into(),
        lowered_convention: CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    }
}
