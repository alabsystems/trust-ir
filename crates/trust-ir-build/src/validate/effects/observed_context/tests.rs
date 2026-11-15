// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: retained ordinary context spelling/argument order is oracle.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use trust_ir::inst::AssertOverflowOp;
use trust_ir::interpret::{InstructionSite, InterpretOptions};
use trust_ir::value::{BlockId, FuncId, GlobalId};
use trust_ir::{Global, Linkage, Ty, Visibility};
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
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.stop == Some(self.events.len()) {
            return Err("original context stop");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(251))
}
fn v(index: u32) -> ValueId {
    ValueId::new(index)
}
fn g(index: u32) -> GlobalId {
    GlobalId::new(index)
}
fn text(pieces: &[Piece<'_>]) -> String {
    let mut output = String::new();
    for piece in pieces {
        match piece {
            Piece::Text(text) => output.push_str(text),
            Piece::U32(n) => output.push_str(&n.to_string()),
        }
    }
    output
}
fn key(arg: Option<Arg>) -> Option<(u8, u32)> {
    arg.map(|arg| match arg {
        Arg::Value(v) => (0, v.index()),
        Arg::Global(g) => (1, g.index()),
        Arg::Untraceable => (2, 0),
    })
}
fn global(name: &str) -> Global {
    Global {
        name: name.into(),
        ty: Ty::U8,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}
fn fixture() -> Module {
    let mut module = Module::new("context");
    module.globals = vec![global("zero"), global("one")];
    module
}
fn kinds() -> Vec<AssertKind> {
    let mut kinds = vec![
        AssertKind::Unspecified,
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::BoundsCheck {
            index: v(7),
            len: v(9),
        },
        AssertKind::MisalignedPtr {
            required: v(13),
            found: v(17),
        },
        AssertKind::NullPtr,
    ];
    kinds.extend(AssertOverflowOp::ALL.into_iter().map(AssertKind::Overflow));
    kinds
}
fn ordinary_args(kind: &AssertKind, location: PanicLocation) -> Vec<Arg> {
    let mut args: Vec<Arg> = kind
        .operands()
        .map_or_else(Vec::new, |values| values.map(Arg::Value).to_vec());
    args.push(match location {
        PanicLocation::Global(global) => Arg::Global(global),
        PanicLocation::Value(value) => Arg::Value(value),
    });
    args
}
#[derive(Clone, Copy)]
enum Query<'a> {
    Call(Call),
    What(What),
    Label(EffectPlace, &'a Module),
    Panic(AssertKind, PanicLocation),
    Get(Arguments<'a>, usize),
}
impl Query<'_> {
    fn run<O: ExecutionObserver>(
        self,
        original: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<()> {
        match self {
            Self::Call(call) => call.parts_observed(original, site).map(|_| ()),
            Self::What(what) => what.parts_observed(original, site).map(|_| ()),
            Self::Label(place, module) => {
                root_label_observed(place, module, original, site).map(|_| ())
            }
            Self::Panic(kind, location) => {
                Arguments::panic_observed(&kind, location, original, site).map(|_| ())
            }
            Self::Get(args, index) => args.get_observed(index, original, site).map(|_| ()),
        }
    }
}
fn trace(query: Query<'_>) -> Observer {
    let mut o = Observer::default();
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut o);
    query.run(&mut original, site()).unwrap();
    assert!(original.first_refusal().is_none());
    assert_eq!(original.remaining_fuel(), InterpretOptions::default().fuel);
    drop(original);
    assert!(o.events.iter().all(|event| event.site == site()));
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    o
}
fn samples<'a>(module: &'a Module, values: &'a [ValueId]) -> [Query<'a>; 16] {
    [
        Query::Call(Call {
            mnemonic: "call",
            kind: CallKind::Plain,
        }),
        Query::Call(Call {
            mnemonic: "assert",
            kind: CallKind::Panic,
        }),
        Query::What(What::Instruction("load")),
        Query::What(What::Parameter {
            call: Call {
                mnemonic: "assert_invoke",
                kind: CallKind::Panic,
            },
            side: Side::Write,
            index: u32::MAX,
        }),
        Query::Label(EffectPlace::ParamPointee { index: u32::MAX }, module),
        Query::Label(EffectPlace::Global(g(1)), module),
        Query::Label(EffectPlace::Global(g(u32::MAX)), module),
        Query::Panic(
            AssertKind::BoundsCheck {
                index: v(7),
                len: v(9),
            },
            PanicLocation::Global(g(13)),
        ),
        Query::Panic(AssertKind::NullPtr, PanicLocation::Value(v(17))),
        Query::Get(Arguments::Values(values), 0),
        Query::Get(Arguments::Values(&[]), usize::MAX),
        Query::Get(Arguments::ElementSlot, 0),
        Query::Get(
            Arguments::Panic {
                operands: Some([v(7), v(9)]),
                location: PanicLocation::Global(g(13)),
            },
            2,
        ),
        Query::Get(
            Arguments::Panic {
                operands: None,
                location: PanicLocation::Value(v(17)),
            },
            usize::MAX,
        ),
        Query::Get(
            Arguments::Panic {
                operands: Some([v(7), v(9)]),
                location: PanicLocation::Global(g(13)),
            },
            1,
        ),
        Query::Get(
            Arguments::Panic {
                operands: None,
                location: PanicLocation::Value(v(17)),
            },
            0,
        ),
    ]
}
