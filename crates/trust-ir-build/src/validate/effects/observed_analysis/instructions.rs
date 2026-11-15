// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Analysis<'_, '_> {
    pub(super) fn instruction<O: ExecutionObserver>(
        &mut self,
        inst: &Inst,
        block: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        // Two exhaustive current67-tag matches: mnemonic and effect class.
        work.admit(
            134,
            size_of::<&Inst>()
                + size_of::<&str>()
                + size_of::<Arguments<'_>>()
                + size_of::<Call>()
                + 2 * size_of::<Piece<'_>>(),
        )?;
        let mnemonic = instruction_kind(inst);
        let what = What::Instruction(mnemonic);
        let call = Call {
            mnemonic,
            kind: CallKind::Plain,
        };
        match inst {
            Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Alloca { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::MakeAggregate { .. }
            | Inst::MakeClosure { .. }
            | Inst::ArraySplat { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            | Inst::Assert { site: None, .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::LandingPad { .. }
            | Inst::Fence { .. } => Ok(()),
            Inst::Load { ptr, .. } | Inst::AtomicLoad { ptr, .. } => {
                self.access(Side::Read, *ptr, block, what, work)
            }
            Inst::Store { ptr, .. } | Inst::AtomicStore { ptr, .. } => {
                self.access(Side::Write, *ptr, block, what, work)
            }
            Inst::AtomicRMW { ptr, .. } | Inst::CmpXchg { ptr, .. } => {
                self.access(Side::Read, *ptr, block, what, work)?;
                self.access(Side::Write, *ptr, block, what, work)
            }
            Inst::CoroSuspend { frame, .. } => self.access(Side::Write, *frame, block, what, work),
            Inst::MemCopy { dst, src, .. } => {
                self.access(Side::Read, *src, block, what, work)?;
                self.access(Side::Write, *dst, block, what, work)
            }
            Inst::MemSet { dst, .. } => self.access(Side::Write, *dst, block, what, work),
            Inst::HeapAlloc { .. } => {
                self.flag(Flag::Allocates, block, &[Piece::Text("heapalloc")], work)
            }
            Inst::Dealloc { .. } => self.flag(Flag::Frees, block, &[Piece::Text("dealloc")], work),
            Inst::Retain { ptr } => {
                self.access(Side::Read, *ptr, block, what, work)?;
                self.access(Side::Write, *ptr, block, what, work)
            }
            Inst::Release { ptr } => {
                self.access(Side::Read, *ptr, block, what, work)?;
                self.access(Side::Write, *ptr, block, what, work)?;
                self.flag(Flag::Frees, block, &[Piece::Text("release")], work)
            }
            Inst::IsUnique { ptr } => self.access(Side::Read, *ptr, block, what, work),
            Inst::Drop { .. } => self.top(
                block,
                &[Piece::Text(
                    "drop (a destructor frees and can run arbitrary user code)",
                )],
                work,
            ),
            Inst::DropInvoke { .. } => self.top(
                block,
                &[Piece::Text(
                    "drop_invoke (a destructor frees and can run arbitrary user code)",
                )],
                work,
            ),
            Inst::CallIndirect { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::InvokeIndirect { .. } => self.top(
                block,
                &[
                    Piece::Text(mnemonic),
                    Piece::Text(" (an indirect callee's effects are unknowable)"),
                ],
                work,
            ),
            Inst::DialectOp(_) => self.top(
                block,
                &[Piece::Text(
                    "an opaque dialect op (its memory effects are unknown)",
                )],
                work,
            ),
            Inst::Resume { .. } => {
                self.flag(Flag::MayUnwind, block, &[Piece::Text("resume")], work)
            }
            Inst::Call { callee, args } | Inst::CallCannotUnwind { callee, args } => {
                self.call(*callee, Arguments::Values(args), block, call, work)
            }
            Inst::Invoke { callee, args, .. } => {
                self.flag(Flag::MayUnwind, block, &[Piece::Text("invoke")], work)?;
                self.call(*callee, Arguments::Values(args), block, call, work)
            }
            Inst::Assert {
                kind,
                site: Some(site),
                ..
            } => self.panic_call(kind, site, block, mnemonic, work),
            Inst::AssertInvoke { kind, site, .. } => {
                self.flag(
                    Flag::MayUnwind,
                    block,
                    &[Piece::Text("assert_invoke")],
                    work,
                )?;
                self.panic_call(kind, site, block, mnemonic, work)
            }
            Inst::SeqMap { fwd, .. } => self.call(*fwd, Arguments::ElementSlot, block, call, work),
        }
    }
}
