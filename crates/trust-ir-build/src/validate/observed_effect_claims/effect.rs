// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
fn is_relaxed(ordering: Ordering) -> bool {
    matches!(ordering, Ordering::Relaxed)
}
impl State<'_, '_> {
    pub(super) fn effect<O: ExecutionObserver>(
        &self,
        inst: &Inst,
        work: &mut Work<'_, '_, O>,
    ) -> R<Effect> {
        work.admit(67, size_of::<Effect>())?;
        let effect = match inst {
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
            // v50: a fresh array value from one register value — no memory.
            | Inst::ArraySplat { .. }
            // The tensor region: a fresh tensor value — no memory, no call.
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
            // A failed check is a TERMINAL panic outcome, whether or not it is
            // sited (amendment P): a site's entry never returns, so like an
            // unsited assert's trap it adds no memory effect the function's
            // continuation can observe. `AssertInvoke` is the same check with an
            // unwind edge the panic=abort projection never takes.
            | Inst::Assert { .. }
            | Inst::AssertInvoke { .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            // Borrows are address identities (the interpreter passes the address
            // through); binding frames are typed slots of the executing frame;
            // a landing pad reads the unwinder's registers and `Resume` hands the
            // exception object back to the unwinder.
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. } => Effect::None,
            Inst::Load { ptr, .. } => Effect::Read { address: *ptr },
            Inst::AtomicLoad { ptr, ordering, .. } => {
                if is_relaxed(*ordering) {
                    Effect::Read { address: *ptr }
                } else {
                    Effect::Refused {
                        reason: "an atomic load stronger than relaxed synchronizes",
                    }
                }
            }
            Inst::Store { ptr, .. } => Effect::Write { address: *ptr },
            Inst::AtomicStore { ptr, ordering, .. } | Inst::AtomicRMW { ptr, ordering, .. } => {
                if is_relaxed(*ordering) {
                    Effect::Write { address: *ptr }
                } else {
                    Effect::Refused {
                        reason: "an atomic write stronger than relaxed synchronizes",
                    }
                }
            }
            Inst::CmpXchg {
                ptr,
                success,
                failure,
                ..
            } => {
                if is_relaxed(*success) && is_relaxed(*failure) {
                    Effect::Write { address: *ptr }
                } else {
                    Effect::Refused {
                        reason: "a cmpxchg stronger than relaxed synchronizes",
                    }
                }
            }
            // `CoroSuspend` is DEFINED as GEP + Store + Return into the frame.
            Inst::CoroSuspend { frame, .. } => Effect::Write { address: *frame },
            Inst::Fence { .. } => Effect::Refused {
                reason: "a fence synchronizes",
            },
            Inst::HeapAlloc { .. } => Effect::Refused {
                reason: "heap allocation",
            },
            Inst::Dealloc { .. } => Effect::Refused {
                reason: "deallocation",
            },
            // A unique exact table row makes this a call edge. Missing or
            // ambiguous glue retains the original unstated-destructor refusal.
            Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => {
                let resolution = match self.drop_index.as_ref() {
                    Some(index) => Some(index.resolve(ty, work.session, work.site)?),
                    None => None,
                };
                match resolution {
                    Some(DropResolution::Resolved(glue)) => Effect::CallEdge { callee: glue },
                    _ => Effect::Refused {
                        reason: "an unresolved drop runs an unstated destructor (no drop_glue row)",
                    },
                }
            }
            // WS3.20 bulk memory: a dynamic-count write (and read) over a byte
            // RANGE, not one addressed cell; the effect model here is per-cell.
            Inst::MemCopy { .. } | Inst::MemSet { .. } => Effect::Refused {
                reason: "a bulk byte-range write with a dynamic count is not a single-cell effect",
            },
            Inst::Retain { .. } | Inst::Release { .. } | Inst::IsUnique { .. } => Effect::Refused {
                reason: "reference counting reads and writes the object header",
            },
            Inst::CallIndirect { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::InvokeIndirect { .. } => Effect::Refused {
                reason: "an indirect callee's attributes are unknowable",
            },
            Inst::DialectOp(_) => Effect::Refused {
                reason: "an opaque dialect op's memory effects are unknown",
            },
            Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }
            | Inst::Invoke { callee, .. } => {
                Effect::CallEdge { callee: *callee }
            }
            // The element function writes through its `&mut elem` parameter;
            // this rule does not attribute that write to a local, so the edge is
            // checked like any call.
            Inst::SeqMap { fwd, .. } => Effect::CallEdge { callee: *fwd },
        };
        Ok(effect)
    }
}
