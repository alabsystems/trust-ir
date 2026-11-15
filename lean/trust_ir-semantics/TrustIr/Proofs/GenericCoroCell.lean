-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshStep

namespace TrustIr.GenericCoro

/-- The exact held-cell allocation/init prefix: the pure image writer may
    update any memory field, while allocation permissions remain actual. -/
def allocateCell (model : ByteModel) (size align : Nat) (write : Memory → Addr → Memory) : Sem Value := do
  let old ← Sem.getState
  Sem.checkTargetAllocation model old.memory size align 0
  let (address, memory) := old.memory.alloc size align 0 .rustStack
  let allocation := AllocId.mk old.memory.nextAllocId
  Sem.setState { old with
    memory := write memory address,
    permissions := old.permissions.set allocation .owned }
  pure (.ptr address (some allocation))

/-- The held cell publishes no private SSA alias, for arbitrary writers,
    target/address failures, permissions and complete initial worlds. -/
theorem allocateCell_equivariant (model : ByteModel) (size align : Nat)
    (write : Memory → Addr → Memory) : HeldMemoryFrames.Equivariant (allocateCell model size align write) := by
  intro state locals nextValueId
  unfold allocateCell
  simp only [Sem.run, sr_bind, sr_get, Except.bind]
  unfold Sem.checkTargetAllocation Sem.fromMemoryExcept
  dsimp only [HeldMemoryFrames.replaceSSA]
  cases checked : checkWordAllocation model state.memory size align 0 <;> rfl

theorem allocateCell_fresh (model : ByteModel) (size align : Nat)
    (write : Memory → Addr → Memory) : SSAFreshStep.KeepsFresh (allocateCell model size align write) :=
  SSAFreshStep.equivariant_fresh _ (allocateCell_equivariant model size align write)

end TrustIr.GenericCoro
