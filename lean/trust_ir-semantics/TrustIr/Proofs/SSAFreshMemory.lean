-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshStep
import TrustIr.Proofs.SSAFreshInstructions
import TrustIr.Proofs.AggregateMemoryFrames

namespace TrustIr.SSAFreshMemory
open SSAFreshFrames SSAFreshStep SSAFreshInstructions

theorem fromMemoryExcept_fresh {α : Type} (result : Except SemError α) :
    KeepsFresh (Sem.fromMemoryExcept result) :=
  equivariant_fresh _ (HeldMemoryFrames.memoryExcept_eqv result)

/-- The snapshot is the actual initial state, so its derived invariant is
    available to continuations that replace only non-SSA state fields. -/
theorem getState_bind_fresh {α : Type} (next : MachineState → Sem α)
    (nextFresh : ∀ state, FreshState state → KeepsFresh (next state)) :
    KeepsFresh (do let state ← Sem.getState; next state) := by
  intro state result fresh run
  simp only [Sem.run, sr_bind, sr_get, Except.bind] at run
  exact nextFresh state fresh state result fresh run

theorem setState_fresh (replacement : MachineState) (fresh : FreshState replacement) :
    KeepsFresh (Sem.setState replacement) := by
  intro state result oldFresh run
  change Except.ok ((), replacement) = Except.ok result at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact fresh

theorem semStoreUsing_fresh (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (pointer value : ValueId) (strict : Bool) (align : Option Nat)
    (model : ByteModel) (layout : MemoryLayoutQuery) :
    KeepsFresh (semStoreUsing encode ty pointer value strict align model layout) := by
  unfold semStoreUsing
  exact bind_fresh _ _ (lookup_fresh pointer) (fun heldPointer =>
    bind_fresh _ _ (lookup_fresh value) (fun heldValue =>
      equivariant_fresh _ (HeldMemoryFrames.semStoreValueUsing_eqv layout encode ty
        heldPointer heldValue strict align model)))

theorem semGEPUsing_fresh (layout : MemoryLayoutQuery) (read : IntegerOperandReader)
    (ty : Ty) (base : ValueId) (indices : List ValueId) (model : ByteModel) :
    KeepsFresh (semGEPUsing layout read ty base indices model) := by
  unfold semGEPUsing
  refine bind_fresh _ _ (lookup_fresh base) (fun heldBase => ?_)
  refine bind_fresh _ _ (mapM_fresh _ indices ?_) (fun inputs => ?_)
  · intro id
    exact bind_fresh _ _ (lookup_fresh id) (fun _ => pure_fresh _)
  · exact bind_fresh _ _
      (equivariant_fresh _ (HeldMemoryFrames.semGEPValuesUsing_eqv layout read ty heldBase inputs model))
      bindFresh_fresh

theorem semAllocateUsing_fresh (layout : MemoryLayoutQuery) (read : IntegerOperandReader)
    (ty : Ty) (count : Option ValueId) (align : Option Nat) (origin : AllocationOrigin)
    (refCounted : Bool) (slack : Nat) (model : ByteModel) :
    KeepsFresh (semAllocateUsing layout read ty count align origin refCounted slack model) := by
  cases count with
  | none =>
    unfold semAllocateUsing
    try simp only [pure_bind]
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun layout => ?_)
    try simp only [pure_bind]
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun size => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun alignment => ?_)
    refine getState_bind_fresh _ (fun before fresh => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun unit => ?_)
    dsimp only
    split <;> exact bind_fresh _ _
      (setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl))
      (fun _ => bindFresh_fresh _)
  | some id =>
    unfold semAllocateUsing
    refine bind_fresh _ _ (lookup_fresh id) (fun value => ?_)
    try simp only [pure_bind]
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun layout => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun integer => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun elements => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun size => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun alignment => ?_)
    refine getState_bind_fresh _ (fun before fresh => ?_)
    refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun unit => ?_)
    dsimp only
    split <;> exact bind_fresh _ _
      (setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl))
      (fun _ => bindFresh_fresh _)

local macro "read_leaves" : tactic =>
  `(tactic| repeat (first
    | exact pure_fresh _
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact fromMemoryExcept_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem expectPointer_fresh (op : String) (value : Value) :
    KeepsFresh (Sem.expectPointer op value) := by
  unfold Sem.expectPointer
  read_leaves

theorem targetAddress_fresh (model : ByteModel) (op : String) (address : Nat) :
    KeepsFresh (Sem.targetAddress model op address) := by
  unfold Sem.targetAddress
  read_leaves

theorem checkTargetRange_fresh (model : ByteModel) (op : String) (address size : Nat) :
    KeepsFresh (Sem.checkTargetRange model op address size) := by
  unfold Sem.checkTargetRange
  read_leaves

theorem declaredOrNaturalAlign_fresh (op : String) (ty : Ty) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (Sem.declaredOrNaturalAlign op ty align model) := by
  unfold Sem.declaredOrNaturalAlign
  dsimp only
  read_leaves

theorem accessAlign_fresh (op : String) (ty : Ty) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (Sem.accessAlign op ty align model) := declaredOrNaturalAlign_fresh op ty align model

theorem checkedAccess_fresh (op : String) (address : Addr) (allocation : AllocId)
    (size align : Nat) (model : ByteModel) :
    KeepsFresh (Sem.checkedAccess op address allocation size align model) := by
  unfold Sem.checkedAccess
  refine bind_fresh _ _ (checkTargetRange_fresh model op address size) (fun _ => ?_)
  read_leaves

local macro "load_leaves" : tactic =>
  `(tactic| repeat (first
    | exact expectPointer_fresh _ _
    | exact targetAddress_fresh _ _ _
    | exact checkTargetRange_fresh _ _ _ _
    | exact accessAlign_fresh _ _ _ _
    | exact checkedAccess_fresh _ _ _ _ _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact fromMemoryExcept_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semLoadUsing_fresh (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (pointer : ValueId) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (semLoadUsing decode ty pointer strict align model) := by
  unfold semLoadUsing
  exact bind_fresh _ _ (lookup_fresh pointer) (fun held =>
    bind_fresh _ _ (equivariant_fresh _
      (HeldMemoryFrames.semLoadValueUsing_eqv decode ty held strict align model)) bindFresh_fresh)

theorem semAllocaUsing_fresh (layout : MemoryLayoutQuery) (read : IntegerOperandReader)
    (ty : Ty) (count : Option ValueId) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (semAllocaUsing layout read ty count align model) :=
  semAllocateUsing_fresh layout read ty count align .rustStack false 0 model

theorem semHeapAllocUsing_fresh (layout : MemoryLayoutQuery) (read : IntegerOperandReader)
    (ty : Ty) (count : Option ValueId) (origin : AllocOrigin) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (semHeapAllocUsing layout read ty count origin align model) :=
  semAllocateUsing_fresh layout read ty count align origin.toAllocationOrigin
    origin.isRefCounted heapUsableSlack model

end TrustIr.SSAFreshMemory
