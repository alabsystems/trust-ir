-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.MemorySafety

namespace TrustIr
namespace HeldMemoryFrames

/-- Replace exactly the two private SSA fields. Every world/choice field is
    retained, including fields that future memory models add. -/
def replaceSSA (state : MachineState) (locals : ValueMap) (nextValueId : Nat) : MachineState :=
  { state with locals := locals, nextValueId := nextValueId }

/-- Held-value computations commute with an arbitrary SSA frame replacement,
    preserving the exact returned value, error and every remaining field. -/
def Equivariant {α : Type} (computation : Sem α) : Prop :=
  ∀ state locals nextValueId,
    Sem.run computation (replaceSSA state locals nextValueId) =
      (Sem.run computation state).map
        (fun result => (result.1, replaceSSA result.2 locals nextValueId))

theorem pure_eqv {α : Type} (value : α) : Equivariant (pure value : Sem α) := by
  intro state locals nextValueId
  rfl

theorem throw_eqv {α : Type} (error : SemError) : Equivariant (throw error : Sem α) := by
  intro state locals nextValueId
  rfl

theorem bind_eqv {α β : Type} (first : Sem α) (next : α → Sem β)
    (hFirst : Equivariant first) (hNext : ∀ value, Equivariant (next value)) :
    Equivariant (first >>= next) := by
  intro state locals nextValueId
  simp only [Sem.run_bind]
  rw [hFirst state locals nextValueId]
  cases h : Sem.run first state with
  | error error => rfl
  | ok result =>
    rcases result with ⟨value, after⟩
    exact hNext value after locals nextValueId

theorem memoryExcept_eqv {α : Type} (result : Except SemError α) :
    Equivariant (Sem.fromMemoryExcept result) := by
  cases result with
  | ok value => exact pure_eqv value
  | error error => exact throw_eqv error

private def readMemory : Sem Memory := do
  let state ← Sem.getState
  pure state.memory

private theorem readMemory_eqv : Equivariant readMemory := by
  intro state locals nextValueId
  rfl

/-- State reads whose continuation consumes only memory do not observe SSA. -/
theorem readMemory_bind_eqv {α : Type} (next : Memory → Sem α)
    (hNext : ∀ memory, Equivariant (next memory)) :
    Equivariant (do let state ← Sem.getState; next state.memory) := by
  simpa only [readMemory, bind_assoc, pure_bind] using
    bind_eqv readMemory next readMemory_eqv hNext

/-- A read-only state observation may retain precisely its memory projection.
    The dependency equation is proved by reduction at each concrete core. -/
theorem readStateMemory_eqv {α : Type} (next : MachineState → Sem α)
    (hMemory : ∀ state, next state = next { MachineState.empty with memory := state.memory })
    (hNext : ∀ memory, Equivariant (next { MachineState.empty with memory := memory })) :
    Equivariant (do let state ← Sem.getState; next state) := by
  intro state locals nextValueId
  simp only [Sem.run, sr_bind, sr_get, Except.bind]
  rw [hMemory (replaceSSA state locals nextValueId), hMemory state]
  exact hNext state.memory state locals nextValueId

theorem throw_bind_eqv {α β : Type} (error : SemError) (next : α → Sem β) :
    Equivariant ((throw error : Sem α) >>= next) := by
  intro state locals nextValueId
  rfl

theorem writeMemory_eqv (memory : Memory) :
    Equivariant (Sem.modifyState (fun state => { state with memory := memory })) := by
  intro state locals nextValueId
  rfl

theorem modifyMemory_eqv (update : Memory → Memory) :
    Equivariant (Sem.modifyState (fun state => { state with memory := update state.memory })) := by
  intro state locals nextValueId
  rfl

private theorem ite_eqv {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Sem α) (hYes : Equivariant yes) (hNo : Equivariant no) :
    Equivariant (if condition then yes else no) := by
  split <;> assumption

private theorem rejectPartial_eqv (value : Value) (op : String) :
    Equivariant (Sem.rejectPartial value op) := by
  cases value <;> first | exact pure_eqv _ | exact throw_eqv _

private theorem expectPointer_eqv (value : Value) (op : String) :
    Equivariant (Sem.expectPointer op value) := by
  unfold Sem.expectPointer
  cases value
  case ptr address provenance =>
    cases provenance with
    | some id => exact pure_eqv _
    | none => exact ite_eqv _ _ _ (throw_eqv _) (throw_eqv _)
  all_goals exact throw_eqv _

private theorem targetRange_eqv (model : ByteModel) (op : String) (address size : Nat) :
    Equivariant (Sem.checkTargetRange model op address size) := by
  cases model with
  | le64 => exact pure_eqv _
  | le32 => exact ite_eqv _ _ _ (pure_eqv _) (throw_eqv _)

private theorem checkedAccess_eqv (model : ByteModel) (op : String)
    (address : Nat) (id : AllocId) (size alignment : Nat) :
    Equivariant (Sem.checkedAccess op address id size alignment model) := by
  unfold Sem.checkedAccess
  refine bind_eqv _ _ (targetRange_eqv model op address size) ?_
  intro _
  refine readStateMemory_eqv _ (fun state => rfl) ?_
  intro memory
  dsimp only
  cases memory.lookup id with
  | none => exact throw_eqv _
  | some allocation =>
    apply ite_eqv
    · exact throw_eqv _
    · apply ite_eqv
      · exact throw_eqv _
      · exact ite_eqv _ _ _ (throw_eqv _) (pure_eqv _)

theorem semGEPAddress_eqv (base : Value) (delta : Nat) (model : ByteModel) :
    Equivariant (semGEPAddress base delta model) := by
  unfold semGEPAddress
  refine bind_eqv _ _ (rejectPartial_eqv base "GEP") ?_
  intro _
  cases base <;> try exact throw_eqv _
  case ptr address provenance =>
    cases provenance with
    | none =>
      refine bind_eqv _ _ (memoryExcept_eqv _) ?_
      intro result
      split
      · exact bind_eqv _ _ (throw_eqv _) (fun _ => pure_eqv _)
      · exact bind_eqv _ _ (pure_eqv _) (fun _ => pure_eqv _)
    | some id =>
      dsimp only
      refine readStateMemory_eqv _ (fun state => rfl) ?_
      intro memory
      dsimp only
      cases memory.lookup id with
      | none => exact throw_bind_eqv _ _
      | some allocation =>
        refine bind_eqv _ _ (pure_eqv allocation) ?_
        intro allocation
        dsimp only
        split
        · exact throw_bind_eqv _ _
        · refine bind_eqv _ _ (pure_eqv _) ?_; intro _
          refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro _
          split
          · exact bind_eqv _ _ (throw_eqv _) (fun _ => pure_eqv _)
          · exact bind_eqv _ _ (pure_eqv _) (fun _ => pure_eqv _)

theorem semGEPValuesUsing_eqv {key : Type} (layoutOf : MemoryLayoutQuery)
    (readInteger : key → Value → Except SemError Int) (pointeeTy : Ty)
    (base : Value) (indices : List (key × Value)) (model : ByteModel) :
    Equivariant (semGEPValuesUsing layoutOf readInteger pointeeTy base indices model) := by
  unfold semGEPValuesUsing
  exact bind_eqv _ _ (memoryExcept_eqv _) (fun delta => semGEPAddress_eqv base delta model)

theorem semStoreValueUsing_eqv (layoutOf : MemoryLayoutQuery)
    (encode : Value → Except SemError (List UInt8)) (ty : Ty)
    (pointer value : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    Equivariant (semStoreValueUsing layoutOf encode ty pointer value strict align model) := by
  unfold semStoreValueUsing
  refine bind_eqv _ _ (rejectPartial_eqv pointer "Store") ?_; intro _
  refine bind_eqv _ _ (expectPointer_eqv pointer "Store") ?_; intro pair
  rcases pair with ⟨address, id⟩
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro layout
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro alignment
  refine bind_eqv _ _ (checkedAccess_eqv model "Store" address id layout.size alignment) ?_
  intro address
  refine readStateMemory_eqv _ (fun state => rfl) ?_
  intro memory
  dsimp only
  split
  · cases value <;> dsimp only <;> try exact throw_eqv _
    case «partial» bytes =>
      apply ite_eqv
      · exact throw_eqv _
      · exact ite_eqv _ _ _ (throw_eqv _) (by intro state locals nextValueId; rfl)
    case undef lane =>
      exact ite_eqv _ _ _ (throw_eqv _) (by intro state locals nextValueId; rfl)
  · split
    · exact throw_bind_eqv _ _
    · refine bind_eqv _ _ (pure_eqv _) ?_; intro _
      cases encode value with
      | error error => exact throw_bind_eqv error _
      | ok bytes =>
        refine bind_eqv _ _ (pure_eqv bytes) ?_; intro encoded
        split
        · exact throw_bind_eqv _ _
        · exact bind_eqv _ _ (pure_eqv _) (fun _ => writeMemory_eqv _)

end HeldMemoryFrames
end TrustIr
