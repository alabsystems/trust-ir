-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.HeldMemoryFrames
import TrustIr.Semantics.AggregateAccess
import TrustIr.Semantics.OriginalClosureMemory

namespace TrustIr.HeldMemoryFrames

private theorem conditional_eqv {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Sem α) (hYes : Equivariant yes) (hNo : Equivariant no) :
    Equivariant (if condition then yes else no) := by
  split <;> assumption

private theorem reject_eqv (value : Value) (op : String) :
    Equivariant (Sem.rejectPartial value op) := by
  cases value <;> first | exact pure_eqv _ | exact throw_eqv _

private theorem pointer_eqv (value : Value) (op : String) :
    Equivariant (Sem.expectPointer op value) := by
  unfold Sem.expectPointer
  cases value
  case ptr address provenance =>
    cases provenance with
    | some id => exact pure_eqv _
    | none => exact conditional_eqv _ _ _ (throw_eqv _) (throw_eqv _)
  all_goals exact throw_eqv _

private theorem range_eqv (model : ByteModel) (op : String) (address size : Nat) :
    Equivariant (Sem.checkTargetRange model op address size) := by
  cases model with
  | le64 => exact pure_eqv _
  | le32 => exact conditional_eqv _ _ _ (pure_eqv _) (throw_eqv _)

private theorem access_eqv (model : ByteModel) (op : String)
    (address : Nat) (id : AllocId) (size alignment : Nat) :
    Equivariant (Sem.checkedAccess op address id size alignment model) := by
  unfold Sem.checkedAccess
  refine bind_eqv _ _ (range_eqv model op address size) ?_; intro _
  refine readStateMemory_eqv _ (fun state => rfl) ?_; intro memory
  dsimp only
  cases memory.lookup id with
  | none => exact throw_eqv _
  | some allocation =>
    apply conditional_eqv
    · exact throw_eqv _
    · apply conditional_eqv
      · exact throw_eqv _
      · exact conditional_eqv _ _ _ (throw_eqv _) (pure_eqv _)

private theorem align_eqv (ty : Ty) (align : Option Nat) (model : ByteModel) :
    Equivariant (Sem.accessAlign "Load" ty align model) := by
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign
  exact conditional_eqv _ _ _ (pure_eqv _) (throw_eqv _)

/-- A canonical held load observes only memory, for every decoder, refusal,
    target model and input state. It never publishes a private SSA value. -/
theorem semLoadValueUsing_eqv (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    Equivariant (semLoadValueUsing decode ty pointer strict align model) := by
  unfold semLoadValueUsing
  refine bind_eqv _ _ (reject_eqv pointer "Load") ?_; intro _
  refine bind_eqv _ _ (pointer_eqv pointer "Load") ?_; intro pair
  rcases pair with ⟨address, allocation⟩
  dsimp only
  cases ty.byteSizeFor model with
  | none => exact throw_bind_eqv _ _
  | some size =>
    refine bind_eqv _ _ (pure_eqv size) ?_
    intro size
    refine bind_eqv _ _ (align_eqv ty align model) ?_; intro alignment
    refine bind_eqv _ _ (access_eqv model "Load" address allocation size alignment) ?_
    intro address
    refine readStateMemory_eqv _ (fun state => rfl) ?_; intro memory
    dsimp only
    cases memory.readBytes address size with
    | some bytes =>
      dsimp only
      cases decode memory bytes with
      | error error => exact throw_eqv _
      | ok value => exact pure_eqv _
    | none => exact conditional_eqv _ _ _ (pure_eqv _) (throw_eqv _)

/-- Descriptor-based held loads preserve the complete world under arbitrary
    SSA-frame replacement. No validity premise is imposed on the service. -/
theorem aggregateLoadValue_eqv (service : AggregateMemory.Service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    Equivariant (AggregateMemory.loadValue service order ty pointer strict align model) := by
  unfold AggregateMemory.loadValue
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro plan
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro alignment
  refine bind_eqv _ _ (reject_eqv pointer "Load") ?_; intro _
  refine bind_eqv _ _ (pointer_eqv pointer "Load") ?_; intro pair
  rcases pair with ⟨address, allocation⟩
  refine bind_eqv _ _ (access_eqv model "Load" address allocation plan.layout.size alignment) ?_
  intro address
  refine readStateMemory_eqv _ (fun state => rfl) ?_; intro memory
  dsimp only
  split
  · exact memoryExcept_eqv _
  · split
    · exact pure_eqv _
    · refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro missing
      cases missing with
      | none => exact memoryExcept_eqv _
      | some offset =>
        cases plan <;> try exact throw_eqv _
        refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro missing
        cases missing with
        | none => exact memoryExcept_eqv _
        | some offset => exact throw_eqv _

/-- An aggregate store is transactional and changes only memory, including
    its unwritten-lane records; malformed services retain their exact error. -/
theorem aggregateStoreValue_eqv (service : AggregateMemory.Service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer value : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    Equivariant (AggregateMemory.storeValue service order ty pointer value strict align model) := by
  unfold AggregateMemory.storeValue
  repeat' (first
    | with_reducible exact memoryExcept_eqv _
    | with_reducible exact reject_eqv _ _
    | with_reducible exact pointer_eqv _ _
    | with_reducible exact access_eqv _ _ _ _ _ _
    | with_reducible exact pure_eqv _
    | exact throw_eqv _
    | exact throw_bind_eqv _ _
    | exact modifyMemory_eqv _
    | exact (by intro state locals nextValueId; rfl)
    | with_reducible refine bind_eqv _ _ ?_ (fun _ => ?_)
    | dsimp only
    | split)

/-- The source-bound closure load observes only memory. Original source/target
refusals and uninitialized-byte failures remain exact under SSA replacement. -/
theorem originalClosureLoadValue_eqv (service : OriginalClosureMemory.Service)
    (order : FunctionAddressOrder) (closure : ClosureTyId) (pointer : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    Equivariant (OriginalClosureMemory.loadValue service order closure pointer strict align model) := by
  unfold OriginalClosureMemory.loadValue
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro binding
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro layout
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro fields
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro alignment
  refine bind_eqv _ _ (reject_eqv pointer "Load") ?_; intro _
  refine bind_eqv _ _ (pointer_eqv pointer "Load") ?_; intro pair
  rcases pair with ⟨address, allocation⟩
  refine bind_eqv _ _ (access_eqv model "Load" address allocation layout.size alignment) ?_; intro address
  refine readStateMemory_eqv _ (fun state => rfl) ?_; intro memory
  dsimp only
  refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro missing
  split
  · exact throw_bind_eqv _ _
  · refine bind_eqv _ _ (pure_eqv _) ?_; intro _
    refine bind_eqv _ _ (memoryExcept_eqv _) ?_; intro captures
    exact pure_eqv _

/-- A checked original closure store changes only canonical memory and its
unwritten records; it cannot inspect or replace the caller's SSA frame. -/
theorem originalClosureStoreValue_eqv (service : OriginalClosureMemory.Service)
    (order : FunctionAddressOrder) (closure : ClosureTyId) (pointer value : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    Equivariant (OriginalClosureMemory.storeValue service order closure pointer value strict align model) := by
  unfold OriginalClosureMemory.storeValue
  repeat' (first
    | with_reducible exact memoryExcept_eqv _
    | with_reducible exact reject_eqv _ _
    | with_reducible exact pointer_eqv _ _
    | with_reducible exact access_eqv _ _ _ _ _ _
    | with_reducible exact pure_eqv _
    | exact throw_eqv _
    | exact throw_bind_eqv _ _
    | exact modifyMemory_eqv _
    | exact (by intro state locals nextValueId; rfl)
    | with_reducible refine bind_eqv _ _ ?_ (fun _ => ?_)
    | dsimp only
    | split)

end TrustIr.HeldMemoryFrames
