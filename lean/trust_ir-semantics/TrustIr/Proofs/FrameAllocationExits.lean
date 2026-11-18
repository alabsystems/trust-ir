-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAtomicExits
import TrustIr.Proofs.FrameAggregateChecks

namespace TrustIr.FrameLifetime

private theorem check_action {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,True.intro,.refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

/-- Observe the actual current state, retaining its identity for a later
snapshot-based update rather than weakening the observation to a Nat post. -/
private theorem get_bind_exit {α : Type} (post : Nat → α → Prop)
    (next : MachineState → Sem α) (state : MachineState)
    (tail : FrameActionExit post state (Sem.run (next state) state)) :
    FrameActionExit post state (Sem.run (do let observed ← Sem.getState; next observed) state) := tail

local macro "static_errors" : tactic => `(tactic|
  repeat' first
    | (solve | intro exception after same; cases same)
    | (simp only [Except.bind,pure_bind])
    | split
    | (dsimp only; split))

theorem word_operand_no_unwind (operation : String) (positive : Bool) (value : Int) :
    ExceptNoUnwind (checkedWord64Operand operation positive value) := by
  unfold checkedWord64Operand
  static_errors

theorem word_mul_no_unwind (operation : String) (left right : Nat) :
    ExceptNoUnwind (checkedWord64Mul operation left right) := by
  unfold checkedWord64Mul
  static_errors

theorem word_add_no_unwind (operation : String) (left right : Nat) :
    ExceptNoUnwind (checkedWord64Add operation left right) := by
  unfold checkedWord64Add
  static_errors

theorem memory_alignment_no_unwind (operation : String) (natural : Nat) (align : Option Nat) :
    ExceptNoUnwind (checkedMemoryAlign operation natural align) := by
  unfold checkedMemoryAlign
  static_errors

theorem word_allocation_no_unwind (model : ByteModel) (memory : Memory) (size alignment slack : Nat) :
    ExceptNoUnwind (checkWordAllocation model memory size alignment slack) := by
  unfold checkWordAllocation
  static_errors

theorem carrier_integer_no_unwind (ctx : EvalContext) (id : ValueId) (value : Value) :
    ExceptNoUnwind (ctx.carrierIntegerOperand id value) := by
  unfold EvalContext.carrierIntegerOperand
  repeat' first
    | (solve | intro exception after same; cases same)
    | (solve | exact typed_integer_no_unwind _ _ _)
    | (simp only [Except.bind,pure_bind])
    | (unfold typedIntegerCarrierValue)
    | split
    | (dsimp only; split)

/-- Actual contextual layout queries, including mismatch, absent layout,
negative cache entries and later uncached requests, cannot forge unwind states. -/
theorem context_memory_layout_no_unwind (ctx : EvalContext) (safe : MemoryContextErrors ctx) (ty : Ty) :
    ExceptNoUnwind (ctx.memoryLayout ty) := by
  unfold EvalContext.memoryLayout
  cases selected : ctx.memoryServiceFor ty with
  | none => simp only [selected]; unfold scalarMemoryLayout; static_errors
  | some service =>
    simp only [selected]
    unfold AggregateMemory.layoutQuery
    split
    · have held := (safe ty service selected ty).2
      exact DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 held)
    · static_errors

/-- Only the new nominal allocation branch uses shape storage. Its pure
source query has a proved static error domain; all older layout questions
retain their original contextual error-policy premise. -/
theorem context_allocation_layout_no_unwind (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (ty : Ty) :
    ExceptNoUnwind (ctx.allocationLayout ty) := by
  cases ty
  case Closure id =>
    simp only [EvalContext.allocationLayout]
    cases selected : ctx.memoryServiceFor (.Closure id) with
    | none =>
      simp only [selected]
      exact context_memory_layout_no_unwind ctx safe _
    | some service =>
      simp only [selected]
      unfold AggregateMemory.allocationLayoutQuery
      split
      · have held := service.allocation_error_policy BlockDecodeError
          (fun _ => True.intro) (fun _ => True.intro) (.Closure id)
        exact DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 held)
      · static_errors
  all_goals
    simp only [EvalContext.allocationLayout]
    exact context_memory_layout_no_unwind ctx safe _

private theorem allocate_world_action (size alignment slack : Nat) (origin : AllocationOrigin)
    (refCounted : Bool) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (do
      let before ← Sem.getState
      Sem.fromMemoryExcept (checkWordAllocation model before.memory size alignment slack)
      let id := AllocId.mk before.memory.nextAllocId
      let (address,memory) := before.memory.alloc size alignment slack origin
      if refCounted then
        Sem.setState {before with
          memory,permissions := before.permissions.set id .arcRef,
          refCounts := fun key => if key == id then some 1 else before.refCounts key}
      else Sem.setState {before with memory,permissions := before.permissions.set id .owned}
      Sem.bindFresh (.ptr address (some id))) := by
  intro state valid
  apply get_bind_exit
  cases checked : checkWordAllocation model state.memory size alignment slack with
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (word_allocation_no_unwind _ _ _ _ _ _ _ checked)
  | ok unit =>
    cases unit
    simp only [Sem.fromMemoryExcept,pure_bind]
    cases allocated : state.memory.alloc size alignment slack origin with
    | mk address memory =>
      cases refCounted <;> simp only [Bool.false_eq_true,↓reduceIte]
      all_goals
        refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state ?_ ?_
        · exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩
        · intro unit state valid _
          cases unit
          exact fresh_minted_frame_exit _ state valid ((mintedValue_iff_shape _ _).2 True.intro)

/-- Full original allocator through count retrieval/interpretation, layout,
u64 arithmetic, alignment, capacity, origin/permission/refcount initialization
and fresh pointer publication. Invalid inputs retain their actual errors. -/
theorem allocate_using_frame_exit (layoutOf : MemoryLayoutQuery) (reader : IntegerOperandReader)
    (layouts : ∀ ty, ExceptNoUnwind (layoutOf ty)) (integers : ∀ id value, ExceptNoUnwind (reader id value))
    (ty : Ty) (count : Option ValueId) (align : Option Nat) (origin : AllocationOrigin)
    (refCounted : Bool) (slack : Nat) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (semAllocateUsing layoutOf reader ty count align origin refCounted slack model) := by
  intro state valid
  unfold semAllocateUsing
  cases count <;> dsimp only
  all_goals repeat' first
    | (solve | exact allocate_world_action _ _ _ _ _ _ state valid)
    | (simp only [pure_bind])
    | (refine FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action _ state valid) ?_; intro value state valid _)
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (check_action _ (layouts _ ) state valid) ?_; intro layout state valid _)
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (check_action _ (integers _ _) state valid) ?_; intro integer state valid _)
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (check_action _ (word_operand_no_unwind _ _ _) state valid) ?_; intro count state valid _)
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (check_action _ (word_mul_no_unwind _ _ _) state valid) ?_; intro size state valid _)
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (check_action _ (memory_alignment_no_unwind _ _ _) state valid) ?_; intro alignment state valid _)

/-- Deallocation's actual base/liveness/permission checks and world update
preserve frame identities and history, including every original error exit. -/
theorem dealloc_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semDealloc pointer) := by
  intro state valid
  unfold semDealloc
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
  intro pointer state valid _
  split
  · simp only [pure_bind]
    apply get_bind_exit
    repeat' first
      | (solve | exact True.intro)
      | (solve | exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩)
      | (simp only [pure_bind])
      | split
      | (dsimp only; split)
  all_goals repeat' first
    | exact True.intro
    | split
    | (dsimp only; split)

inductive AllocationFrameInst : Inst → Prop where
  | stack (ty count align) : AllocationFrameInst (.Alloca ty count align)
  | heap (ty count align origin) : AllocationFrameInst (.HeapAlloc ty count align origin)
  | free (pointer) : AllocationFrameInst (.Dealloc pointer)

theorem allocation_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (inst : Inst) (grammar : AllocationFrameInst inst) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) := by
  intro state valid
  cases grammar with
  | stack ty count align =>
    simp only [stepInstWithContext,semAllocaUsing]
    apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state
      (allocate_using_frame_exit _ _ (context_allocation_layout_no_unwind ctx safe) (carrier_integer_no_unwind ctx) _ _ _ _ _ _ _ state valid)
    intro id state valid _
    exact ⟨valid,True.intro,.refl _⟩
  | heap ty count align origin =>
    simp only [stepInstWithContext,semHeapAllocUsing]
    apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state
      (allocate_using_frame_exit _ _ (context_memory_layout_no_unwind ctx safe) (carrier_integer_no_unwind ctx) _ _ _ _ _ _ _ state valid)
    intro id state valid _
    exact ⟨valid,True.intro,.refl _⟩
  | free pointer =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (dealloc_frame_exit pointer state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩

theorem allocation_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy)
    (inst : Inst) (grammar : AllocationFrameInst inst) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  intro state valid
  have stepSafe := allocation_step_frame_exit ctx safe inst grammar state valid
  cases grammar <;> apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state stepSafe
  all_goals
    intro result state valid shape
    cases result with
    | terminator step => cases shape
    | value id =>
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (instruction_results_frame_action ctx _ (.value id) dests state valid)
      intro unit state valid _
      cases unit
      exact ⟨valid,True.intro,.refl _⟩
    | values ids =>
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (instruction_results_frame_action ctx _ (.values ids) dests state valid)
      intro unit state valid _
      cases unit
      exact ⟨valid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
