-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAtomicScalarExits

namespace TrustIr.FrameLifetime

/-- Actual typed comparison cannot fabricate an unwind world, including
nested aggregate, compact-array, pointer/provenance and float comparisons. -/
theorem aggregate_equal_no_unwind (model : ByteModel) (plan : AggregateMemory.Plan) (left right : Value) :
    ExceptNoUnwind (AggregateMemory.equal model plan left right) := by
  apply DecodeFrameExit.no_unwind (fun _ => True)
  apply (block_result_frame_iff _ _).1
  exact AggregateMemory.equal_errors BlockDecodeError (fun _ => True.intro)
    (fun ty value => (block_result_frame_iff _ _).2
      (DecodeFrameExit.of_no_unwind (fun _ => True) _ (cast_float_to_bits_no_unwind ty value) (fun _ _ => True.intro)))
    model plan left right

private theorem check_action {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,True.intro,.refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

private theorem carry_value {α : Type} (before : MachineState) (result : Except SemError (α × MachineState))
    (value : Value) (incoming : MintedValue before.nextFrameLineage value)
    (safe : FrameActionExit (fun _ _ => True) before result) :
    FrameActionExit (fun bound _ => MintedValue bound value) before result := by
  cases result with
  | ok pair => exact ⟨safe.1,incoming.mono safe.2.2.monotone,safe.2.2⟩
  | error error => cases error <;> exact safe

/-- Aggregate RMW uses the original strict load, integer operation, strict
store and old-value publication, including all failures in their actual order. -/
theorem aggregate_rmw_frame_exit (service : AggregateMemory.Service)
    (safe : AggregateMemory.ServiceErrorPolicy BlockDecodeError service)
    (order : FunctionAddressOrder) (op : AtomicRMWOp) (ty : Ty) (pointer operand : ValueId)
    (ordering : MemOrdering) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (AggregateMemory.atomicRMW service order op ty pointer operand ordering model) := by
  intro state valid
  unfold AggregateMemory.atomicRMW
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
  intro pointer state valid _
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action operand state valid)
  intro operand state valid _
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state
    (aggregate_load_value_frame_exit service safe order ty pointer true none model state valid)
  intro current state valid incoming
  apply FrameActionExit.bind (fun bound _ => MintedValue bound current) (fun _ _ => True) _ _ state
    (carry_value state _ current incoming (reject_partial_frame_action operand "AtomicRMW" state valid))
  intro unit state valid incoming
  cases unit
  cases current <;> cases operand <;> dsimp only
  all_goals first
    | exact True.intro
    | (simp only [pure_bind]
       apply FrameActionExit.bind (fun bound _ => MintedValue bound _) (fun _ _ => True) _ _ state
         (carry_value state _ _ incoming (aggregate_store_value_frame_exit service safe _ _ _ _ _ _ _ state valid))
       intro unit state valid incoming
       cases unit
       exact fresh_minted_frame_exit _ state valid incoming)

/-- Aggregate compare-exchange performs actual typed comparison and the
conditional strict store; successful output retains the loaded identity bound. -/
theorem aggregate_exchange_frame_exit (service : AggregateMemory.Service)
    (safe : AggregateMemory.ServiceErrorPolicy BlockDecodeError service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer expected desired : ValueId) (model : ByteModel) :
    FrameActionValid (fun bound (pair : Value × Bool) => MintedValue bound pair.1)
      (AggregateMemory.cmpXchgExchange service order ty pointer expected desired model) := by
  intro state valid
  unfold AggregateMemory.cmpXchgExchange
  apply FrameActionExit.bind MintedValue (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (lookup_value_frame_action pointer state valid)
  intro pointer state valid _
  apply FrameActionExit.bind MintedValue (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (lookup_value_frame_action expected state valid)
  intro expected state valid _
  apply FrameActionExit.bind MintedValue (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (lookup_value_frame_action desired state valid)
  intro desired state valid _
  apply FrameActionExit.bind MintedValue (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state
    (aggregate_load_value_frame_exit service safe order ty pointer true none model state valid)
  intro current state valid incoming
  apply FrameActionExit.bind (fun bound _ => MintedValue bound current) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state
    (carry_value state _ current incoming (reject_partial_frame_action expected "CmpXchg expected" state valid))
  intro unit state valid incoming
  cases unit
  have planSafe := AggregateMemory.checkedPlan_errors BlockDecodeError (fun _ => True.intro) service safe model ty
  apply FrameActionExit.bind (fun bound _ => MintedValue bound current) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state
    (carry_value state _ current incoming (check_action _ (DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 planSafe)) state valid))
  intro plan state valid incoming
  apply FrameActionExit.bind (fun bound _ => MintedValue bound current) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state
    (carry_value state _ current incoming (check_action _ (aggregate_equal_no_unwind model plan current expected) state valid))
  intro success state valid incoming
  cases success
  · simp only [Bool.false_eq_true,↓reduceIte,pure_bind]
    exact ⟨valid,incoming,.refl _⟩
  · simp only [↓reduceIte]
    apply FrameActionExit.bind (fun bound _ => MintedValue bound current) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state
      (carry_value state _ current incoming (aggregate_store_value_frame_exit service safe _ _ _ _ _ _ _ state valid))
    intro unit state valid incoming
    cases unit
    exact ⟨valid,incoming,.refl _⟩

private theorem aggregate_atomic_load_action (service : AggregateMemory.Service)
    (safe : AggregateMemory.ServiceErrorPolicy BlockDecodeError service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (AggregateMemory.atomicLoad service order ty pointer ordering model) := by
  intro state valid
  unfold AggregateMemory.atomicLoad
  by_cases rejected : (!isValidLoadOrdering ordering) = true
  · simp only [rejected,↓reduceIte]
    exact True.intro
  · simp only [rejected,↓reduceIte,pure_bind,AggregateMemory.load]
    apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
    intro pointer state valid _
    apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state
      (aggregate_load_value_frame_exit service safe order ty pointer true none model state valid)
    intro value state valid incoming
    exact fresh_minted_frame_exit value state valid incoming

private theorem aggregate_atomic_store_action (service : AggregateMemory.Service)
    (safe : AggregateMemory.ServiceErrorPolicy BlockDecodeError service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (AggregateMemory.atomicStore service order ty pointer value ordering model) := by
  intro state valid
  unfold AggregateMemory.atomicStore
  by_cases rejected : (!isValidStoreOrdering ordering) = true
  · simp only [rejected,↓reduceIte]
    exact True.intro
  · simp only [rejected,↓reduceIte,pure_bind,AggregateMemory.store]
    apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
    intro pointer state valid _
    apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action value state valid)
    intro value state valid _
    exact aggregate_store_value_frame_exit service safe order ty pointer value true none model state valid

private theorem fresh_exchange_pair (value : Value) (success : Bool) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedValue state.nextFrameLineage value) :
    FrameActionExit (fun _ _ => True) state (Sem.run (Sem.bindFreshPair value (.bool success)) state) := by
  unfold Sem.bindFreshPair
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (fresh_minted_frame_exit value state valid incoming)
  intro first state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (fresh_minted_frame_exit (.bool success) state valid ((mintedValue_iff_shape _ _).2 True.intro))
  intro second state valid _
  exact ⟨valid,True.intro,.refl _⟩

private theorem publish_one_action (action : Sem ValueId) (safe : FrameActionValid (fun _ _ => True) action) :
    FrameActionValid (fun _ result => BodyValueResult result) (do
      let id ← action
      pure (.value (some id))) := by
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (safe state valid)
  intro id state valid _
  exact ⟨valid,True.intro,.refl _⟩

private theorem publish_none_action (action : Sem Unit) (safe : FrameActionValid (fun _ _ => True) action) :
    FrameActionValid (fun _ result => BodyValueResult result) (do
      action
      pure (.value none)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (safe state valid)
  intro unit state valid _
  cases unit
  exact ⟨valid,True.intro,.refl _⟩

theorem atomic_load_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer : ValueId) (ordering : MemOrdering) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.AtomicLoad ty pointer ordering)) := by
  simp only [stepInstWithContext]
  cases selected : ctx.memoryServiceFor ty with
  | none => exact publish_one_action _ (scalar_atomic_load_frame_exit ctx ty pointer ordering)
  | some service => exact publish_one_action _ (aggregate_atomic_load_action service (safe ty service selected) _ _ _ _ _)

theorem atomic_store_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.AtomicStore ty pointer value ordering)) := by
  simp only [stepInstWithContext]
  cases selected : ctx.memoryServiceFor ty with
  | none => exact publish_none_action _ (scalar_atomic_store_frame_exit ctx ty pointer value ordering)
  | some service => exact publish_none_action _ (aggregate_atomic_store_action service (safe ty service selected) _ _ _ _ _ _)

theorem atomic_rmw_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (op : AtomicRMWOp) (ty : Ty) (pointer operand : ValueId) (ordering : MemOrdering) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.AtomicRMW op ty pointer operand ordering)) := by
  simp only [stepInstWithContext]
  cases selected : ctx.memoryServiceFor ty with
  | none => exact publish_one_action _ (scalar_atomic_rmw_frame_exit ctx op ty pointer operand ordering)
  | some service => exact publish_one_action _ (aggregate_rmw_frame_exit service (safe ty service selected) _ _ _ _ _ _ _)

private theorem publish_exchange_action (action : Sem (Value × Bool))
    (safe : FrameActionValid (fun bound (pair : Value × Bool) => MintedValue bound pair.1) action) :
    FrameActionValid (fun _ result => BodyValueResult result) (do
      let pair ← action
      let ids ← Sem.bindFreshPair pair.1 (.bool pair.2)
      pure (.values [ids.1,ids.2])) := by
  intro state valid
  apply FrameActionExit.bind (fun bound (pair : Value × Bool) => MintedValue bound pair.1) (fun _ result => BodyValueResult result) _ _ state (safe state valid)
  intro pair state valid incoming
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (fresh_exchange_pair pair.1 pair.2 state valid incoming)
  intro ids state valid _
  exact ⟨valid,True.intro,.refl _⟩

theorem cmpxchg_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer expected desired : ValueId) (success failure : MemOrdering) (weak : Bool) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.CmpXchg ty pointer expected desired success failure weak)) := by
  cases weak
  · simp only [stepInstWithContext,Bool.false_eq_true,↓reduceIte]
    cases selected : ctx.memoryServiceFor ty with
    | none => exact publish_exchange_action _ (scalar_exchange_frame_exit ctx ty pointer expected desired)
    | some service => exact publish_exchange_action _ (aggregate_exchange_frame_exit service (safe ty service selected) _ _ _ _ _ _)
  · intro state valid
    exact True.intro

/-- The complete atomic instruction family of the current single-threaded
semantics. This does not assert a concurrent memory-model refinement. -/
inductive AtomicFrameInst : Inst → Prop where
  | load (ty pointer ordering) : AtomicFrameInst (.AtomicLoad ty pointer ordering)
  | store (ty pointer value ordering) : AtomicFrameInst (.AtomicStore ty pointer value ordering)
  | rmw (op ty pointer value ordering) : AtomicFrameInst (.AtomicRMW op ty pointer value ordering)
  | exchange (ty pointer expected desired success failure weak) : AtomicFrameInst (.CmpXchg ty pointer expected desired success failure weak)
  | fence (ordering) : AtomicFrameInst (.Fence ordering)

theorem atomic_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (inst : Inst) (grammar : AtomicFrameInst inst) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) := by
  cases grammar
  · exact atomic_load_step_frame_exit ctx safe _ _ _
  · exact atomic_store_step_frame_exit ctx safe _ _ _ _
  · exact atomic_rmw_step_frame_exit ctx safe _ _ _ _ _
  · exact cmpxchg_step_frame_exit ctx safe _ _ _ _ _ _ _
  · intro state valid; exact ⟨valid,True.intro,.refl _⟩

theorem atomic_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy)
    (inst : Inst) (grammar : AtomicFrameInst inst) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  intro state valid
  have stepSafe := atomic_step_frame_exit ctx safe inst grammar state valid
  cases grammar <;> apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state stepSafe
  all_goals
    intro result state valid shape
    cases result with
    | terminator step => cases shape
    | value id =>
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
        (instruction_results_frame_action ctx _ (.value id) dests state valid)
      intro unit state valid _
      cases unit
      exact ⟨valid,True.intro,.refl _⟩
    | values ids =>
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
        (instruction_results_frame_action ctx _ (.values ids) dests state valid)
      intro unit state valid _
      cases unit
      exact ⟨valid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
