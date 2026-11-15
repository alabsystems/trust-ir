-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameIndirectInvokeExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem ok_safe {α : Type} (value : α) : ExceptNoUnwind (.ok value) := by
  intro exception after run
  cases run

private theorem type_safe {α : Type} (message : String) :
    ExceptNoUnwind (.error (.typeError message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem ub_safe {α : Type} (message : String) :
    ExceptNoUnwind (.error (.ub message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem unsupported_safe {α : Type} (feature : UnsupportedFeature) (message : String) :
    ExceptNoUnwind (.error (.unsupported feature message) : Except SemError α) := by
  intro exception after run
  cases run

theorem ExceptNoUnwind.forIn {α β : Type} (items : List α) (initial : β)
    (action : α → β → Except SemError (ForInStep β))
    (safe : ∀ item value, ExceptNoUnwind (action item value)) :
    ExceptNoUnwind (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact ok_safe _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply ExceptNoUnwind.bind _ _ (safe item initial)
    intro step
    cases step with
    | done value => exact ok_safe _
    | yield value => exact ih value

theorem ExceptNoUnwind.forM {α : Type} (items : List α) (action : α → Except SemError Unit)
    (safe : ∀ item, ExceptNoUnwind (action item)) : ExceptNoUnwind (items.forM action) := by
  induction items with
  | nil => exact ok_safe _
  | cons item rest ih =>
    change ExceptNoUnwind (action item >>= fun _ => rest.forM action)
    exact ExceptNoUnwind.bind _ _ (safe item) (fun _ => ih)

private theorem leaf_range_no_unwind {α : Type} (check : α → Except SemError Unit)
    (safe : ∀ value, ExceptNoUnwind (check value)) {size : Nat} (leaf : CompactArray.Leaf α size)
    (offset count : Nat) : ExceptNoUnwind (leaf.checkRangeSpec check offset count) := by
  induction leaf generalizing offset count with
  | nil => simp only [CompactArray.Leaf.checkRangeSpec]; split <;> exact ok_safe _
  | cons head tail ih =>
    rw [CompactArray.Leaf.checkRangeSpec]
    split
    · exact ok_safe _
    · split
      · exact ExceptNoUnwind.bind _ _ (safe head) (fun _ => ih 0 (count-1))
      · exact ih (offset-1) count

/-- Pure compressed-array validation propagates only callback errors, including
clipped periodic windows; it cannot invent a runtime throw state. -/
theorem tree_range_no_unwind {α : Type} (check : α → Except SemError Unit)
    (safe : ∀ value, ExceptNoUnwind (check value)) {size : Nat} (tree : CompactArray.Tree α size)
    (offset count : Nat) : ExceptNoUnwind (tree.checkRangeSpec check offset count) := by
  induction tree generalizing offset count with
  | uniform n value =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact safe value
  | dense small values =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact leaf_range_no_unwind check safe values _ _
  | split large left right ihl ihr =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact ExceptNoUnwind.bind _ _ (ihl _ _) (fun _ => ihr _ _)
  | periodic unit positive phase n ih =>
    rw [CompactArray.Tree.checkRangeSpec]
    split
    · exact ok_safe _
    · exact ExceptNoUnwind.bind _ _ (ih _ _) (fun _ => ih _ _)

theorem tree_stored_no_unwind {α : Type} (check : α → Except SemError Unit)
    (safe : ∀ value, ExceptNoUnwind (check value)) {size : Nat} (tree : CompactArray.Tree α size) :
    ExceptNoUnwind (tree.checkStored check) := by
  rw [← tree.checkRangeSpec_full]
  exact tree_range_no_unwind check safe tree 0 size

private theorem float_no_unwind (ty : Ty) (value : Float) : ExceptNoUnwind (checkFloatAt ty value) := by
  unfold checkFloatAt
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | split

set_option maxHeartbeats 2000000 in
/-- Every structural budget and every value/type shape of the original
closure validator is free of dynamic unwind errors, for arbitrary contexts. -/
theorem closure_value_at_no_unwind (ctx : EvalContext) (fuel : Nat) (ty : Ty) (value : Value) :
    ExceptNoUnwind (checkClosureValueAt ctx fuel ty value) := by
  induction fuel generalizing ty value with
  | zero => exact unsupported_safe _ _
  | succ fuel ih =>
    unfold checkClosureValueAt
    repeat' first
      | exact ok_safe _
      | exact type_safe _
      | exact ub_safe _
      | exact unsupported_safe _ _
      | exact float_no_unwind _ _
      | exact ih _ _
      | exact ExceptNoUnwind.forM _ _ (fun value => ih _ value)
      | (refine tree_stored_no_unwind _ (fun value => ?_) _)
      | (refine ExceptNoUnwind.forM _ _ (fun input => ?_); cases input <;> dsimp only)
      | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
      | split

theorem closure_value_no_unwind (ctx : EvalContext) (ty : Ty) (value : Value) :
    ExceptNoUnwind (checkClosureValue ctx ty value) :=
  closure_value_at_no_unwind ctx (value.depth+1) ty value


local macro "closure_validation_leaves" : tactic => `(tactic|
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | exact unsupported_safe _ _
    | exact closure_value_no_unwind _ _ _
    | (refine ExceptNoUnwind.forM _ _ (fun input => ?_); cases input <;> dsimp only)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split)

/-- Nominal closure header resolution never reads functionErrors. -/
theorem closure_contract_no_unwind (ctx : EvalContext) (cid : ClosureTyId) (fn : FuncId) :
    ExceptNoUnwind (closureContract ctx cid fn) := by
  unfold closureContract
  closure_validation_leaves

theorem make_closure_no_unwind (ctx : EvalContext) (cid : ClosureTyId) (fn : FuncId) (captures : List Value) :
    ExceptNoUnwind (makeClosureValue ctx cid fn captures) := by
  unfold makeClosureValue
  apply ExceptNoUnwind.bind _ _ (closure_contract_no_unwind ctx cid fn)
  intro input
  rcases input with ⟨definition,signature,target⟩
  dsimp only
  closure_validation_leaves

theorem closure_call_no_unwind (ctx : EvalContext) (cid : ClosureTyId) (fn : FuncId)
    (captures : List Value) (sig : FuncTyId) (args : List Value) (conv : CallingConv) :
    ExceptNoUnwind (closureCall ctx cid fn captures sig args conv) := by
  unfold closureCall
  apply ExceptNoUnwind.bind _ _ (closure_contract_no_unwind ctx cid fn)
  intro input
  rcases input with ⟨definition,signature,target⟩
  dsimp only
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | exact make_closure_no_unwind _ _ _ _
    | exact closure_value_no_unwind _ _ _
    | (refine ExceptNoUnwind.forM _ _ (fun input => ?_); cases input <;> dsimp only)
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split


theorem checked_closure_captures_no_unwind (ctx : EvalContext) (cid : ClosureTyId) (captures : List Value) :
    ExceptNoUnwind (checkedClosureCaptures ctx cid captures) := by
  unfold checkedClosureCaptures
  closure_validation_leaves

theorem closure_extract_no_unwind (ctx : EvalContext) (ty : Ty) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) :
    ExceptNoUnwind (closureExtract ctx ty cid fn captures field) := by
  unfold closureExtract
  apply ExceptNoUnwind.bind _ _ (checked_closure_captures_no_unwind ctx cid captures)
  intro definition
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | exact ub_safe _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split

theorem closure_insert_no_unwind (ctx : EvalContext) (ty : Ty) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) (value : Value) :
    ExceptNoUnwind (closureInsert ctx ty cid fn captures field value) := by
  unfold closureInsert
  repeat' first
    | exact ok_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact checked_closure_captures_no_unwind _ _ _
    | exact closure_value_no_unwind _ _ _
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun input => ?_) <;> dsimp only)
    | split

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem throw_no_unwind {α : Type} (error : SemError)
    (safe : ExceptNoUnwind (.error error : Except SemError α)) : CallCheckNoUnwind (throw error : Sem α) := by
  intro state exception after run
  cases run
  exact safe exception after rfl

theorem CallCheckNoUnwind.forIn {α β : Type} (items : List α) (initial : β)
    (action : α → β → Sem (ForInStep β))
    (safe : ∀ item value, CallCheckNoUnwind (action item value)) :
    CallCheckNoUnwind (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact pure_no_unwind _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply CallCheckNoUnwind.bind _ _ (safe item initial)
    intro step
    cases step with
    | done value => exact pure_no_unwind _
    | yield value => exact ih value

/-- Original return checks, including recursive typed-closure membership,
cannot forge an unwind state. Every poison/closure flag combination is covered. -/
theorem checked_returns_no_unwind (ctx : EvalContext) (returnTys : List Ty)
    (poison closure : Bool) (message : String) (values : List Value) :
    CallCheckNoUnwind (checkReturns ctx returnTys poison closure message values) := by
  unfold checkReturns
  apply CallCheckNoUnwind.bind
  · split <;> first
      | exact pure_no_unwind _
      | exact throw_no_unwind _ (type_safe _)
  · intro _
    apply CallCheckNoUnwind.bind
    · cases poison <;> simp only [Bool.false_eq_true,if_false,if_true]
      · exact pure_no_unwind _
      · unfold Sem.rejectPoisonValues
        split <;> first
          | exact pure_no_unwind _
          | exact throw_no_unwind _ (ub_safe _)
    · intro _
      cases closure <;> simp only [Bool.false_eq_true,if_false,if_true]
      · exact pure_no_unwind _
      · apply CallCheckNoUnwind.bind
        · apply CallCheckNoUnwind.forIn
          intro input _
          rcases input with ⟨ty,value⟩
          dsimp only
          cases checked : checkClosureValue ctx ty value with
          | ok unit =>
            cases unit
            simp only [checked,pure_bind]
            exact pure_no_unwind _
          | error error =>
            simp only [checked]
            apply CallCheckNoUnwind.bind _ _ (throw_no_unwind error ?_) (fun _ => pure_no_unwind _)
            rw [← checked]
            exact closure_value_no_unwind ctx ty value
        · intro _
          exact pure_no_unwind _

/-- Checked plain-call exits now discharge recursive closure-return validation
without a separate no-unwind hypothesis. Actual callee exits remain explicit. -/
theorem checked_call_frame_exit (ctx : EvalContext) (returnTys : List Ty)
    (poison closure : Bool) (message : String) (callee : Sem (List Value))
    (state : MachineState) (valid : WellMintedState state)
    (execution : FrameCalleeExit (callerWorld state) (Sem.run callee (callerWorld state))) :
    FrameCalleeExit state (Sem.run (callFrameWith (checkReturns ctx returnTys poison closure message) callee) state) :=
  call_frame_with_exit _ callee state valid
    (fun returned => check_returns_readonly ctx returnTys poison closure message returned)
    (fun returned => checked_returns_no_unwind ctx returnTys poison closure message returned) execution

end TrustIr.FrameLifetime
