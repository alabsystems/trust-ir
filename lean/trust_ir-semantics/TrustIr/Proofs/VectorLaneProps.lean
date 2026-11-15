-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Eval

namespace TrustIr

/-- A lane admitted by the bounded backend predicate passes the general
    semantic lane check, for either inspecting or transporting the value. -/
theorem executableVectorLaneValueMatches_check {elemTy : Ty} {value : Value}
    (allowPoison : Bool)
    (h : elemTy.executableVectorLaneValueMatches value = true) :
    checkVectorLaneType elemTy allowPoison value = .ok () := by
  cases elemTy <;> cases value <;>
    simp_all [Ty.executableVectorLaneValueMatches, Ty.executableIntLane?,
      Value.isIntWidth, Value.isBool, checkVectorLaneType,
      Value.isPoison, Value.isUninit, Ty.semanticIntLaneWidth?] <;> rfl

/-- Every member of a bounded lane payload satisfies its lane predicate. -/
theorem executableVectorLanePayloadMatches_member {elemTy : Ty} {lanes : List Value}
    (h : Ty.executableVectorLanePayloadMatches elemTy lanes = true)
    {value : Value} (hmem : value ∈ lanes) :
    elemTy.executableVectorLaneValueMatches value = true := by
  cases elemTy <;>
    simp_all [Ty.executableVectorLanePayloadMatches,
      Ty.executableVectorLaneValueMatches, Ty.executableIntLane?]

/-- The bounded payload predicates retain their original nonempty domain. -/
theorem executableVectorLanePayloadMatches_nonempty {elemTy : Ty} {lanes : List Value}
    (h : Ty.executableVectorLanePayloadMatches elemTy lanes = true) :
    lanes ≠ [] := by
  intro he
  subst lanes
  cases elemTy <;> simp [Ty.executableVectorLanePayloadMatches, Ty.executableIntLane?] at h

/-- A bounded payload's lane type is admitted by general vector execution. -/
theorem executableVectorLanePayloadMatches_semantic {elemTy : Ty} {lanes : List Value}
    (h : Ty.executableVectorLanePayloadMatches elemTy lanes = true) :
    elemTy.semanticVectorLane = true := by
  cases elemTy <;>
    simp_all [Ty.executableVectorLanePayloadMatches, Ty.executableIntLane?,
      Ty.semanticVectorLane, Ty.semanticIntLaneWidth?, Ty.isFloat] <;> rfl

private theorem executableBoolVectorLanes_cases (count lanes : Nat)
    (h : (Ty.Vector count .Bool).executableBoolVectorLanes? = some lanes) :
    lanes = count ∧ (count = 16 ∨ count = 8 ∨ count = 4 ∨ count = 2) := by
  unfold Ty.executableBoolVectorLanes? at h
  split at h <;> simp_all

private theorem mem_of_get?_eq_some {α : Type} {xs : List α} {index : Nat} {x : α}
    (h : trustIrListGet? xs index = some x) : x ∈ xs := by
  trustIrCompilerProof {
    rcases List.get?_eq_some.mp h with ⟨hIndex, hEq⟩
    exact List.mem_iff_get.mpr ⟨⟨index, hIndex⟩, hEq⟩
  } {
    exact CompilerCompat.listGetConstructive_mem h
  }

/-- The original bounded vector shapes establish the general census check. -/
theorem executableVectorPayloadMatches_shape {count : Nat} {elemTy : Ty}
    {lanes : List Value}
    (h : (Ty.Vector count elemTy).executableVectorPayloadMatches lanes = true) :
    checkVectorShape count elemTy lanes = .ok () := by
  have hFacts : lanes.length = count ∧ count ≠ 0 ∧ elemTy.semanticVectorLane = true := by
    cases elemTy <;>
      simp [Ty.executableVectorPayloadMatches, Ty.executableIntVectorWidth?,
        Ty.executableIntLane?, Ty.executableBoolVectorLanes?,
        Ty.semanticVectorLane, Ty.semanticIntLaneWidth?, Ty.isFloat] at h ⊢
    all_goals repeat' split at h
    all_goals try (simp_all <;> omega)
    rename_i lanes hClassifier
    have hBool := executableBoolVectorLanes_cases count lanes hClassifier
    simp_all
    omega
  rcases hFacts with ⟨hLen, hNonzero, hLane⟩
  simp [checkVectorShape, hLen, hNonzero, hLane, bind, pure, Except.bind, Except.pure]

/-- A bounded whole-vector payload also satisfies the lane-only predicate. -/
theorem executableVectorPayloadMatches_lanePayload {count : Nat} {elemTy : Ty}
    {lanes : List Value}
    (h : (Ty.Vector count elemTy).executableVectorPayloadMatches lanes = true) :
    elemTy.executableVectorLanePayloadMatches lanes = true := by
  cases elemTy <;>
    simp [Ty.executableVectorPayloadMatches, Ty.executableIntVectorWidth?,
      Ty.executableIntLane?, Ty.executableBoolVectorLanes?,
      Ty.executableVectorLanePayloadMatches] at h ⊢
  all_goals repeat' split at h
  all_goals try simp_all
  rename_i lanes hClassifier
  have hBool := executableBoolVectorLanes_cases count lanes hClassifier
  simp_all
  omega

/-- Extraction of a lane in an existing bounded payload remains executable
    through the general selected-lane implementation. -/
theorem getVectorElement_of_executablePayload {elemTy : Ty} {lanes : List Value}
    {index : Nat} {lane : Value}
    (hPayload : elemTy.executableVectorLanePayloadMatches lanes = true)
    (hGet : trustIrListGet? lanes index = some lane) :
    getVectorElement elemTy (.vector lanes) index = .ok lane := by
  have hLane := executableVectorLanePayloadMatches_member hPayload (mem_of_get?_eq_some hGet)
  have hCheck := executableVectorLaneValueMatches_check true hLane
  have hSemantic := executableVectorLanePayloadMatches_semantic hPayload
  have hNonempty := executableVectorLanePayloadMatches_nonempty hPayload
  have hNotEmpty : lanes.isEmpty = false := by
    cases lanes <;> simp_all [List.isEmpty]
  simp [getVectorElement, hSemantic, hNotEmpty,
    hGet, hCheck, bind, pure, Except.bind, Except.pure]

/-- Insertion into a bounded payload remains executable, while the runtime
    implementation itself admits all positive scalar-vector lane counts. -/
theorem setVectorElement_of_executablePayload {count : Nat} {elemTy : Ty}
    {lanes : List Value} {index : Nat} {newValue : Value}
    (hPayload : (Ty.Vector count elemTy).executableVectorPayloadMatches lanes = true)
    (hValue : elemTy.executableVectorLaneValueMatches newValue = true)
    (hIndex : index < lanes.length) :
    setVectorElement (.Vector count elemTy) (.vector lanes) index newValue =
      .ok (.vector (lanes.set index newValue)) := by
  have hShape := executableVectorPayloadMatches_shape hPayload
  have hCheckNew := executableVectorLaneValueMatches_check false hValue
  let previous := lanes.get ⟨index, hIndex⟩
  have hGet : trustIrListGet? lanes index = some previous := by
    trustIrCompilerProof { exact List.get?_eq_get hIndex } {
      exact CompilerCompat.listGet?_eq_get hIndex
    }
  have hLane := executableVectorLanePayloadMatches_member
    (executableVectorPayloadMatches_lanePayload hPayload) (mem_of_get?_eq_some hGet)
  have hCheckPrevious := executableVectorLaneValueMatches_check true hLane
  simp [setVectorElement, hShape, hCheckNew, hGet, hCheckPrevious,
    bind, pure, Except.bind, Except.pure]

/-- Unary structural traversal preserves the payload census at every size. -/
theorem semVectorUnOp_length (op : UnOp) (elemTy : Ty)
    {lanes result : List Value} (h : semVectorUnOp op elemTy lanes = .ok result) :
    result.length = lanes.length := by
  induction lanes generalizing result with
  | nil => simp [semVectorUnOp] at h; subst result; rfl
  | cons lane lanes ih =>
    cases hLane : semVectorUnOpLane op elemTy lane with
    | error e => simp [semVectorUnOp, hLane, bind, Except.bind] at h
    | ok first =>
      cases hRest : semVectorUnOp op elemTy lanes with
      | error e => simp [semVectorUnOp, hLane, hRest, bind, Except.bind] at h
      | ok rest =>
        simp [semVectorUnOp, hLane, hRest, bind, pure, Except.bind, Except.pure] at h
        subst result
        simp [ih hRest]

/-- Binary structural traversal preserves both source censuses. -/
theorem semVectorBinOp_length (op : BinOp) (elemTy : Ty)
    {lhs rhs result : List Value} (h : semVectorBinOp op elemTy lhs rhs = .ok result) :
    result.length = lhs.length ∧ lhs.length = rhs.length := by
  induction lhs generalizing rhs result with
  | nil => cases rhs <;> simp [semVectorBinOp] at h; subst result; exact ⟨rfl, rfl⟩
  | cons left lhs ih =>
    cases rhs with
    | nil => simp [semVectorBinOp] at h
    | cons right rhs =>
      cases hLane : semVectorBinOpLane op elemTy left right with
      | error e => simp [semVectorBinOp, hLane, bind, Except.bind] at h
      | ok first =>
        cases hRest : semVectorBinOp op elemTy lhs rhs with
        | error e => simp [semVectorBinOp, hLane, hRest, bind, Except.bind] at h
        | ok rest =>
          simp [semVectorBinOp, hLane, hRest, bind, pure, Except.bind, Except.pure] at h
          subst result
          obtain ⟨hLeft, hRight⟩ := ih hRest
          simp [hLeft, hRight]

/-- Boolean unary execution covers any positive declared lane count. -/
theorem semUnOpValue_bool_not_replicate (count : Nat) (value : Bool) :
    semUnOpValue .Not (.Vector (count + 1) .Bool)
      (.vector (List.replicate (count + 1) (.bool value))) =
    .ok (.vector (List.replicate (count + 1) (.bool (!value)))) := by
  have hLanes : ∀ n, semVectorUnOp .Not .Bool (List.replicate n (.bool value)) =
      .ok (List.replicate n (.bool (!value))) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hLane : semVectorUnOpLane .Not .Bool (.bool value) =
          .ok (.bool (!value)) := rfl
      simp [List.replicate, semVectorUnOp, hLane, ih,
        bind, pure, Except.bind, Except.pure]
  have hShape : checkVectorShape (count + 1) .Bool
      (List.replicate (count + 1) (.bool value)) = .ok () := by
    simp [checkVectorShape, Ty.semanticVectorLane,
      bind, pure, Except.bind, Except.pure]
  change (checkVectorShape (count + 1) .Bool
    (List.replicate (count + 1) (.bool value)) >>= fun _ =>
    semVectorUnOp .Not .Bool (List.replicate (count + 1) (.bool value)) >>= fun result =>
    pure (Value.vector result)) = _
  rw [hShape, hLanes]
  rfl

/-- A zero-lane declared vector is refused before lane execution. -/
theorem semUnOpValue_zero_vector (op : UnOp) (elemTy : Ty) (lanes : List Value) :
    semUnOpValue op (.Vector 0 elemTy) (.vector lanes) =
      .error (.unsupported .vectorShape "zero-lane vectors are not executable") := rfl

/-- Inspecting an Undef lane is UB for every declared lane type. -/
theorem checkVectorLaneType_undef_inspect (elemTy undefTy : Ty) :
    checkVectorLaneType elemTy false (.undef undefTy) =
      .error (.ub "vector operation: use of an uninitialized lane") := rfl

/-- The lane transport check preserves poison without inspecting its image. -/
theorem checkVectorLaneType_undef_transport (elemTy undefTy : Ty) :
    checkVectorLaneType elemTy true (.undef undefTy) = .ok () := rfl

/-- Extraction inspects the selected lane, leaving arbitrary other lanes alone. -/
theorem getVectorElement_bool_head (value : Bool) (rest : List Value) :
    getVectorElement .Bool (.vector (.bool value :: rest)) 0 = .ok (.bool value) := rfl

/-- Insertion transports an unrelated poison lane while checking the new lane. -/
theorem setVectorElement_transports_unselected_poison (oldValue newValue : Bool) (ty : Ty) :
    setVectorElement (.Vector 2 .Bool) (.vector [.bool oldValue, .undef ty]) 0
      (.bool newValue) = .ok (.vector [.bool newValue, .undef ty]) := rfl

/-- The scalar and vector spelling of conjunction use the same Bool operation. -/
theorem semBoolBinOp_conjunction (lhs rhs : Bool) :
    semBoolBinOp .And lhs rhs = .ok (lhs && rhs) ∧
    semBoolBinOp .BAnd lhs rhs = .ok (lhs && rhs) := ⟨rfl, rfl⟩

/-- Both disjunction spellings return a logical Bool. -/
theorem semBoolBinOp_disjunction (lhs rhs : Bool) :
    semBoolBinOp .Or lhs rhs = .ok (lhs || rhs) ∧
    semBoolBinOp .BOr lhs rhs = .ok (lhs || rhs) := ⟨rfl, rfl⟩

/-- Both exclusive-or spellings return a logical Bool. -/
theorem semBoolBinOp_exclusive_or (lhs rhs : Bool) :
    semBoolBinOp .Xor lhs rhs = .ok (Bool.xor lhs rhs) ∧
    semBoolBinOp .BXor lhs rhs = .ok (Bool.xor lhs rhs) := ⟨rfl, rfl⟩

/-- Scalar and vector Bool dispatch agree on success and operator refusal. -/
theorem semVectorBinOpLane_bool_agrees (op : BinOp) (lhs rhs : Bool) :
    semVectorBinOpLane op .Bool (.bool lhs) (.bool rhs) =
      semBoolBinOpValues op (.bool lhs) (.bool rhs) := rfl

/-- The bare helper admits actual Bool values at the Bool static type. Its
    separate legacy integer-carrier path is not a typed Bool guarantee. -/
theorem semBinOpValues_bool_agrees (op : BinOp) (lhs rhs : Bool) :
    semBinOpValues op .Bool (.bool lhs) (.bool rhs) =
      semBoolBinOpValues op (.bool lhs) (.bool rhs) := rfl

/-- The typed Bool boundary refuses integer carriers, irrespective of width. -/
theorem semBoolBinOpValues_int_refused (op : BinOp) (width : Nat) (raw : Int)
    (rhs : Bool) :
    semBoolBinOpValues op (.int width raw) (.bool rhs) =
      .error (.typeError "Bool BinOp: expected boolean operands") := rfl

/-- Both operands are inspected before their Bool carriers or operator are
    checked, including the right operand of a non-short-circuiting connective. -/
theorem semBoolBinOpValues_rhs_undef_priority (op : BinOp) (lhs : Value) (ty : Ty) :
    semBoolBinOpValues op lhs (.undef ty) =
      .error (.ub "Bool BinOp: use of an uninitialized operand") := by
  simp [semBoolBinOpValues, Value.isPoison, Value.isUninit,
    bind, pure, Except.bind, Except.pure]

/-- Real contextual execution enforces Bool carriers while the bare integer
    helper retains its existing arbitrary-result-type contract. -/
theorem run_contextual_bool_binop_int_refused (ctx : EvalContext) (s : MachineState)
    (op : BinOp) (lhsId rhsId : ValueId) (width : Nat) (raw : Int) (rhs : Bool)
    (hLhs : s.lookupValue lhsId = some (.int width raw))
    (hRhs : s.lookupValue rhsId = some (.bool rhs)) :
    Sem.run (stepInstWithContext ctx (.BinOp op .Bool lhsId rhsId)) s =
      .error (.typeError "Bool BinOp: expected boolean operands") := by
  simp [stepInstWithContext, semBoolBinOpInst, Sem.lookupValue, hLhs, hRhs,
    semBoolBinOpValues, Value.isPoison, Value.isUninit, Sem.getState,
    Sem.run, StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.pure,
    bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]

end TrustIr
