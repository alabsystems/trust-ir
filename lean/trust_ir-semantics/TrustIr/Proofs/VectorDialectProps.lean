-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Refinement proofs for the portable vector dialect.
-- Shows that vector.* dialect operations preserve core IR semantics
-- when lowered to equivalent core instruction sequences.

import TrustIr.Semantics.VectorDialect
import TrustIr.Proofs.TransformCorrectness
import TrustIr.Proofs.IntResidue
import TrustIr.Proofs.MetaTheorems
import TrustIr.Proofs.VectorLaneProps

/-- Select the actual standard bang lookup on each compiler. -/
macro "trustIrVectorGet! " values:term:max index:term:max : term => do
  if Lean.versionString == "4.8.0" then `(List.get! $values $index)
  else if Lean.versionString == "4.30.0-rc2" then `($values[$index]!)
  else Lean.Macro.throwError "unsupported compiler for vector operand lookup"

namespace TrustIr
namespace VectorDialect

/-!
# Vector Dialect Refinement

This module discharges a `DialectLowerSound`-style obligation for the
`vector.*` ops the production Rust pass (`crates/trust-ir/src/dialect/vector.rs`,
`VectorLoweringPass`) actually rewrites: `vector.pack_lanes`,
`vector.mask_to_bits`, `vector.reduce`, and `vector.shuffle` (fast-4).
(`extract_lane` /
`insert_lane` are *not* rewritten by that pass — TrustCg lowers them directly
to single target ops — but their single-instruction refinements are also
proven here, `runsAgree_extract_lane` and `runsAgree_insert_lane`.
`vector.fma` is deliberately never rewritten: the ratified fast-4 policy
forbids the double-rounding unfused fallback, so there is no lowering to
refine.)

Because the production lowering allocates fresh SSA ids (`ctx.alloc_value()`),
the standard `DialectLowerSound` schema (`TrustIr.DialectLowerSound`, which
demands *full* `MachineState` equality via `runsAgree`) is too strong: the
lowered sequence binds extra fresh locals the dialect op never created. We
therefore work with the documented equal-except-locals refinement
`runsAgreeFrom` — a function of the runtime allocator counter (`s.nextValueId`),
faithfully modelling `ctx.alloc_value()` — and state the soundness theorem over
`vectorLowerFrom`, the base-threaded lowering whose emitted instruction sequence
matches the Rust pass byte-for-byte (zero-`Const` pack seed; shared-zero /
seed-accumulator prologue; per-lane `ExtractElement`/`Select`/`BinOp .Or` fold).
See `vectorLowerFrom_pack_lanes_sound` / `vectorLowerFrom_mask_to_bits_sound`
and the dispatch theorem `vectorLowerFrom_sound`.

The earlier in-file `vectorLower : Lowering` (hardcoded `ValueId.mk 0`) is a
`Lowering`-typed *shape witness* only: it cannot thread fresh ids and so cannot
satisfy any agreement statement (its mask arm never reassembles the packed
integer). The genuine, Rust-faithful discharge is `vectorLowerFrom_sound`.
-/

/-- Lowering for the vector dialect. -/
noncomputable def vectorLower : Lowering
  | op =>
    open Classical in
    if op.dialect = dialectName then
      match op.op with
      | "extract_lane" =>
        match decodeExtractLane op.inst with
        | .ok spec =>
          .ok [.ExtractElement spec.elemTy ((trustIrVectorGet! op.inst.operands 0)) (ValueId.mk 0)]
        | .error _ => .error "vectorLower: failed to decode extract_lane"
      | "insert_lane" =>
        match decodeInsertLane op.inst with
        | .ok spec =>
          .ok [.InsertElement spec.vectorTy ((trustIrVectorGet! op.inst.operands 0)) (ValueId.mk 0) ((trustIrVectorGet! op.inst.operands 1))]
        | .error _ => .error "vectorLower: failed to decode insert_lane"
      | "pack_lanes" =>
        match decodePackLanes op.inst with
        | .ok spec => .ok (lowerPackLanes spec.vectorTy op.inst.operands 0)
        | .error _ => .error "vectorLower: failed to decode pack_lanes"
      | "mask_to_bits" =>
        match decodeMaskToBits op.inst with
        | .ok spec => .ok (lowerMaskToBits spec.resultTy ((trustIrVectorGet! op.inst.operands 0)) spec.lanes)
        | .error _ => .error "vectorLower: failed to decode mask_to_bits"
      | _ => .error s!"vectorLower: unsupported op {op.op}"
    else
      .error s!"vectorLower: expected dialect {dialectName}, got {op.dialect}"
where
  lowerPackLanes (vectorTy : Ty) (operands : List ValueId) (idxBase : Nat) : List Inst :=
    match operands with
    | [] => []
    | laneId :: rest =>
      .InsertElement vectorTy (ValueId.mk 0) (ValueId.mk idxBase) laneId ::
        lowerPackLanes vectorTy rest (idxBase + 1)

  lowerMaskToBits (resultTy : Ty) (maskId : ValueId) (lanes : Nat) : List Inst :=
    match lanes with
    | 0 => []
    | n + 1 =>
      -- Lowering: ExtractElement logical bool lane, then Select it to build mask.
      -- This is a simplified model for the induction.
      .ExtractElement .Bool maskId (ValueId.mk n) ::
        lowerMaskToBits resultTy maskId n

/-!
## Observational equivalence (weakened for SSA) -/

/-- Refined observational equivalence that allows for different SSA bindings
    (locals) in the final state, as long as all other state fields
    (memory, permissions, etc.) are identical and the computed results match. -/
def runsAgree_SSA (op : DialectOpSem) (lowered : List Inst) : Prop :=
  ∀ (s : MachineState),
    match op.runOp s with
    | .ok s1 => exists r s2, Sem.run (runInsts lowered) s = .ok (r, s2) ∧
                state_equiv_except_locals s1 s2 ∧
                -- Soundness: the result produced by the dialect op (s1.nextValueId - 1)
                -- must match the result produced by the lowered sequence (s2.nextValueId - 1).
                exists v1 v2, s1.lookupValue (ValueId.mk (s1.nextValueId - 1)) = some v1 ∧
                              s2.lookupValue (ValueId.mk (s2.nextValueId - 1)) = some v2 ∧
                              v1 = v2
    | .error e => Sem.run (runInsts lowered) s = .error e

/-!
## Refinement Lemma: vector.extract_lane
-/

/-- State-restricted SSA agreement. The domain is checked at the actual
    input state and may include poison lanes or outcomes that refuse. -/
def runsAgree_SSAOn (domain : MachineState → Prop)
    (op : DialectOpSem) (lowered : List Inst) : Prop :=
  ∀ s, domain s →
    match op.runOp s with
    | .ok s1 => exists r s2, Sem.run (runInsts lowered) s = .ok (r, s2) ∧
        state_equiv_except_locals s1 s2 ∧
        exists v1 v2, s1.lookupValue (ValueId.mk (s1.nextValueId - 1)) = some v1 ∧
          s2.lookupValue (ValueId.mk (s2.nextValueId - 1)) = some v2 ∧ v1 = v2
    | .error e => Sem.run (runInsts lowered) s = .error e

/-- The typed extraction domain records only this state's generated index,
    vector constructor and declared census. Lane contents may contain poison. -/
def extractLaneDomain (inst : DialectInst) (spec : ExtractLaneSpec)
    (idxId : ValueId) (s : MachineState) : Prop :=
  s.lookupValue idxId = some (.int 64 (Int.ofNat spec.lane)) ∧
    ∃ lanes, s.lookupValue ((trustIrVectorGet! inst.operands 0)) = some (.vector lanes) ∧
      lanes.length = spec.lanes

/-- A dialect extract carries the full declared vector census; core Extract
    carries only its result lane type. Their complete outcomes agree on the
    actual typed input domain, including selected poison and lane refusals. -/
theorem runsAgree_extract_lane (op : DialectOpSem) (spec : ExtractLaneSpec)
    (hDec : decodeExtractLane op.inst = .ok spec)
    (hRun : op.runOp = runSpec op.inst (.extractLane spec))
    (idxId : ValueId) :
    runsAgree_SSAOn (extractLaneDomain op.inst spec idxId) op
      [.ExtractElement spec.elemTy ((trustIrVectorGet! op.inst.operands 0)) idxId] := by
  trustIrCompilerProof {
    intro s hDomain
    obtain ⟨hIdx, lanes, hVecRaw, hCount⟩ := hDomain
    rw [hRun]
    unfold runSpec runExtractLane
    match hOps : op.inst.operands with
    | [vectorId] =>
      have hg : (trustIrVectorGet! ([vectorId] : List ValueId) 0) = vectorId := rfl
      have hVecS : s.lookupValue vectorId = some (.vector lanes) := by
        rw [hOps, hg] at hVecRaw; exact hVecRaw
      have hlt : ¬ ((↑spec.lane : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg spec.lane)
      simp only [hOps, hg, hVecS, hCount, bne_self_eq_false, Bool.false_eq_true,
        if_false, bind, Except.bind, pure, Except.pure]
      cases hLane : getVectorElement spec.elemTy (.vector lanes) spec.lane with
      | error e =>
        simp only [hLane]
        simp [runInsts, stepInst, Ty.bitWidthFor, semExtractElement, semExtractElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hLane, hlt,
          Sem.getState, Sem.bindFresh, Sem.throwUB, Sem.throwTypeError, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
      | ok lane =>
        simp only [hLane]
        simp [runInsts, stepInst, Ty.bitWidthFor, semExtractElement, semExtractElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hLane, hlt,
          bindFreshValue, Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, MachineState.bindValue]
        refine ⟨?_, lane, ?_, lane, ?_, rfl⟩
        · exact state_equiv_except_locals_refl _
        · simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]
        · simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]
    | [] =>
      exfalso
      unfold decodeExtractLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst extractLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
    | a :: b :: rest =>
      exfalso
      unfold decodeExtractLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst extractLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
  } {
    intro s hDomain
    obtain ⟨hIdx, lanes, hVecRaw, hCount⟩ := hDomain
    rw [hRun]
    unfold runSpec runExtractLane
    match hOps : op.inst.operands with
    | [vectorId] =>
      have hg : (trustIrVectorGet! ([vectorId] : List ValueId) 0) = vectorId := rfl
      have hVecS : s.lookupValue vectorId = some (.vector lanes) := by
        rw [hOps, hg] at hVecRaw; exact hVecRaw
      have hlt : ¬ ((↑spec.lane : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg spec.lane)
      simp only [hOps, hg, hVecS, hCount, bne_self_eq_false, Bool.false_eq_true,
        if_false, bind, Except.bind, pure, Except.pure]
      cases hLane : getVectorElement spec.elemTy (.vector lanes) spec.lane with
      | error e =>
        simp only [hLane]
        simp [runInsts, stepInst, Ty.bitWidthFor, semExtractElement, semExtractElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hLane, hlt,
          Sem.getState, Sem.bindFresh, Sem.throwUB, Sem.throwTypeError, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
      | ok lane =>
        simp only [hLane]
        simp [runInsts, stepInst, Ty.bitWidthFor, semExtractElement, semExtractElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hLane, hlt,
          bindFreshValue, Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, MachineState.bindValue]
        refine ⟨state_equiv_except_locals_refl _, lane, ?_⟩
        simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]
    | [] =>
      exfalso
      unfold decodeExtractLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst extractLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
    | a :: b :: rest =>
      exfalso
      unfold decodeExtractLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst extractLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
  }

private def extractProofInst (lane : Nat := 0) : DialectInst :=
  extractLane (.Vector 4 .I32) .I32 (ValueId.mk 0) lane

private def extractProofSpec (lane : Nat := 0) : ExtractLaneSpec :=
  { vectorTy := .Vector 4 .I32, elemTy := .I32, lanes := 4, lane := lane }

private def extractProofState (lanes : List Value) (index : Nat := 0) : MachineState :=
  { MachineState.empty with
    locals := (ValueMap.empty.set (ValueId.mk 0) (.vector lanes)).set
      (ValueId.mk 1) (.int 64 (Int.ofNat index))
    nextValueId := 2 }

private def extractProofOp : DialectOpSem :=
  { inst := extractProofInst
    runOp := runSpec extractProofInst (.extractLane extractProofSpec) }

/-- A concrete decoded operation instantiates the corrected refinement on
    an inhabited state-local domain; the decoder premise is proved in Lean. -/
theorem extract_lane_refinement_valid_state :
    ∃ s, extractLaneDomain extractProofOp.inst extractProofSpec (ValueId.mk 1) s ∧
      runsAgree_SSAOn
        (extractLaneDomain extractProofOp.inst extractProofSpec (ValueId.mk 1))
        extractProofOp [.ExtractElement .I32 (ValueId.mk 0) (ValueId.mk 1)] := by
  refine ⟨extractProofState [.int 32 1, .int 32 2, .int 32 3, .int 32 4], ?_, ?_⟩
  · exact ⟨rfl, _, rfl, rfl⟩
  · exact runsAgree_extract_lane extractProofOp extractProofSpec (by rfl) rfl (ValueId.mk 1)

/-- The structural decoder check keeps its actual result-type refusal. -/
theorem extract_lane_result_type_mismatch_refused :
    decodeExtractLane (extractLane (.Vector 4 .I32) .Bool (ValueId.mk 0) 0) =
      .error (.typeError "vector.extract_lane result type does not match vector element type") := by
  trustIrCompilerProof {
    rfl
  } {
    trustIrReduce
  }



/-- The state-local domain is inhabited by a concrete typed vector and index,
    and both executions produce the same value and complete state. -/
theorem extract_lane_valid_state_instance :
    ∃ s, extractLaneDomain (extractProofInst) (extractProofSpec) (ValueId.mk 1) s ∧
      runExtractLane (extractProofInst) (extractProofSpec) s =
        .ok (bindFreshValue s (.int 32 1)) ∧
      Sem.run (runInsts [.ExtractElement .I32 (ValueId.mk 0) (ValueId.mk 1)]) s =
        .ok ((), bindFreshValue s (.int 32 1)) := by
  refine ⟨extractProofState [.int 32 1, .int 32 2, .int 32 3, .int 32 4], ?_⟩
  exact ⟨⟨rfl, _, rfl, rfl⟩, rfl, rfl⟩

/-- Selected poison remains a transported result on the genuine domain; no
    non-poison or all-lanes-inspected assumption is needed for extraction. -/
theorem extract_lane_poison_state_instance :
    ∃ s, extractLaneDomain (extractProofInst) (extractProofSpec) (ValueId.mk 1) s ∧
      runExtractLane (extractProofInst) (extractProofSpec) s =
        .ok (bindFreshValue s (.undef .I32)) ∧
      Sem.run (runInsts [.ExtractElement .I32 (ValueId.mk 0) (ValueId.mk 1)]) s =
        .ok ((), bindFreshValue s (.undef .I32)) := by
  trustIrCompilerProof {
    refine ⟨extractProofState [.undef .I32, .int 32 2, .int 32 3, .int 32 4], ?_⟩
    exact ⟨⟨rfl, _, rfl, rfl⟩, rfl, rfl⟩
  } {
    refine ⟨extractProofState [.undef .I32, .int 32 2, .int 32 3, .int 32 4], ?_⟩
    refine ⟨⟨rfl, _, rfl, rfl⟩, ?_, ?_⟩ <;> trustIrReduce
  }

/-- A concrete counterexample to the old constructor-only domain: a declared
    four-lane dialect extract refuses eight runtime lanes, while core Extract
    has only the lane result type and correctly extracts from that vector. -/
theorem extract_lane_wrong_census_refused :
    let s := extractProofState (List.replicate 8 (.int 32 1))
    runExtractLane (extractProofInst) (extractProofSpec) s =
      .error (.unsupported .vectorShape
        "vector.extract_lane runtime lane count does not match declared vector type") ∧
    Sem.run (runInsts [.ExtractElement .I32 (ValueId.mk 0) (ValueId.mk 1)]) s =
      .ok ((), bindFreshValue s (.int 32 1)) := ⟨rfl, rfl⟩

/-- The domain retains selected-lane type refusals instead of assuming every
    lane is well typed merely to simplify the refinement proof. -/
theorem extract_lane_wrong_lane_type_agrees :
    let s := extractProofState [.bool true, .int 32 2, .int 32 3, .int 32 4]
    extractLaneDomain (extractProofInst) (extractProofSpec) (ValueId.mk 1) s ∧
    runExtractLane (extractProofInst) (extractProofSpec) s =
      .error (.typeError "vector lane does not inhabit its declared type") ∧
    Sem.run (runInsts [.ExtractElement .I32 (ValueId.mk 0) (ValueId.mk 1)]) s =
      .error (.typeError "vector lane does not inhabit its declared type") :=
  ⟨⟨rfl, _, rfl, rfl⟩, rfl, rfl⟩

/-- Raw denotation control for an out-of-bounds static index. The producer
    decoder rejects this index; both helper executions retain the UB refusal. -/
theorem extract_lane_out_of_bounds_agrees :
    let s := extractProofState [.int 32 1, .int 32 2, .int 32 3, .int 32 4] 4
    runExtractLane (extractProofInst 4) (extractProofSpec 4) s =
      .error (.ub "ExtractElement: vector index out of bounds") ∧
    Sem.run (runInsts [.ExtractElement .I32 (ValueId.mk 0) (ValueId.mk 1)]) s =
      .error (.ub "ExtractElement: vector index out of bounds") := ⟨rfl, rfl⟩

/-!
## Refinement Lemma: vector.insert_lane
-/

/-- The insertion domain records this state's generated index, vector
    operand and bound replacement. Shared typed insertion checks retain census,
    lane-type, poison and bounds refusals without assuming successful execution. -/
def insertLaneDomain (inst : DialectInst) (spec : InsertLaneSpec)
    (idxId : ValueId) (s : MachineState) : Prop :=
  s.lookupValue idxId = some (.int 64 (Int.ofNat spec.lane)) ∧
    ∃ lanes, s.lookupValue ((trustIrVectorGet! inst.operands 0)) = some (.vector lanes) ∧
      ∃ value, s.lookupValue ((trustIrVectorGet! inst.operands 1)) = some value

/-- Insertion preserves complete outcomes on the actual state-local domain.
    The replacement and existing lanes may contain poison; their use or
    transport is decided by the shared typed insertion operation. -/
theorem runsAgree_insert_lane (op : DialectOpSem) (spec : InsertLaneSpec)
    (hDec : decodeInsertLane op.inst = .ok spec)
    (hRun : op.runOp = runSpec op.inst (.insertLane spec))
    (idxId : ValueId) :
    runsAgree_SSAOn (insertLaneDomain op.inst spec idxId) op
      [.InsertElement spec.vectorTy ((trustIrVectorGet! op.inst.operands 0)) idxId
        ((trustIrVectorGet! op.inst.operands 1))] := by
  trustIrCompilerProof {
    intro s hDomain
    obtain ⟨hIdx, lanes, hVecRaw, val, hValRaw⟩ := hDomain
    rw [hRun]
    unfold runSpec runInsertLane
    match hOps : op.inst.operands with
    | [vectorId, valId] =>
      have hg0 : (trustIrVectorGet! ([vectorId, valId] : List ValueId) 0) = vectorId := rfl
      have hg1 : (trustIrVectorGet! ([vectorId, valId] : List ValueId) 1) = valId := rfl
      have hVecS : s.lookupValue vectorId = some (.vector lanes) := by
        rw [hOps, hg0] at hVecRaw; exact hVecRaw
      have hValS : s.lookupValue valId = some val := by
        rw [hOps, hg1] at hValRaw; exact hValRaw
      have hlt : ¬ ((↑spec.lane : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg spec.lane)
      simp only [hOps, hg0, hg1, hVecS, hValS, bind, Except.bind, pure, Except.pure]
      cases hRes : setVectorElement spec.vectorTy (.vector lanes) spec.lane val with
      | error e =>
        simp only [hRes]
        simp [runInsts, stepInst, Ty.bitWidthFor, semInsertElement, semInsertElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hValS, hRes, hlt,
          Sem.getState, Sem.bindFresh, Sem.throwUB, Sem.throwTypeError, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
      | ok res =>
        simp only [hRes]
        simp [runInsts, stepInst, Ty.bitWidthFor, semInsertElement, semInsertElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hValS, hRes, hlt,
          bindFreshValue, Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, MachineState.bindValue]
        refine ⟨?_, res, ?_, res, ?_, rfl⟩
        · exact state_equiv_except_locals_refl _
        · simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]
        · simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]
    | [] =>
      exfalso
      unfold decodeInsertLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst insertLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
    | [a] =>
      exfalso
      unfold decodeInsertLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst insertLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
    | a :: b :: c :: rest =>
      exfalso
      unfold decodeInsertLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst insertLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
  } {
    intro s hDomain
    obtain ⟨hIdx, lanes, hVecRaw, val, hValRaw⟩ := hDomain
    rw [hRun]
    unfold runSpec runInsertLane
    match hOps : op.inst.operands with
    | [vectorId, valId] =>
      have hg0 : (trustIrVectorGet! ([vectorId, valId] : List ValueId) 0) = vectorId := rfl
      have hg1 : (trustIrVectorGet! ([vectorId, valId] : List ValueId) 1) = valId := rfl
      have hVecS : s.lookupValue vectorId = some (.vector lanes) := by
        rw [hOps, hg0] at hVecRaw; exact hVecRaw
      have hValS : s.lookupValue valId = some val := by
        rw [hOps, hg1] at hValRaw; exact hValRaw
      have hlt : ¬ ((↑spec.lane : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg spec.lane)
      simp only [hOps, hg0, hg1, hVecS, hValS, bind, Except.bind, pure, Except.pure]
      cases hRes : setVectorElement spec.vectorTy (.vector lanes) spec.lane val with
      | error e =>
        simp only [hRes]
        simp [runInsts, stepInst, Ty.bitWidthFor, semInsertElement, semInsertElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hValS, hRes, hlt,
          Sem.getState, Sem.bindFresh, Sem.throwUB, Sem.throwTypeError, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
      | ok res =>
        simp only [hRes]
        simp [runInsts, stepInst, Ty.bitWidthFor, semInsertElement, semInsertElementUsing, Sem.rejectPartial, Sem.lookupValue, hIdx, hVecS, hValS, hRes, hlt,
          bindFreshValue, Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind,
          Sem.run_pure, StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, MachineState.bindValue]
        refine ⟨state_equiv_except_locals_refl _, res, ?_⟩
        simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]
    | [] =>
      exfalso
      unfold decodeInsertLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst insertLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
    | [a] =>
      exfalso
      unfold decodeInsertLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst insertLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
    | a :: b :: c :: rest =>
      exfalso
      unfold decodeInsertLane at hDec
      simp only [bind, Except.bind] at hDec
      cases hch : checkHeader op.inst insertLaneOp with
      | error e => rw [hch] at hDec; simp at hDec
      | ok u => rw [hch] at hDec; simp [requireOperandCount, hOps, VectorDialect.typeError] at hDec
  }

private def insertProofInst (lane : Nat := 0) : DialectInst :=
  insertLane (.Vector 4 .I32) (ValueId.mk 0) (ValueId.mk 2) lane

private def insertProofSpec (lane : Nat := 0) : InsertLaneSpec :=
  { vectorTy := .Vector 4 .I32, elemTy := .I32, lanes := 4, lane := lane }

private def insertProofOp : DialectOpSem :=
  { inst := insertProofInst
    runOp := runSpec insertProofInst (.insertLane insertProofSpec) }

private def insertProofState (lanes : List Value) (value : Value)
    (index : Nat := 0) : MachineState :=
  { MachineState.empty with
    locals := ((ValueMap.empty.set (ValueId.mk 0) (.vector lanes)).set
      (ValueId.mk 1) (.int 64 (Int.ofNat index))).set (ValueId.mk 2) value
    nextValueId := 3 }

/-- The insertion refinement has a concrete decoded operation and an inhabited
    actual state; its decoder premise and theorem application are kernel proofs. -/
theorem insert_lane_refinement_valid_state :
    ∃ s, insertLaneDomain insertProofOp.inst insertProofSpec (ValueId.mk 1) s ∧
      runsAgree_SSAOn
        (insertLaneDomain insertProofOp.inst insertProofSpec (ValueId.mk 1))
        insertProofOp
        [.InsertElement (.Vector 4 .I32) (ValueId.mk 0) (ValueId.mk 1) (ValueId.mk 2)] := by
  refine ⟨insertProofState [.int 32 1, .int 32 2, .int 32 3, .int 32 4] (.int 32 9), ?_, ?_⟩
  · exact ⟨rfl, _, rfl, _, rfl⟩
  · exact runsAgree_insert_lane insertProofOp insertProofSpec (by rfl) rfl (ValueId.mk 1)

/-- A successful insertion leaves an unselected poison lane intact. -/
theorem insert_lane_unselected_poison_transport :
    let s := insertProofState [.int 32 1, .undef .I32, .int 32 3, .int 32 4] (.int 32 9)
    let result := .vector [.int 32 9, .undef .I32, .int 32 3, .int 32 4]
    insertLaneDomain insertProofOp.inst insertProofSpec (ValueId.mk 1) s ∧
    runInsertLane insertProofInst insertProofSpec s = .ok (bindFreshValue s result) ∧
    Sem.run (runInsts
      [.InsertElement (.Vector 4 .I32) (ValueId.mk 0) (ValueId.mk 1) (ValueId.mk 2)]) s =
      .ok ((), bindFreshValue s result) := ⟨⟨rfl, _, rfl, _, rfl⟩, rfl, rfl⟩

/-- An inserted poison value is inspected and refuses on the same domain. -/
theorem insert_lane_new_poison_refused :
    let s := insertProofState [.int 32 1, .int 32 2, .int 32 3, .int 32 4] (.undef .I32)
    insertLaneDomain insertProofOp.inst insertProofSpec (ValueId.mk 1) s ∧
    runInsertLane insertProofInst insertProofSpec s =
      .error (.ub "vector operation: use of an uninitialized lane") ∧
    Sem.run (runInsts
      [.InsertElement (.Vector 4 .I32) (ValueId.mk 0) (ValueId.mk 1) (ValueId.mk 2)]) s =
      .error (.ub "vector operation: use of an uninitialized lane") :=
  ⟨⟨rfl, _, rfl, _, rfl⟩, rfl, rfl⟩

/-- A bound replacement of the wrong lane type retains both type refusals. -/
theorem insert_lane_wrong_lane_type_refused :
    let s := insertProofState [.int 32 1, .int 32 2, .int 32 3, .int 32 4] (.bool true)
    insertLaneDomain insertProofOp.inst insertProofSpec (ValueId.mk 1) s ∧
    runInsertLane insertProofInst insertProofSpec s =
      .error (.typeError "vector lane does not inhabit its declared type") ∧
    Sem.run (runInsts
      [.InsertElement (.Vector 4 .I32) (ValueId.mk 0) (ValueId.mk 1) (ValueId.mk 2)]) s =
      .error (.typeError "vector lane does not inhabit its declared type") :=
  ⟨⟨rfl, _, rfl, _, rfl⟩, rfl, rfl⟩

/-!
## Faithful, fresh-id-threaded lowering infrastructure

The `Lowering := DialectOpSem → Except String (List Inst)` schema produces a
*fixed* instruction list with no access to the function's SSA allocator. The
production Rust pass (`crates/trust_ir/src/dialect/vector.rs`,
`VectorLoweringPass`) instead receives a `LoweringContext` with
`alloc_value()`. A faithful multi-instruction lowering therefore must thread
fresh ids: each emitted instruction binds `ValueId.mk s.nextValueId` and bumps
the counter (see `MachineState.bindValue`), so the *k*-th instruction's result
id is statically `base + k` where `base` is the runtime `nextValueId`.

We model that allocator by parameterising the lowering on `base : Nat`
(= runtime `nextValueId`) and prove agreement against the sequence seeded at
that base (`runsAgreeFrom` below). The lemmas in this section characterise the
`Sem.run` of each instruction the faithful lowering emits, in terms of the
single-fresh-bind post-state `bindOne`.
-/

/-- Post-state of one fresh SSA bind. Equals `(s.bindValue v).2`. -/
def bindOne (s : MachineState) (v : Value) : MachineState :=
  { s with
    locals := s.locals.set (ValueId.mk s.nextValueId) v,
    nextValueId := s.nextValueId + 1 }

@[simp] theorem bindOne_nextValueId (s : MachineState) (v : Value) :
    (bindOne s v).nextValueId = s.nextValueId + 1 := rfl

@[simp] theorem bindOne_memory (s : MachineState) (v : Value) :
    (bindOne s v).memory = s.memory := rfl

@[simp] theorem bindOne_permissions (s : MachineState) (v : Value) :
    (bindOne s v).permissions = s.permissions := rfl

@[simp] theorem bindOne_refCounts (s : MachineState) (v : Value) :
    (bindOne s v).refCounts = s.refCounts := rfl

/-- The freshly bound id holds the bound value. -/
@[simp] theorem lookup_bindOne_self (s : MachineState) (v : Value) :
    (bindOne s v).lookupValue (ValueId.mk s.nextValueId) = some v := by
  simp [bindOne, MachineState.lookupValue, ValueMap.set, ValueMap.get]

/-- Earlier (distinct) bindings survive a fresh bind. -/
theorem lookup_bindOne_ne (s : MachineState) (v : Value) (id : ValueId)
    (h : id.index ≠ s.nextValueId) :
    (bindOne s v).lookupValue id = s.lookupValue id := by
  have hne : ¬ (id == ValueId.mk s.nextValueId) = true := by
    simp only [beq_iff_eq]
    intro heq; exact h (by rw [heq])
  simp [bindOne, MachineState.lookupValue, ValueMap.set, ValueMap.get, hne]

/-- `Sem.run` of a single fresh bind. -/
theorem run_bindFresh (v : Value) (s : MachineState) :
    Sem.run (Sem.bindFresh v) s
      = .ok (ValueId.mk s.nextValueId, bindOne s v) := by
  simp [Sem.bindFresh, Sem.run, Sem.getState, Sem.setState, StateT.run,
        StateT.get, StateT.set, StateT.bind, StateT.pure, bind, pure,
        Except.bind, Except.pure, MachineState.bindValue, bindOne]

/-- Sequencing: a non-terminator step advances `runInsts` to the tail. -/
theorem runInsts_cons_value (i : Inst) (rest : List Inst)
    (s s' : MachineState) (ovid : Option ValueId)
    (h : Sem.run (stepInst i) s = .ok (.value ovid, s')) :
    Sem.run (runInsts (i :: rest)) s = Sem.run (runInsts rest) s' := by
  simp only [runInsts, Sem.run_bind, h, Except.bind]

set_option smartUnfolding false in
/-- `Sem.run` of an integer `Const`: it binds the literal's residue at the
    declared width (`Value.intAt`, the model's one integer representation).
    Pointer-typed constants use their checked null-only representation. -/
theorem run_stepConstIntAt (ty : Ty) (i : Int) (w : Nat) (s : MachineState)
    (hw : ty.bitWidth = some w) (hInteger : ty.isInteger = true) :
    Sem.run (stepInst (.Const ty (.int i))) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (Value.intAt w i)) := by
  trustIrCompilerProof {
    have hNeg : ¬ ((Constant.int i).hasSymbolAddr = true) := by
      simp [Constant.hasSymbolAddr]
    have hA : ¬ (constWidthAmbiguous ty (.int i) = true) := by
      simp [constWidthAmbiguous, constHasInexactFloat]
    have hForm : constPointerFormsSupported ty (.int i) = true := by
      cases ty <;> simp_all [constPointerFormsSupported, Ty.isInteger]
    have hValue : constValueAt ty (.int i) = Value.intAt w i := by
      cases ty <;> simp_all [constValueAt, Ty.bitWidthFor, Ty.isInteger]
    have hChecked : constValueAtChecked ty (.int i) = .ok (Value.intAt w i) := by
      rw [constValueAtChecked_eq]
      cases ty <;> simp_all [Ty.isInteger, exceptSem_pure, exceptSem_ok_bind]
    simp only [stepInst, if_neg hNeg, hChecked, pure_bind]
    rw [Sem.run_bind, run_bindFresh]
    rfl
  } {
    have hNeg : ¬ ((Constant.int i).hasSymbolAddr = true) := by
      simp [Constant.hasSymbolAddr]
    have hA : ¬ (constWidthAmbiguous ty (.int i) = true) := by
      cases ty <;> simp_all [Ty.isInteger, constWidthAmbiguous, constHasInexactFloat]
    have hForm : constPointerFormsSupported ty (.int i) = true := by
      cases ty <;> simp_all [constPointerFormsSupported, Ty.isInteger]
    have hValue : constValueAt ty (.int i) = Value.intAt w i := by
      cases ty <;> simp_all [constValueAt, Ty.bitWidthFor, Ty.isInteger]
    have hChecked : constValueAtChecked ty (.int i) = .ok (Value.intAt w i) := by
      rw [constValueAtChecked_eq]
      cases ty <;> simp_all [Ty.isInteger, exceptSem_pure, exceptSem_ok_bind]
    simp only [stepInst, if_neg hNeg, hChecked, pure_bind]
    rw [Sem.run_bind, run_bindFresh]
    rfl
  }

/-- `Sem.run` of an integer `Const` whose literal is already a residue at the
    declared width (`0 ≤ i < 2^w`, every lane index and seed a lowering
    emits): it binds the literal itself. -/
theorem run_stepConstInt (ty : Ty) (i : Int) (w : Nat) (s : MachineState)
    (hw : ty.bitWidth = some w) (hInteger : ty.isInteger = true) (h0 : 0 ≤ i) (h1 : i < 2 ^ w) :
    Sem.run (stepInst (.Const ty (.int i))) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w i)) := by
  have h := run_stepConstIntAt ty i w s hw hInteger
  rwa [show Value.intAt w i = .int w i by
    simp only [Value.intAt, truncateUnsigned_of_residue h0 h1]] at h

private theorem i64_is_integer : Ty.I64.isInteger = true := rfl

/-- An index read off a list it is in bounds of. -/
theorem lt_length_of_get?_some {α : Type} {l : List α} {n : Nat} {a : α}
    (h : (trustIrListGet? l n) = some a) : n < l.length := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ k =>
      simp only [trustIrListGetConsSucc] at h
      simp only [List.length_cons]
      have := ih h
      omega

/-- Every integer lane type of the executable subset has at most 16 lanes. -/
theorem executableIntLane?_lanes_le {elemTy : Ty} {n w : Nat}
    (h : elemTy.executableIntLane? = some (n, w)) : n ≤ 16 := by
  cases elemTy <;> simp [Ty.executableIntLane?] at h <;> omega

/-- Every executable integer vector shape has at most 16 lanes. -/
theorem executableIntVectorWidth?_lanes_le {ty : Ty} {n w : Nat}
    (h : ty.executableIntVectorWidth? = some (n, w)) : n ≤ 16 := by
  unfold Ty.executableIntVectorWidth? at h
  split at h
  · split at h
    · rename_i lanes width hlane
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact executableIntLane?_lanes_le hlane
      · simp at h
    · simp at h
  · simp at h

/-- Every executable bool-vector shape has at most 16 lanes. -/
theorem executableBoolVectorLanes?_le {ty : Ty} {n : Nat}
    (h : ty.executableBoolVectorLanes? = some n) : n ≤ 16 := by
  unfold Ty.executableBoolVectorLanes? at h
  split at h <;> simp at h <;> omega

/-- Every executable vector payload has at most 16 lanes. -/
theorem executableVectorPayloadMatches_length_le {ty : Ty} {lanes : List Value}
    (h : ty.executableVectorPayloadMatches lanes = true) : lanes.length ≤ 16 := by
  unfold Ty.executableVectorPayloadMatches at h
  split at h
  · rename_i n w hw
    have := executableIntVectorWidth?_lanes_le hw
    simp at h
    omega
  · split at h
    · rename_i n hb
      have := executableBoolVectorLanes?_le hb
      simp at h
      omega
    · simp at h

/-- Every executable lane payload has at most 16 lanes. -/
theorem executableVectorLanePayloadMatches_length_le {elemTy : Ty} {lanes : List Value}
    (h : Ty.executableVectorLanePayloadMatches elemTy lanes = true) : lanes.length ≤ 16 := by
  unfold Ty.executableVectorLanePayloadMatches at h
  split at h
  · rename_i n w hw
    have := executableIntLane?_lanes_le hw
    simp at h
    omega
  · split at h <;> simp at h <;> omega

/-- A lane index of an executable vector is an `i64` residue. -/
theorem lane_index_lt_two_pow_64 {j : Nat} (h : j < 17) : (Int.ofNat j) < 2 ^ 64 := by
  show ((j : Int)) < 2 ^ 64
  omega

/-- `Sem.run` of an `InsertElement` writing lane `k` of a vector operand. -/
theorem run_stepInsertElementVec (n : Nat) (elemTy : Ty)
    (arrId idxId valId : ValueId) (s : MachineState)
    (lanes : List Value) (k : Nat) (newVal : Value)
    (harr : s.lookupValue arrId = some (.vector lanes))
    (hidx : s.lookupValue idxId = some (.int 64 (Int.ofNat k)))
    (hval : s.lookupValue valId = some newVal)
    (hpay : (Ty.Vector n elemTy).executableVectorPayloadMatches lanes = true)
    (hlane : elemTy.executableVectorLaneValueMatches newVal = true)
    (hk : k < lanes.length) :
    Sem.run (stepInst (.InsertElement (.Vector n elemTy) arrId idxId valId)) s
      = .ok (.value (some (ValueId.mk s.nextValueId)),
             bindOne s (.vector (lanes.set k newVal))) := by
  have hlt : ¬ ((↑k : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg k)
  have hRes : setVectorElement (.Vector n elemTy) (.vector lanes) k newVal
      = .ok (.vector (lanes.set k newVal)) := by
    exact setVectorElement_of_executablePayload hpay hlane hk
  simp [stepInst, Ty.bitWidthFor, semInsertElement, semInsertElementUsing, Sem.rejectPartial, Sem.lookupValue, harr, hidx, hval, hlt, hRes,
        Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
        StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
        bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]

set_option smartUnfolding false in
/-- `Sem.run` of a vector integer `Const`. The Const arm refines int lanes to
    the declared element width `w`. `hns`: no lane holds a link-time
    `symbolAddr` (which the step refuses, WS2.18). -/
theorem run_stepConstVec (n : Nat) (elemTy : Ty) (w : Nat) (cs : List Constant)
    (s : MachineState) (hw : elemTy.bitWidth = some w)
    (hNonzero : n ≠ 0) (hCount : cs.length = n)
    (hScalar : (vectorScalarByteSize elemTy).isSome = true)
    (hTyped : ∀ c ∈ cs, ConstInlineAdmitted false elemTy c)
    (hns : Constant.listHasSymbolAddr cs = false) :
    Sem.run (stepInst (.Const (.Vector n elemTy) (.vector cs))) s
      = .ok (.value (some (ValueId.mk s.nextValueId)),
             bindOne s (.vector (cs.map (fun c => match c with
               | .int i => Value.intAt w i
                | other => constValueAt elemTy other)))) := by
  trustIrCompilerProof {
    have hNeg : ¬ ((Constant.vector cs).hasSymbolAddr = true) := by
      simp [Constant.hasSymbolAddr, hns]
    have hLanesAll : ∀ lanes, (∀ c ∈ lanes, ConstInlineAdmitted false elemTy c) →
        ConstLanesAdmitted elemTy lanes := by
      intro lanes
      induction lanes with
      | nil => intro _; exact .nil
      | cons c cs ih =>
        intro h
        exact .cons (h c ((trustIrListMemConsSelf _ _))) (ih (fun d hd => h d (List.mem_cons_of_mem _ hd)))
    have hValueAll : ∀ lanes, constLanesAt elemTy lanes = lanes.map (fun c => match c with
        | .int i => Value.intAt w i
        | other => constValueAt elemTy other) := by
      intro lanes
      induction lanes with
      | nil => simp [constLanesAt]
      | cons c cs ih =>
        simp only [constLanesAt, List.map_cons, ih]
        congr 1
        cases c <;> try rfl
        cases elemTy <;> simp_all [vectorScalarByteSize, constValueAt, Ty.bitWidthFor]
    have hValue := hValueAll cs
    have hChecked : constValueAtChecked (.Vector n elemTy) (.vector cs) =
        .ok (.vector (cs.map (fun c => match c with
          | .int i => Value.intAt w i
          | other => constValueAt elemTy other))) := by
      have hAdmitted : ConstInlineAdmitted true (.Vector n elemTy) (.vector cs) :=
        .vector hNonzero hCount hScalar (hLanesAll cs hTyped)
      have h := hAdmitted.checked .le64
      simpa only [constValueAt, hValue] using h
    simp only [stepInst, if_neg hNeg, hChecked, pure_bind]
    rw [Sem.run_bind, run_bindFresh]
    rfl
  } {
    have hNeg : ¬ ((Constant.vector cs).hasSymbolAddr = true) := by
      change ¬ (Constant.listHasSymbolAddr cs = true)
      simp [hns]
    have hLanesAll : ∀ lanes, (∀ c ∈ lanes, ConstInlineAdmitted false elemTy c) →
        ConstLanesAdmitted elemTy lanes := by
      intro lanes
      induction lanes with
      | nil => intro _; exact .nil
      | cons c cs ih =>
        intro h
        exact .cons (h c ((trustIrListMemConsSelf _ _))) (ih (fun d hd => h d (List.mem_cons_of_mem _ hd)))
    have hValueAll : ∀ lanes, constLanesAt elemTy lanes = lanes.map (fun c => match c with
        | .int i => Value.intAt w i
        | other => constValueAt elemTy other) := by
      intro lanes
      induction lanes with
      | nil => simp [constLanesAt]
      | cons c cs ih =>
        simp only [constLanesAt, List.map_cons, ih]
        congr 1
        cases c <;> try rfl
        cases elemTy <;> simp_all [vectorScalarByteSize, constValueAt, Ty.bitWidthFor]
    have hValue := hValueAll cs
    have hChecked : constValueAtChecked (.Vector n elemTy) (.vector cs) =
        .ok (.vector (cs.map (fun c => match c with
          | .int i => Value.intAt w i
          | other => constValueAt elemTy other))) := by
      have hAdmitted : ConstInlineAdmitted true (.Vector n elemTy) (.vector cs) :=
        .vector hNonzero hCount hScalar (hLanesAll cs hTyped)
      have h := hAdmitted.checked .le64
      simpa only [constValueAt, hValue] using h
    simp only [stepInst, if_neg hNeg, hChecked, pure_bind]
    rw [Sem.run_bind, run_bindFresh]
    rfl
  }

private theorem executable_bool_shape (n count : Nat)
    (h : (Ty.Vector n .Bool).executableBoolVectorLanes? = some count) :
    count = n ∧ n ≠ 0 := by
  unfold Ty.executableBoolVectorLanes? at h
  split at h <;> simp_all <;> omega

/-- Executable vector payloads establish the real lane count and admitted
    scalar kind, rather than only the total bit width. -/
private theorem executable_payload_shape (n : Nat) (elemTy : Ty) (lanes : List Value)
    (h : (Ty.Vector n elemTy).executableVectorPayloadMatches lanes = true) :
    lanes.length = n ∧ n ≠ 0 ∧ (vectorScalarByteSize elemTy).isSome = true := by
  cases elemTy <;>
    simp [Ty.executableVectorPayloadMatches, Ty.executableIntVectorWidth?,
      Ty.executableIntLane?, Ty.executableBoolVectorLanes?, vectorScalarByteSize] at h ⊢
  all_goals repeat' split at h
  all_goals try (simp_all <;> omega)
  rename_i count hClassifier
  have hShape := executable_bool_shape n count hClassifier
  simp_all

/-- A typed seed lane supplies constructor/type admission. The runtime lane
    check rules out untyped fallback carriers such as FnDef, Bytes or U128 at
    a narrower integer lane type. -/
private theorem seed_admitted_of_lane (elemTy : Ty) (w : Nat) (c : Constant)
    (h : elemTy.executableVectorLaneValueMatches
      (match c with | .int i => Value.intAt w i | other => constValueAt elemTy other) = true) :
    ConstInlineAdmitted false elemTy c := by
  cases elemTy <;> first
    | (simp [Ty.executableVectorLaneValueMatches, Ty.executableIntLane?] at h; done)
    | (cases c <;> first
        | exact .integer rfl
        | exact .boolean
        | simp [constValueAt, Value.ofConstant, Ty.executableVectorLaneValueMatches,
            Ty.executableIntLane?, Value.isIntWidth, Value.isBool, Value.intAt] at h)

/-- A list of constants none of which holds a link-time address. -/
theorem listHasSymbolAddr_eq_false_of_forall (cs : List Constant)
    (h : ∀ c ∈ cs, c.hasSymbolAddr = false) : Constant.listHasSymbolAddr cs = false := by
  induction cs with
  | nil => simp [Constant.listHasSymbolAddr]
  | cons c rest ih =>
    simp only [Constant.listHasSymbolAddr]
    rw [h c (trustIrListMemConsSelf c rest),
        ih (fun d hd => h d (List.mem_cons_of_mem c hd))]
    rfl

/-- The zero seed `[int i, .., int i]` holds no link-time address. -/
theorem listHasSymbolAddr_replicate_int (m : Nat) (i : Int) :
    Constant.listHasSymbolAddr (List.replicate m (.int i)) = false := by
  induction m with
  | zero => simp [Constant.listHasSymbolAddr]
  | succ k ih =>
    simp [List.replicate, Constant.listHasSymbolAddr, Constant.hasSymbolAddr, ih]

private theorem mem_replicate_constant_eq {count : Nat} {c value : Constant}
    (h : c ∈ List.replicate count value) : c = value := by
  induction count with
  | zero => simp [List.replicate] at h
  | succ count ih =>
    simp only [List.replicate, List.mem_cons] at h
    exact h.elim id ih

/-- A seed constant whose lowered lane passes the executable lane check holds
    no link-time address: that check admits only int / bool scalars, and a
    `symbolAddr` (or any composite holding one) lowers to neither. -/
theorem seed_noSym_of_lane (elemTy : Ty) (w : Nat) (c : Constant)
    (h : elemTy.executableVectorLaneValueMatches
          (match c with | .int i => Value.intAt w i | other => constValueAt elemTy other) = true) :
    c.hasSymbolAddr = false := by
  cases c <;>
    first
    | (simp [Constant.hasSymbolAddr]; done)
    | (exfalso
       cases elemTy <;>
         simp [constValueAt, Value.ofConstant, Ty.executableVectorLaneValueMatches,
               Ty.executableIntLane?, Value.isIntWidth, Value.isBool] at h)

/-- Earlier bindings (ids strictly below a dominating `base`) survive a fresh
    bind whenever `base` does not exceed the current allocator counter. This is
    the SSA-dominance preservation used to thread operands through the
    fresh-id-allocating lowering chain. -/
theorem lookup_bindOne_below (s : MachineState) (v : Value) (id : ValueId)
    (base : Nat) (hid : id.index < base) (hb : base ≤ s.nextValueId) :
    (bindOne s v).lookupValue id = s.lookupValue id :=
  lookup_bindOne_ne s v id (by omega)

/-- Setting a lane to a value that satisfies the lane predicate preserves an
    `all`-style payload check. -/
theorem all_set_of_all {P : Value → Bool} :
    ∀ {lanes : List Value} {j : Nat} {w : Value},
    lanes.all P = true → P w = true → (lanes.set j w).all P = true := by
  intro lanes
  induction lanes with
  | nil => intro j w _ _; simp
  | cons a t ih =>
    intro j w hall hw
    cases j with
    | zero =>
      simp only [List.set, List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨hw, hall.2⟩
    | succ k =>
      simp only [List.set, List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨hall.1, ih hall.2 hw⟩

/-- Taking `j+1` of a list whose lane `j` was just set splits as the
    untouched prefix plus the new value. The key rewrite that turns the insert
    chain's running vector into `prefix ++ remaining`. -/
theorem take_succ_set : ∀ (lanes : List Value) (j : Nat) (w : Value),
    j < lanes.length → (lanes.set j w).take (j + 1) = lanes.take j ++ [w] := by
  intro lanes
  induction lanes with
  | nil => intro j w hj; exact absurd hj (Nat.not_lt_zero j)
  | cons a t ih =>
    intro j w hj
    cases j with
    | zero => simp [List.set, List.take]
    | succ k =>
      have hk : k < t.length := by
        simp only [List.length_cons] at hj; omega
      simp only [List.set, List.take, List.cons_append]
      rw [ih k w hk]

/-- Cons-decomposition for the dialect operand resolver: a successful
    `lookupOperands` on a non-empty list splits into the head value and a
    successful resolve of the tail. -/
theorem lookupOperands_cons {o : ValueId} {rest : List ValueId}
    {state : MachineState} {vals : List Value}
    (h : lookupOperands (o :: rest) state = .ok vals) :
    ∃ vo vrest, vals = vo :: vrest ∧ state.lookupValue o = some vo ∧
                lookupOperands rest state = .ok vrest := by
  unfold lookupOperands at h
  cases hl : state.lookupValue o with
  | none => rw [hl] at h; simp [typeError] at h
  | some vo =>
    rw [hl] at h
    simp only [bind, Except.bind] at h
    cases hr : lookupOperands rest state with
    | error e => rw [hr] at h; simp at h
    | ok vrest =>
      rw [hr] at h
      simp only [Except.bind] at h
      exact ⟨vo, vrest, by injection h with h'; exact h'.symm, rfl, rfl⟩

/-!
## Faithful base-threaded lowering for `vector.pack_lanes`

`packInsertsFrom` is the SSA-allocator-threaded refinement of the production
Rust pass: starting from a freshly-built zero vector at `ValueId.mk base`, it
emits, for each lane operand, a `Const` of the lane index followed by an
`InsertElement` that writes that operand into the running vector. The *k*-th
operand's `InsertElement` reads the previous vector at `base + 2*k`, its index
constant at `base + 1 + 2*k`, and binds the updated vector at `base + 2 + 2*k`
— exactly the ids `MachineState.bindValue` hands out when execution starts with
`nextValueId = base`. -/
def packInsertsFrom (vt : Ty) (operands : List ValueId) (base j : Nat) : List Inst :=
  match operands with
  | [] => []
  | o :: rest =>
    Inst.Const .I64 (.int (Int.ofNat j)) ::
    Inst.InsertElement vt (ValueId.mk (base + 2 * j)) (ValueId.mk (base + 1 + 2 * j)) o ::
    packInsertsFrom vt rest base (j + 1)

/-- The full pack lowering: build a zero seed vector, then chain the lane
    inserts. `zeros` is the seed constant payload (all-zero lanes). -/
def lowerPackLanesFrom (vt : Ty) (zeros : List Constant)
    (operands : List ValueId) (base : Nat) : List Inst :=
  Inst.Const vt (.vector zeros) :: packInsertsFrom vt operands base 0

/-- Fold a list of lane values into `lanes` starting at index `j`. Used to
    describe the running vector contents through the insert chain. For a full
    overwrite (`j = 0`, `vals.length = lanes.length`) this reduces by
    computation to `vals`. -/
def setSeq : List Value → Nat → List Value → List Value
  | lanes, _, [] => lanes
  | lanes, j, w :: rest => setSeq (lanes.set j w) (j + 1) rest

/-- Base-threaded analogue of `runsAgree_SSA`: the lowering is a *function* of
    the runtime allocator counter (`s.nextValueId`), faithfully modelling the
    Rust pass's `ctx.alloc_value()`. Agreement is required only in SSA-dominated
    states (every operand id below the allocator counter), which is the standing
    invariant at any well-formed program point. -/
def runsAgreeFrom (op : DialectOpSem) (operands : List ValueId)
    (lower : Nat → List Inst) : Prop :=
  ∀ (s : MachineState),
    (∀ o ∈ operands, o.index < s.nextValueId) →
    match op.runOp s with
    | .ok s1 => ∃ r s2, Sem.run (runInsts (lower s.nextValueId)) s = .ok (r, s2) ∧
                state_equiv_except_locals s1 s2 ∧
                ∃ v1 v2, s1.lookupValue (ValueId.mk (s1.nextValueId - 1)) = some v1 ∧
                         s2.lookupValue (ValueId.mk (s2.nextValueId - 1)) = some v2 ∧
                         v1 = v2
    | .error e => Sem.run (runInsts (lower s.nextValueId)) s = .error e

/-- **Faithful refinement of `vector.pack_lanes` (induction core).** Running the
    base-threaded insert chain from a state whose allocator counter is exactly
    `base + 1 + 2*j`, with the running vector for the already-written prefix
    bound at `ValueId.mk (base + 2*j)`, reproduces the dialect outcome: the chain
    terminates, leaves memory/permissions/refcounts untouched, and binds the
    fully-populated vector `curLanes.take j ++ vals` at the final fresh id. The
    `P`/`lenN` characterisation hypotheses pin the bounded executable lane type;
    they hold by `rfl` at `<4 x i32>` and `<2 x i64>`. This is the genuine
    multi-lane generalisation of the single-lane `run_stepInsertElementVec`. -/
theorem run_packInsertsFrom (n lenN base : Nat) (elemTy : Ty) (P : Value → Bool)
    (s0 : MachineState)
    (hchar : ∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
               = (decide (ls.length = lenN) && ls.all P))
    (hlaneP : ∀ v : Value, elemTy.executableVectorLaneValueMatches v = P v) :
    ∀ (operands : List ValueId) (vals : List Value) (s : MachineState)
      (j : Nat) (curLanes : List Value),
      lookupOperands operands s0 = .ok vals →
      (∀ id : ValueId, id.index < base → s.lookupValue id = s0.lookupValue id) →
      (∀ o ∈ operands, o.index < base) →
      (∀ v ∈ vals, P v = true) →
      s.nextValueId = base + 1 + 2 * j →
      s.lookupValue (ValueId.mk (base + 2 * j)) = some (.vector curLanes) →
      (Ty.Vector n elemTy).executableVectorPayloadMatches curLanes = true →
      j + vals.length = curLanes.length →
      ∃ s2 : MachineState,
        Sem.run (runInsts (packInsertsFrom (Ty.Vector n elemTy) operands base j)) s
          = .ok ((), s2) ∧
        s2.nextValueId = base + 1 + 2 * (j + operands.length) ∧
        s2.memory = s.memory ∧ s2.permissions = s.permissions ∧
        s2.refCounts = s.refCounts ∧
        s2.lookupValue (ValueId.mk (base + 2 * (j + operands.length)))
          = some (.vector (curLanes.take j ++ vals)) := by
  trustIrCompilerProof {
    intro operands
    induction operands with
    | nil =>
      intro vals s j curLanes hlook _ _ _ hnext hcur _ hsum
      simp only [lookupOperands, Except.ok.injEq] at hlook
      subst hlook
      have hj : j = curLanes.length := by simpa using hsum
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [packInsertsFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · have hjlen : curLanes.take j = curLanes := by rw [hj]; exact List.take_length curLanes
        simp only [List.length_nil, Nat.add_zero, List.append_nil, hjlen]
        exact hcur
    | cons o rest ih =>
      intro vals s j curLanes hlook hpres hdom hvalsP hnext hcur hpay hsum
      obtain ⟨vo, vrest, rfl, ho0, hrest⟩ := lookupOperands_cons hlook
      have hlen : curLanes.length = lenN := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h; exact of_decide_eq_true h.1
      have hallP : curLanes.all P = true := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h; exact h.2
      have hPvo : P vo = true := hvalsP vo (trustIrListMemConsSelf vo vrest)
      have hsum' : j + (vrest.length + 1) = curLanes.length := by
        simpa [List.length_cons] using hsum
      have hk : j < curLanes.length := by omega
      have hunfold : packInsertsFrom (Ty.Vector n elemTy) (o :: rest) base j
          = Inst.Const Ty.I64 (.int (Int.ofNat j))
            :: Inst.InsertElement (Ty.Vector n elemTy)
                 (ValueId.mk (base + 2 * j)) (ValueId.mk (base + 1 + 2 * j)) o
            :: packInsertsFrom (Ty.Vector n elemTy) rest base (j + 1) := rfl
      rw [hunfold]
      have hConst : Sem.run (stepInst (.Const Ty.I64 (.int (Int.ofNat j)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat j))) :=
        run_stepConstInt Ty.I64 (Int.ofNat j) 64 s rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 (by
            have := executableVectorPayloadMatches_length_le hpay; omega))
      rw [runInsts_cons_value _ _ _ _ _ hConst]
      have harr : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 2 * j))
          = some (.vector curLanes) := by
        rw [lookup_bindOne_ne s (.int 64 (Int.ofNat j)) (ValueId.mk (base + 2 * j))
             (by show base + 2 * j ≠ s.nextValueId; rw [hnext]; omega)]
        exact hcur
      have hidx : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 1 + 2 * j))
          = some (.int 64 (Int.ofNat j)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat j)); rwa [hnext] at h
      have hvalLk : (bindOne s (.int 64 (Int.ofNat j))).lookupValue o = some vo := by
        have hob : o.index < base := hdom o (trustIrListMemConsSelf o rest)
        rw [lookup_bindOne_ne s (.int 64 (Int.ofNat j)) o (by rw [hnext]; omega), hpres o hob]
        exact ho0
      have hlaneVo : elemTy.executableVectorLaneValueMatches vo = true := by
        rw [hlaneP]; exact hPvo
      have hInsert := run_stepInsertElementVec n elemTy (ValueId.mk (base + 2 * j))
        (ValueId.mk (base + 1 + 2 * j)) o (bindOne s (.int 64 (Int.ofNat j)))
        curLanes j vo harr hidx hvalLk hpay hlaneVo hk
      rw [runInsts_cons_value _ _ _ _ _ hInsert]
      have hpres' : ∀ id : ValueId, id.index < base →
          (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))).lookupValue id
            = s0.lookupValue id := by
        intro id hid
        have h1 := lookup_bindOne_below (bindOne s (.int 64 (Int.ofNat j)))
          (.vector (curLanes.set j vo)) id base hid
          (by simp only [bindOne_nextValueId, hnext]; omega)
        have h2 := lookup_bindOne_below s (.int 64 (Int.ofNat j)) id base hid
          (by rw [hnext]; omega)
        rw [h1, h2]; exact hpres id hid
      have hdom' : ∀ o' ∈ rest, o'.index < base := fun o' ho' => hdom o' (List.mem_cons_of_mem o ho')
      have hvalsP' : ∀ v ∈ vrest, P v = true := fun v hv => hvalsP v (List.mem_cons_of_mem vo hv)
      have hnext' : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))).nextValueId
          = base + 1 + 2 * (j + 1) := by simp only [bindOne_nextValueId, hnext]; omega
      have hcur' : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))).lookupValue
          (ValueId.mk (base + 2 * (j + 1))) = some (.vector (curLanes.set j vo)) := by
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))
        have heq : (bindOne s (.int 64 (Int.ofNat j))).nextValueId = base + 2 * (j + 1) := by
          simp only [bindOne_nextValueId, hnext]; omega
        rwa [heq] at h
      have hpay' : (Ty.Vector n elemTy).executableVectorPayloadMatches (curLanes.set j vo) = true := by
        rw [hchar, Bool.and_eq_true]
        refine ⟨?_, all_set_of_all hallP hPvo⟩
        simp [List.length_set, hlen]
      have hsum'' : (j + 1) + vrest.length = (curLanes.set j vo).length := by
        rw [List.length_set]; omega
      obtain ⟨s2, hrun2, hnext2, hmem2, hperm2, href2, hvec2⟩ :=
        ih vrest (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo)))
          (j + 1) (curLanes.set j vo) hrest hpres' hdom' hvalsP' hnext' hcur' hpay' hsum''
      refine ⟨s2, hrun2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext2]; simp only [List.length_cons]; omega
      · rw [hmem2]; simp
      · rw [hperm2]; simp
      · rw [href2]; simp
      · have hidxeq : j + (o :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq, hvec2, take_succ_set curLanes j vo hk, List.append_assoc, List.singleton_append]
  } {
    intro operands
    induction operands with
    | nil =>
      intro vals s j curLanes hlook _ _ _ hnext hcur _ hsum
      simp only [lookupOperands, Except.ok.injEq] at hlook
      subst hlook
      have hj : j = curLanes.length := by simpa using hsum
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [packInsertsFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · have hjlen : curLanes.take j = curLanes := by rw [hj]; exact (List.take_length (l := curLanes))
        simp only [List.length_nil, Nat.add_zero, List.append_nil, hjlen]
        exact hcur
    | cons o rest ih =>
      intro vals s j curLanes hlook hpres hdom hvalsP hnext hcur hpay hsum
      obtain ⟨vo, vrest, rfl, ho0, hrest⟩ := lookupOperands_cons hlook
      have hlen : curLanes.length = lenN := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h; exact of_decide_eq_true h.1
      have hallP : curLanes.all P = true := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h; exact h.2
      have hPvo : P vo = true := hvalsP vo (trustIrListMemConsSelf vo vrest)
      have hsum' : j + (vrest.length + 1) = curLanes.length := by
        simpa [List.length_cons] using hsum
      have hk : j < curLanes.length := by omega
      have hunfold : packInsertsFrom (Ty.Vector n elemTy) (o :: rest) base j
          = Inst.Const Ty.I64 (.int (Int.ofNat j))
            :: Inst.InsertElement (Ty.Vector n elemTy)
                 (ValueId.mk (base + 2 * j)) (ValueId.mk (base + 1 + 2 * j)) o
            :: packInsertsFrom (Ty.Vector n elemTy) rest base (j + 1) := rfl
      rw [hunfold]
      have hConst : Sem.run (stepInst (.Const Ty.I64 (.int (Int.ofNat j)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat j))) :=
        run_stepConstInt Ty.I64 (Int.ofNat j) 64 s rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 (by
            have := executableVectorPayloadMatches_length_le hpay; omega))
      rw [runInsts_cons_value _ _ _ _ _ hConst]
      have harr : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 2 * j))
          = some (.vector curLanes) := by
        rw [lookup_bindOne_ne s (.int 64 (Int.ofNat j)) (ValueId.mk (base + 2 * j))
             (by show base + 2 * j ≠ s.nextValueId; rw [hnext]; omega)]
        exact hcur
      have hidx : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 1 + 2 * j))
          = some (.int 64 (Int.ofNat j)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat j)); rwa [hnext] at h
      have hvalLk : (bindOne s (.int 64 (Int.ofNat j))).lookupValue o = some vo := by
        have hob : o.index < base := hdom o (trustIrListMemConsSelf o rest)
        rw [lookup_bindOne_ne s (.int 64 (Int.ofNat j)) o (by rw [hnext]; omega), hpres o hob]
        exact ho0
      have hlaneVo : elemTy.executableVectorLaneValueMatches vo = true := by
        rw [hlaneP]; exact hPvo
      have hInsert := run_stepInsertElementVec n elemTy (ValueId.mk (base + 2 * j))
        (ValueId.mk (base + 1 + 2 * j)) o (bindOne s (.int 64 (Int.ofNat j)))
        curLanes j vo harr hidx hvalLk hpay hlaneVo hk
      rw [runInsts_cons_value _ _ _ _ _ hInsert]
      have hpres' : ∀ id : ValueId, id.index < base →
          (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))).lookupValue id
            = s0.lookupValue id := by
        intro id hid
        have h1 := lookup_bindOne_below (bindOne s (.int 64 (Int.ofNat j)))
          (.vector (curLanes.set j vo)) id base hid
          (by simp only [bindOne_nextValueId, hnext]; omega)
        have h2 := lookup_bindOne_below s (.int 64 (Int.ofNat j)) id base hid
          (by rw [hnext]; omega)
        rw [h1, h2]; exact hpres id hid
      have hdom' : ∀ o' ∈ rest, o'.index < base := fun o' ho' => hdom o' (List.mem_cons_of_mem o ho')
      have hvalsP' : ∀ v ∈ vrest, P v = true := fun v hv => hvalsP v (List.mem_cons_of_mem vo hv)
      have hnext' : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))).nextValueId
          = base + 1 + 2 * (j + 1) := by simp only [bindOne_nextValueId, hnext]; omega
      have hcur' : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))).lookupValue
          (ValueId.mk (base + 2 * (j + 1))) = some (.vector (curLanes.set j vo)) := by
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo))
        have heq : (bindOne s (.int 64 (Int.ofNat j))).nextValueId = base + 2 * (j + 1) := by
          simp only [bindOne_nextValueId, hnext]; omega
        rwa [heq] at h
      have hpay' : (Ty.Vector n elemTy).executableVectorPayloadMatches (curLanes.set j vo) = true := by
        rw [hchar, Bool.and_eq_true]
        refine ⟨?_, all_set_of_all hallP hPvo⟩
        simp [List.length_set, hlen]
      have hsum'' : (j + 1) + vrest.length = (curLanes.set j vo).length := by
        rw [List.length_set]; omega
      obtain ⟨s2, hrun2, hnext2, hmem2, hperm2, href2, hvec2⟩ :=
        ih vrest (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.vector (curLanes.set j vo)))
          (j + 1) (curLanes.set j vo) hrest hpres' hdom' hvalsP' hnext' hcur' hpay' hsum''
      refine ⟨s2, hrun2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext2]; simp only [List.length_cons]; omega
      · rw [hmem2]; simp
      · rw [hperm2]; simp
      · rw [href2]; simp
      · have hidxeq : j + (o :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq, hvec2, take_succ_set curLanes j vo hk, List.append_assoc, List.singleton_append]
  }

/-!
## Refinement Lemma: vector.pack_lanes

Discharged with a genuine proof (no axiom or proof placeholder):
`runsAgreeFrom_pack_lanes` establishes dialect/lowering agreement against
the faithful, fresh-id-threaded `lowerPackLanesFrom` (a zero-seed `Const`
followed by the SSA-faithful `InsertElement` chain), using the multi-lane
induction core `run_packInsertsFrom`. The former placeholder
`vectorLower.lowerPackLanes` (hardcoded `ValueId.mk 0` base) could not
satisfy the statement — the seed/chain rewrite is what makes it true. The
`hchar`/`hlaneP`/seed hypotheses pin the bounded executable lane type and
hold by `rfl`/`decide` at the supported shapes (`<4 x i32>`, `<2 x i64>`;
see the corollaries below); `hdom` is the well-typed-operands refinement
precondition (cf. `hVec`/`hVal` in `runsAgree_insert_lane`).
-/

/-- **Faithful refinement of `vector.pack_lanes`.** The dialect denotation and
    the base-threaded lowering `lowerPackLanesFrom` agree on every state in the
    refinement domain (`hdom`: operands all bound to lane-typed values, of the
    declared count). Genuine discharge of the obligation formerly taken as
    `axiom runsAgree_pack_lanes`. -/
theorem runsAgreeFrom_pack_lanes
    (op : DialectOpSem) (spec : PackLanesSpec)
    (n lenN w : Nat) (elemTy : Ty) (P : Value → Bool)
    (seedZeros : List Constant) (seedLanes : List Value)
    (hRun : op.runOp = runSpec op.inst (.packLanes spec))
    (helem : spec.elemTy = elemTy)
    (hlanes : spec.lanes = lenN)
    (hbw : elemTy.bitWidth = some w)
    (hchar : ∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
               = (decide (ls.length = lenN) && ls.all P))
    (hlaneP : ∀ v : Value, elemTy.executableVectorLaneValueMatches v = P v)
    (hseedEq : (seedZeros.map (fun c => match c with
                   | .int i => Value.intAt w i | other => constValueAt elemTy other)) = seedLanes)
    (hseedLen : seedLanes.length = lenN)
    (hseedP : seedLanes.all P = true)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ vals, lookupOperands op.inst.operands s = .ok vals ∧
                      vals.length = lenN ∧ vals.all P = true) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerPackLanesFrom (Ty.Vector n elemTy) seedZeros op.inst.operands base) := by
  intro s hdomS
  obtain ⟨vals, hlook, hvalsLen, hvalsP⟩ := hdom s hdomS
  have hvalsPmem : ∀ v ∈ vals, P v = true := (List.all_eq_true).mp hvalsP
  -- The dialect takes its success path, binding `.vector vals`.
  have hlaneVals : vals.all (laneValueMatches spec.elemTy) = true := by
    rw [helem, List.all_eq_true]
    intro v hv
    show elemTy.executableVectorLaneValueMatches v = true
    rw [hlaneP]; exact hvalsPmem v hv
  have hcountVals : (vals.length == spec.lanes) = true := by
    rw [hlanes, hvalsLen]; exact beq_self_eq_true lenN
  have hrunOk : op.runOp s = .ok (bindFreshValue s (.vector vals)) := by
    rw [hRun]
    simp [runSpec, runPackLanes, bind, Except.bind, pure, Except.pure,
          hlook, hlaneVals, hcountVals]
  -- The lowering: step the zero seed, then run the insert chain at j = 0.
  have hseedPayload : (Ty.Vector n elemTy).executableVectorPayloadMatches seedLanes = true := by
    rw [hchar, Bool.and_eq_true]; exact ⟨decide_eq_true hseedLen, hseedP⟩
  have hShape := executable_payload_shape n elemTy seedLanes hseedPayload
  have hSeedCount : seedZeros.length = n := by
    have hlen := congrArg List.length hseedEq
    simp only [List.length_map] at hlen
    exact hlen.trans hShape.1
  have hSeedTyped : ∀ c ∈ seedZeros, ConstInlineAdmitted false elemTy c := by
    intro c hc
    apply seed_admitted_of_lane elemTy w c
    rw [hlaneP]
    have hP := hseedP
    rw [← hseedEq] at hP
    exact (List.all_eq_true).mp hP _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hConst : Sem.run (stepInst (.Const (.Vector n elemTy) (.vector seedZeros))) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.vector seedLanes)) := by
    have hseedNoSym : Constant.listHasSymbolAddr seedZeros = false := by
      apply listHasSymbolAddr_eq_false_of_forall
      intro c hc
      apply seed_noSym_of_lane elemTy w c
      rw [hlaneP]
      have hP := hseedP
      rw [← hseedEq] at hP
      exact (List.all_eq_true).mp hP _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have h := run_stepConstVec n elemTy w seedZeros s hbw hShape.2.1 hSeedCount
      hShape.2.2 hSeedTyped hseedNoSym
    rw [hseedEq] at h; exact h
  have hpres : ∀ id : ValueId, id.index < s.nextValueId →
      (bindOne s (.vector seedLanes)).lookupValue id = s.lookupValue id := fun id hid =>
    lookup_bindOne_below s (.vector seedLanes) id s.nextValueId hid (Nat.le_refl _)
  have hnext0 : (bindOne s (.vector seedLanes)).nextValueId = s.nextValueId + 1 + 2 * 0 := by
    rw [bindOne_nextValueId]
  have hcur0 : (bindOne s (.vector seedLanes)).lookupValue (ValueId.mk (s.nextValueId + 2 * 0))
      = some (.vector seedLanes) := by
    simpa using lookup_bindOne_self s (.vector seedLanes)
  have hpay0 : (Ty.Vector n elemTy).executableVectorPayloadMatches seedLanes = true := by
    rw [hchar, Bool.and_eq_true]; exact ⟨decide_eq_true hseedLen, hseedP⟩
  have hsum0 : 0 + vals.length = seedLanes.length := by rw [hvalsLen, hseedLen]; omega
  obtain ⟨s2, hrun2, hnext2, hmem2, hperm2, href2, hvec2⟩ :=
    run_packInsertsFrom n lenN s.nextValueId elemTy P s hchar hlaneP
      op.inst.operands vals (bindOne s (.vector seedLanes)) 0 seedLanes
      hlook hpres hdomS hvalsPmem hnext0 hcur0 hpay0 hsum0
  simp only [hrunOk]
  refine ⟨(), s2, ?_, ?_, .vector vals, .vector vals, ?_, ?_, rfl⟩
  · -- the full lowering run
    show Sem.run (runInsts (lowerPackLanesFrom (Ty.Vector n elemTy) seedZeros
      op.inst.operands s.nextValueId)) s = .ok ((), s2)
    unfold lowerPackLanesFrom
    rw [runInsts_cons_value _ _ _ _ _ hConst]
    exact hrun2
  · -- state agreement (memory / permissions / refcounts)
    show state_equiv_except_locals (bindOne s (.vector vals)) s2
    refine ⟨?_, ?_, ?_⟩
    · simp only [hmem2, bindOne_memory]
    · simp only [hperm2, bindOne_permissions]
    · simp only [href2, bindOne_refCounts]
  · -- dialect result value at the final fresh id
    show (bindOne s (.vector vals)).lookupValue
      (ValueId.mk ((bindOne s (.vector vals)).nextValueId - 1)) = some (.vector vals)
    have hn1 : (bindOne s (.vector vals)).nextValueId - 1 = s.nextValueId := by
      rw [bindOne_nextValueId]; omega
    rw [hn1]; exact lookup_bindOne_self s (.vector vals)
  · -- lowering result value, identical to the dialect's
    have hid2 : s2.nextValueId - 1 = s.nextValueId + 2 * (0 + op.inst.operands.length) := by
      rw [hnext2]; omega
    rw [hid2, hvec2, List.take_zero, List.nil_append]

/-- Core `BEq`/`decide` bridge for `Nat`. The executable payload checks use
    `==` (`Nat.beq`) whereas the `run_packInsertsFrom` characterisation is
    phrased with `decide (· = ·)`; this connects the two for the corollaries. -/
theorem beq_eq_decide_nat (a b : Nat) : (a == b) = decide (a = b) := by
  cases h : decide (a = b) with
  | true => simp only [decide_eq_true_eq] at h; subst h; simp
  | false => simp only [decide_eq_false_iff_not] at h; simp [h]

/-- `<4 x i32>` instance of `runsAgreeFrom_pack_lanes`: every characterisation
    and seed hypothesis discharges by `rfl`/`decide`, leaving only the genuine
    refinement-domain precondition `hdom`. Witnesses that the general theorem is
    non-vacuous at a supported vector shape. -/
theorem runsAgreeFrom_pack_lanes_v4i32
    (op : DialectOpSem) (spec : PackLanesSpec)
    (hRun : op.runOp = runSpec op.inst (.packLanes spec))
    (helem : spec.elemTy = .I32)
    (hlanes : spec.lanes = 4)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ vals, lookupOperands op.inst.operands s = .ok vals ∧
                      vals.length = 4 ∧ vals.all (Value.isIntWidth 32) = true) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerPackLanesFrom (.Vector 4 .I32)
        [.int 0, .int 0, .int 0, .int 0] op.inst.operands base) :=
  runsAgreeFrom_pack_lanes op spec 4 4 32 .I32 (Value.isIntWidth 32)
    [.int 0, .int 0, .int 0, .int 0] [.int 32 0, .int 32 0, .int 32 0, .int 32 0]
    hRun helem hlanes rfl
    (fun ls => by
      show (ls.length == 4 && ls.all (Value.isIntWidth 32))
        = (decide (ls.length = 4) && ls.all (Value.isIntWidth 32))
      rw [beq_eq_decide_nat])
    (fun _ => rfl) rfl rfl rfl hdom

/-- `<2 x i64>` instance of `runsAgreeFrom_pack_lanes`; companion to the
    `<4 x i32>` corollary above. -/
theorem runsAgreeFrom_pack_lanes_v2i64
    (op : DialectOpSem) (spec : PackLanesSpec)
    (hRun : op.runOp = runSpec op.inst (.packLanes spec))
    (helem : spec.elemTy = .I64)
    (hlanes : spec.lanes = 2)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ vals, lookupOperands op.inst.operands s = .ok vals ∧
                      vals.length = 2 ∧ vals.all (Value.isIntWidth 64) = true) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerPackLanesFrom (.Vector 2 .I64)
        [.int 0, .int 0] op.inst.operands base) :=
  runsAgreeFrom_pack_lanes op spec 2 2 64 .I64 (Value.isIntWidth 64)
    [.int 0, .int 0] [.int 64 0, .int 64 0]
    hRun helem hlanes rfl
    (fun ls => by
      show (ls.length == 2 && ls.all (Value.isIntWidth 64))
        = (decide (ls.length = 2) && ls.all (Value.isIntWidth 64))
      rw [beq_eq_decide_nat])
    (fun _ => rfl) rfl rfl rfl hdom

/-!
## Faithful refinement for `vector.mask_to_bits` — arithmetic core

The dialect denotation `maskBitsAux` folds the bool lanes into a `Nat`,
adding `2^index` for each set lane.  A faithful lowering rebuilds that
integer with core IR ops: per lane it extracts the bool, `Select`s either
`2^index` or `0`, and accumulates with an integer `Add`.  These lemmas
relate that fold to `maskBitsAux` and bound it so the fixed-width `Add`
never wraps (the bounded executable bool subset has at most 4 lanes, far
below the 32/64-bit accumulator). -/

/-- Pure `Nat` denotation of the lane fold: the contribution of `bits`,
    starting at bit position `idx`. The mask-side `maskBitsAux` equals this
    (plus the running accumulator) on an all-bool mask. -/
def boolListBits : List Bool → Nat → Nat
  | [], _ => 0
  | b :: rest, idx => (if b then 2 ^ idx else 0) + boolListBits rest (idx + 1)

/-- On an all-bool mask `bits.map Value.bool`, the dialect fold `maskBitsAux`
    is exactly the running accumulator plus `boolListBits`. -/
theorem maskBitsAux_map (bits : List Bool) (idx acc : Nat) :
    maskBitsAux (bits.map (Value.bool ·)) idx acc
      = .ok (acc + boolListBits bits idx) := by
  trustIrCompilerProof {
    induction bits generalizing idx acc with
    | nil => simp [maskBitsAux, boolListBits]
    | cons b rest ih =>
      simp only [List.map_cons, maskBitsAux, boolListBits]
      rw [ih]
      congr 1
      cases b <;> simp only [if_true, if_false] <;> omega
  } {
    induction bits generalizing idx acc with
    | nil => simp [maskBitsAux, boolListBits]
    | cons b rest ih =>
      simp only [List.map_cons, maskBitsAux, boolListBits]
      rw [ih]
      congr 1
      cases b <;> (simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false]) <;> omega
  }

/-- Strengthened bound: the fold plus the leading bit weight stays within the
    next power of two. Gives `boolListBits bits idx < 2 ^ (idx + bits.length)`
    and, at `idx = 0`, `boolListBits bits 0 < 2 ^ bits.length`. -/
theorem boolListBits_add_lt (bits : List Bool) (idx : Nat) :
    boolListBits bits idx + 2 ^ idx ≤ 2 ^ (idx + bits.length) := by
  trustIrCompilerProof {
    induction bits generalizing idx with
    | nil => simp [boolListBits]
    | cons b rest ih =>
      have hih := ih (idx + 1)
      have hpow : (2 : Nat) ^ (idx + 1) = 2 ^ idx + 2 ^ idx := by
        rw [Nat.pow_succ]; omega
      have e1 : idx + (rest.length + 1) = (idx + 1) + rest.length := by omega
      rw [List.length_cons, e1]
      simp only [boolListBits]
      -- Abstract the power terms to plain `Nat` variables so `omega` gets their
      -- nonnegativity (it otherwise treats `2 ^ k` as a sign-unknown atom).
      revert hih hpow
      generalize (2 : Nat) ^ idx = A
      generalize (2 : Nat) ^ (idx + 1) = B
      generalize (2 : Nat) ^ (idx + 1 + rest.length) = R
      intro hpow hih
      cases b <;> simp only [if_true, if_false] <;> omega
  } {
    induction bits generalizing idx with
    | nil => simp [boolListBits]
    | cons b rest ih =>
      have hih := ih (idx + 1)
      have hpow : (2 : Nat) ^ (idx + 1) = 2 ^ idx + 2 ^ idx := by
        rw [Nat.pow_succ]; omega
      have e1 : idx + (rest.length + 1) = (idx + 1) + rest.length := by omega
      rw [List.length_cons, e1]
      simp only [boolListBits]
      -- Abstract the power terms to plain `Nat` variables so `omega` gets their
      -- nonnegativity (it otherwise treats `2 ^ k` as a sign-unknown atom).
      revert hih hpow
      generalize (2 : Nat) ^ idx = A
      generalize (2 : Nat) ^ (idx + 1) = B
      generalize (2 : Nat) ^ (idx + 1 + rest.length) = R
      intro hpow hih
      cases b <;> (simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false]) <;> omega
  }

/-- `wrap` (the fixed-width modular reduction used by `semIntBinOp`) is the
    identity on a non-negative integer already below the modulus. -/
theorem wrap_eq_self (w : Nat) (v : Int) (h0 : 0 ≤ v) (hlt : v < (2 : Int) ^ w) :
    (((v % (2 : Int) ^ w) + (2 : Int) ^ w) % (2 : Int) ^ w) = v := by
  have h1 : v % (2 : Int) ^ w = v := Int.emod_eq_of_lt h0 hlt
  rw [h1]
  have h2 : (v + (2 : Int) ^ w) % (2 : Int) ^ w = v % (2 : Int) ^ w := by
    have h := Int.add_mul_emod_self_left v ((2 : Int) ^ w) 1
    rwa [Int.mul_one] at h
  rw [h2, h1]

/-- The integer modulus `(2 : Int) ^ w` is the cast of the `Nat` power, so a
    `Nat` bound transfers to the `Int` side used by `semIntBinOp`. -/
theorem two_pow_int (w : Nat) : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by
  trustIrCompilerProof {
    induction w with
    | zero => rfl
    | succ k ih => rw [Int.pow_succ, Nat.pow_succ, ih, Int.ofNat_mul]; rfl
  } {
    induction w with
    | zero => rfl
    | succ k ih => rw [Int.pow_succ, Nat.pow_succ, ih, Int.natCast_mul]; rfl
  }

/-!
## Bitwise-OR fold = bit-packed sum (the `BinOp .Or` accumulator)

The shipped Rust pass (`lower_mask_to_bits`) accumulates lane contributions
with `BinOp::Or`, not `Add`. For disjoint single-bit contributions the two
agree: an accumulator `A < 2^j` (carrying only bits below position `j`) OR a
contribution `c ∈ {0, 2^j}` (a single bit at position `j`) equals `A + c`,
because the bit at position `j` is clear in `A`. These lemmas establish that
identity over the `Nat`/`Int.lor` model and lift it to `semIntBinOp .Or`. -/

/-- Disjoint bitwise OR is addition: a `Nat` already below `2^j` shares no bit
    with `2^j`, so OR-ing the high bit in is the same as adding it. Proved by
    `testBit` extensionality using the core two-power bit lemmas (no Mathlib). -/
theorem nat_lor_two_pow_of_lt {A j : Nat} (h : A < 2 ^ j) :
    Nat.lor A (2 ^ j) = A + 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show Nat.lor A (2 ^ j) = A ||| 2 ^ j from rfl, Nat.testBit_or, Nat.add_comm A (2 ^ j)]
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · -- i < j: the `2^j` bit is clear at position i (< j), so OR = `A`'s bit,
    -- and `(2^j + A)`'s low bit also equals `A`'s bit.
    have h2 : (2 ^ j).testBit i = false := by
      have := Nat.testBit_two_pow_add_gt hij 0
      simpa using this
    rw [h2, Bool.or_false, Nat.testBit_two_pow_add_gt hij A]
  · -- i = j: `A`'s bit is clear (A < 2^j), the `2^j` bit is set, sum bit is set.
    subst hij
    have hAbit : A.testBit i = false := Nat.testBit_lt_two_pow h
    have hpow : (2 ^ i).testBit i = true := by
      have := Nat.testBit_two_pow_add_eq 0 i
      simpa using this
    have hsum : (2 ^ i + A).testBit i = true := by
      rw [Nat.testBit_two_pow_add_eq, hAbit]; rfl
    rw [hAbit, hpow, hsum]; rfl
  · -- i > j: both `A` and `2^j` are below `2^i`, as is their sum, so all bits
    -- at position i are clear.
    have hApow : A < 2 ^ i := Nat.lt_trans h (Nat.pow_lt_pow_of_lt (by omega) hij)
    have hAbit : A.testBit i = false := Nat.testBit_lt_two_pow hApow
    have h2 : (2 ^ j).testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.pow_lt_pow_of_lt (by omega) hij)
    have hsumlt : 2 ^ j + A < 2 ^ i := by
      have hle : 2 ^ j + 2 ^ j ≤ 2 ^ i := by
        have h2j : (2 : Nat) ^ j + 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
        rw [h2j]; exact Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hsum : (2 ^ j + A).testBit i = false := Nat.testBit_lt_two_pow hsumlt
    rw [hAbit, h2, hsum]; rfl

/-- `Int.lor` lifts `nat_lor_two_pow_of_lt`: for a non-negative accumulator
    below `2^j`, OR-ing the lane weight `2^j` equals the integer sum. -/
theorem int_lor_two_pow_of_lt {A j : Nat} (h : A < 2 ^ j) :
    Int.lor (Int.ofNat A) (Int.ofNat (2 ^ j)) = Int.ofNat (A + 2 ^ j) := by
  show Int.ofNat (Nat.lor A (2 ^ j)) = Int.ofNat (A + 2 ^ j)
  rw [nat_lor_two_pow_of_lt h]

/-- `Nat.lor` with a zero right operand is the identity. -/
theorem nat_lor_zero (m : Nat) : Nat.lor m 0 = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show Nat.lor m 0 = m ||| 0 from rfl, Nat.testBit_or, Nat.zero_testBit, Bool.or_false]

/-- `Int.lor` of a non-negative value with zero is the identity (the `Select`
    else branch contributes `0` for a clear lane). Stated on `Int.ofNat` because
    the running accumulator is always non-negative. -/
theorem int_lor_ofNat_zero (m : Nat) : Int.lor (Int.ofNat m) 0 = Int.ofNat m := by
  show Int.ofNat (Nat.lor m 0) = Int.ofNat m
  rw [nat_lor_zero]

/-- `Sem.run` of an integer `Or` on two operands of width `w` whose bitwise OR
    equals their (non-negative, sub-modulus) integer sum, so the fixed-width wrap
    is the identity. Generic over the `Int` payloads with the `lor = +` fact
    supplied by the caller (mirrors `run_stepBinOpAddInt`); the disjoint-bit
    reasoning is discharged by `int_lor_two_pow_of_lt` / `int_lor_ofNat_zero`
    in the loop body. This is the load-bearing alignment with the shipped Rust
    pass, which accumulates lane contributions with `BinOp::Or`. -/
theorem run_stepBinOpOrInt (resultTy : Ty) (w : Nat) (a c : Int)
    (accId contribId : ValueId) (s : MachineState)
    (hacc : s.lookupValue accId = some (.int w a))
    (hcontrib : s.lookupValue contribId = some (.int w c))
    (hlor : Int.lor a c = a + c)
    (h0 : 0 ≤ a + c) (hlt : a + c < (2 : Int) ^ w) :
    Sem.run (stepInst (.BinOp .Or resultTy accId contribId)) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w (a + c))) := by
  have hwrap : semIntBinOp .Or w a c = .ok (a + c) := by
    show Except.ok ((((Int.lor a c) % (2 : Int) ^ w) + (2 : Int) ^ w) % (2 : Int) ^ w)
        = .ok (a + c)
    rw [hlor, wrap_eq_self w (a + c) h0 hlt]
  simp [stepInst, Ty.bitWidthFor, semBinOp, semBinOpDeterministic, semBinOpValues,
        BinOp.isMinMax, Sem.rejectPartial, Sem.lookupValue, hacc, hcontrib, hwrap,
        Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
        StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
        bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]

/-!
## Step helpers for the `vector.mask_to_bits` lowering

The faithful lowering emits, per lane, an index `Const`, a bool
`ExtractElement`, a power-of-two `Const`, a scalar-bool `Select`, and an
integer `Add`.  The index/power `Const`s are already covered by
`run_stepConstInt`; the three lemmas below characterise the `Sem.run` of the
remaining three instruction shapes in terms of `bindOne`. -/

/-- `Sem.run` of a bool `ExtractElement` reading lane `j` of a bool mask. -/
theorem run_stepExtractElementBool (maskId idxId : ValueId) (s : MachineState)
    (maskLanes : List Value) (j : Nat) (b : Bool)
    (harr : s.lookupValue maskId = some (.vector maskLanes))
    (hidx : s.lookupValue idxId = some (.int 64 (Int.ofNat j)))
    (hpay : Ty.executableVectorLanePayloadMatches .Bool maskLanes = true)
    (hget : (trustIrListGet? maskLanes j) = some (.bool b)) :
    Sem.run (stepInst (.ExtractElement .Bool maskId idxId)) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.bool b)) := by
  have hlt : ¬ ((↑j : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg j)
  have hget' : getVectorElement .Bool (.vector maskLanes) j = .ok (.bool b) := by
    exact getVectorElement_of_executablePayload hpay hget
  simp [stepInst, Ty.bitWidthFor, semExtractElement, semExtractElementUsing, Sem.rejectPartial, Sem.lookupValue, harr, hidx, hlt, hget',
        Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
        StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
        bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]

/-- `Sem.run` of a scalar-bool `Select`: the condition gates the whole value. -/
theorem run_stepSelectScalarBool (ty : Ty) (condId thenId elseId : ValueId)
    (s : MachineState) (b : Bool) (tv ev : Value)
    (hcond : s.lookupValue condId = some (.bool b))
    (hthen : s.lookupValue thenId = some tv)
    (helse : s.lookupValue elseId = some ev) :
    Sem.run (stepInst (.Select ty condId thenId elseId)) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (if b then tv else ev)) := by
  cases b with
  | true =>
    simp [stepInst, Ty.bitWidthFor, Sem.rejectPartial, Sem.lookupValue, hcond, hthen,
          Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
          StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]
  | false =>
    simp [stepInst, Ty.bitWidthFor, Sem.rejectPartial, Sem.lookupValue, hcond, helse,
          Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
          StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
          bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]

/-!
## Faithful base-threaded lowering for `vector.mask_to_bits`

`maskLoopFrom` is the SSA-allocator-threaded refinement of the production
Rust pass (`lower_mask_to_bits`): for each lane `j` it emits an index
`Const`, a bool `ExtractElement`, a power-of-two `Const`, a scalar-bool
`Select` (picking the lane weight `2^j` or the shared zero constant), and an
integer `Or` that folds the contribution into the running accumulator — the
exact `BinOp::Or` the Rust pass emits. (For disjoint single-bit lane weights
`Or` and `Add` coincide; see `run_stepBinOpOrInt` and `nat_lor_two_pow_of_lt`.)
With the loop body starting at allocator counter `base + 2` (after the two
prologue `Const`s — a shared zero at `base`, the seed accumulator at
`base + 1`), the *j*-th lane block binds:

* `base + 2 + 5*j` — the lane index constant (`i64 j`),
* `base + 3 + 5*j` — the extracted bool lane,
* `base + 4 + 5*j` — the lane weight constant (`2^j`),
* `base + 5 + 5*j` — the `Select`ed contribution,
* `base + 6 + 5*j` — the new accumulator (`= base + 1 + 5*(j+1)`),

so the accumulator feeding lane `j` is uniformly at `base + 1 + 5*j`
(`= base + 1` = the seed for `j = 0`). These are exactly the ids
`MachineState.bindValue` hands out when execution reaches the loop with
`nextValueId = base + 2`. -/
def maskLoopFrom (resultTy : Ty) (maskId : ValueId) (base : Nat) :
    Nat → Nat → List Inst
  | _, 0 => []
  | j, count + 1 =>
    Inst.Const .I64 (.int (Int.ofNat j)) ::
    Inst.ExtractElement .Bool maskId (ValueId.mk (base + 2 + 5 * j)) ::
    Inst.Const resultTy (.int (Int.ofNat (2 ^ j))) ::
    Inst.Select resultTy (ValueId.mk (base + 3 + 5 * j))
      (ValueId.mk (base + 4 + 5 * j)) (ValueId.mk base) ::
    Inst.BinOp .Or resultTy (ValueId.mk (base + 1 + 5 * j))
      (ValueId.mk (base + 5 + 5 * j)) ::
    maskLoopFrom resultTy maskId base (j + 1) count

/-- The full mask-to-bits lowering: a shared zero `Const` (the `Select` else
    branch), a seed-accumulator `Const`, then the per-lane fold chain. -/
def lowerMaskToBitsFrom (resultTy : Ty) (maskId : ValueId)
    (lanes : Nat) (base : Nat) : List Inst :=
  Inst.Const resultTy (.int 0) ::
  Inst.Const resultTy (.int 0) ::
  maskLoopFrom resultTy maskId base 0 lanes

/-- **Faithful refinement of `vector.mask_to_bits` (induction core).** Running
    the per-lane fold chain from a state whose allocator counter is exactly
    `base + 2 + 5*j`, with the running accumulator `Int.ofNat A` bound at
    `ValueId.mk (base + 1 + 5*j)`, the shared zero at `ValueId.mk base`, and the
    bool mask readable at `maskId`, reproduces the dialect fold `boolListBits`:
    the chain terminates, leaves memory/permissions/refcounts untouched, and
    binds the accumulated bit pattern at the final fresh id. The fold uses the
    shipped pass's `BinOp::Or`; the disjointness invariant `hAcc : A < 2^j`
    (the accumulator carries only bits below position `j`) makes each `Or`
    coincide with `Add`, and `hbound` keeps the pattern below the modulus so the
    fixed-width op never wraps. The genuine multi-lane generalisation of the
    single-lane step helpers. -/
theorem run_maskLoopFrom (resultTy : Ty) (w : Nat) (maskId : ValueId)
    (base : Nat) (maskLanes : List Value) (s0 : MachineState)
    (hbw : resultTy.bitWidth = some w)
    (hInteger : resultTy.isInteger = true)
    (hpay : Ty.executableVectorLanePayloadMatches .Bool maskLanes = true)
    (hmaskDom : maskId.index < base)
    (hmask0 : s0.lookupValue maskId = some (.vector maskLanes)) :
    ∀ (bits : List Bool) (s : MachineState) (j A : Nat),
      (∀ id : ValueId, id.index < base → s.lookupValue id = s0.lookupValue id) →
      s.lookupValue (ValueId.mk base) = some (.int w 0) →
      s.nextValueId = base + 2 + 5 * j →
      s.lookupValue (ValueId.mk (base + 1 + 5 * j)) = some (.int w (Int.ofNat A)) →
      (∀ k, (trustIrListGet? maskLanes (j + k)) = ((trustIrListGet? bits k)).map (Value.bool ·)) →
      A < 2 ^ j →
      A + boolListBits bits j < 2 ^ w →
      j + bits.length ≤ w →
      ∃ s2 : MachineState,
        Sem.run (runInsts (maskLoopFrom resultTy maskId base j bits.length)) s
          = .ok ((), s2) ∧
        s2.nextValueId = base + 2 + 5 * (j + bits.length) ∧
        s2.memory = s.memory ∧ s2.permissions = s.permissions ∧
        s2.refCounts = s.refCounts ∧
        s2.lookupValue (ValueId.mk (base + 1 + 5 * (j + bits.length)))
          = some (.int w (Int.ofNat (A + boolListBits bits j))) := by
  trustIrCompilerProof {
    -- A single fresh bind preserves any id strictly below the pre-state counter.
    have pres1 : ∀ (id : ValueId) (st : MachineState) (c : Value),
        id.index < st.nextValueId → (bindOne st c).lookupValue id = st.lookupValue id :=
      fun id st c h => lookup_bindOne_ne st c id (Nat.ne_of_lt h)
    intro bits
    induction bits with
    | nil =>
      intro s j A _ _ hnext hacc _ _ _ _
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [maskLoopFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · simp only [List.length_nil, Nat.add_zero, boolListBits]; exact hacc
    | cons b rest ih =>
      intro s j A hpres hzero hnext hacc hmask hAlt hbound hjw
      -- The lane index is in bounds of the (at most 16-lane) mask, and below the
      -- result width (`hjw`), so both per-lane immediates are residues.
      have hj16 : j < 17 := by
        have hg := hmask 0
        simp only [Nat.add_zero, trustIrListGetConsZero, Option.map_some'] at hg
        have := lt_length_of_get?_some hg
        have := executableVectorLanePayloadMatches_length_le hpay
        omega
      have hpowI : (Int.ofNat (2 ^ j)) < (2 : Int) ^ w := by
        rw [two_pow_int]
        have hle : (2 : Nat) ^ (j + 1) ≤ 2 ^ w :=
          Nat.pow_le_pow_right (by decide) (by simp only [List.length_cons] at hjw; omega)
        have hpos : 0 < (2 : Nat) ^ j := Nat.pos_pow_of_pos j (by decide)
        exact Int.ofNat_lt.mpr (by omega)
      -- Unfold one lane block of the loop.
      have hunfold : maskLoopFrom resultTy maskId base j (b :: rest).length
          = Inst.Const .I64 (.int (Int.ofNat j))
            :: Inst.ExtractElement .Bool maskId (ValueId.mk (base + 2 + 5 * j))
            :: Inst.Const resultTy (.int (Int.ofNat (2 ^ j)))
            :: Inst.Select resultTy (ValueId.mk (base + 3 + 5 * j))
                 (ValueId.mk (base + 4 + 5 * j)) (ValueId.mk base)
            :: Inst.BinOp .Or resultTy (ValueId.mk (base + 1 + 5 * j))
                 (ValueId.mk (base + 5 + 5 * j))
            :: maskLoopFrom resultTy maskId base (j + 1) rest.length := by
        simp only [List.length_cons, maskLoopFrom]
      rw [hunfold]
      -- Step 1: index `Const` binds `i64 j` at `base + 2 + 5*j`.
      have hConstIdx : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat j)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat j))) :=
        run_stepConstInt .I64 (Int.ofNat j) 64 s rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 hj16)
      rw [runInsts_cons_value _ _ _ _ _ hConstIdx]
      -- Step 2: bool `ExtractElement` reads lane `j`.
      have harr1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue maskId
          = some (.vector maskLanes) := by
        rw [pres1 maskId s (.int 64 (Int.ofNat j)) (by rw [hnext]; omega),
            hpres maskId hmaskDom]; exact hmask0
      have hidx1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 2 + 5 * j))
          = some (.int 64 (Int.ofNat j)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat j)); rwa [hnext] at h
      have hgetlane : (trustIrListGet? maskLanes j) = some (.bool b) := by
        have h := hmask 0; simpa using h
      have hExtract := run_stepExtractElementBool maskId (ValueId.mk (base + 2 + 5 * j))
        (bindOne s (.int 64 (Int.ofNat j))) maskLanes j b harr1 hidx1 hpay hgetlane
      have hnext1 : (bindOne s (.int 64 (Int.ofNat j))).nextValueId = base + 3 + 5 * j := by
        rw [bindOne_nextValueId, hnext]; omega
      rw [hnext1] at hExtract
      rw [runInsts_cons_value _ _ _ _ _ hExtract]
      -- Step 3: power-of-two `Const` binds `2^j` at `base + 4 + 5*j`.
      have hConstPow : Sem.run (stepInst (.Const resultTy (.int (Int.ofNat (2 ^ j)))))
          (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          = .ok (.value (some (ValueId.mk (base + 4 + 5 * j))),
                 bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
                   (.int w (Int.ofNat (2 ^ j)))) := by
        have h := run_stepConstInt resultTy (Int.ofNat (2 ^ j)) w
          (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b)) hbw hInteger (Int.ofNat_nonneg _) hpowI
        have hn : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b)).nextValueId
            = base + 4 + 5 * j := by simp only [bindOne_nextValueId, hnext]; omega
        rwa [hn] at h
      rw [runInsts_cons_value _ _ _ _ _ hConstPow]
      -- Step 4: scalar-bool `Select` picks `2^j` (lane set) or the shared zero.
      have hcond : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).lookupValue (ValueId.mk (base + 3 + 5 * j))
          = some (.bool b) := by
        rw [pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega)]
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat j))) (.bool b)
        rwa [hnext1] at h
      have hthen : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).lookupValue (ValueId.mk (base + 4 + 5 * j))
          = some (.int w (Int.ofNat (2 ^ j))) := by
        have h := lookup_bindOne_self (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))
        have hn : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b)).nextValueId
            = base + 4 + 5 * j := by simp only [bindOne_nextValueId, hnext]; omega
        rwa [hn] at h
      have helse : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).lookupValue (ValueId.mk base) = some (.int w 0) := by
        rw [pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hzero
      have hSelect := run_stepSelectScalarBool resultTy (ValueId.mk (base + 3 + 5 * j))
        (ValueId.mk (base + 4 + 5 * j)) (ValueId.mk base)
        (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))) b (.int w (Int.ofNat (2 ^ j))) (.int w 0)
        hcond hthen helse
      have hnext3 : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).nextValueId = base + 5 + 5 * j := by
        simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext3] at hSelect
      rw [runInsts_cons_value _ _ _ _ _ hSelect]
      -- The `Select`ed value, pushed inside the `Value.int` constructor.
      have hSel : (if b then Value.int w (Int.ofNat (2 ^ j)) else Value.int w 0)
          = Value.int w (if b then Int.ofNat (2 ^ j) else 0) := by cases b <;> simp
      rw [hSel]
      -- Step 5: integer `Or` folds the contribution into the accumulator.
      generalize hS4 : bindOne (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
        (.int w (Int.ofNat (2 ^ j)))) (Value.int w (if b then Int.ofNat (2 ^ j) else 0)) = S4
      have hacc4 : S4.lookupValue (ValueId.mk (base + 1 + 5 * j))
          = some (.int w (Int.ofNat A)) := by
        rw [← hS4, pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hacc
      have hcontrib4 : S4.lookupValue (ValueId.mk (base + 5 + 5 * j))
          = some (.int w (if b then Int.ofNat (2 ^ j) else 0)) := by
        rw [← hS4]
        have h := lookup_bindOne_self (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))) (Value.int w (if b then Int.ofNat (2 ^ j) else 0))
        rwa [hnext3] at h
      -- Bound bookkeeping: the per-lane contribution keeps the sum under the modulus.
      have hbound' : A + ((if b then 2 ^ j else 0) + boolListBits rest (j + 1)) < 2 ^ w := by
        have := hbound; simp only [boolListBits] at this; exact this
      -- Push `Value.int`'s payload through the lane contribution: the Int sum equals the cast
      -- of a single Nat sum (`hAcast`), so `omega` never sees a raw `Int.ofNat` constructor
      -- (which it treats as a sign-free opaque atom, distinct from the `↑` cast). The order
      -- obligations then reduce to the Nat bound `hltN`.
      have hAcast : Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0)
          = Int.ofNat (A + if b then 2 ^ j else 0) := by cases b <;> simp <;> omega
      have hltN : (A + if b then 2 ^ j else 0) < 2 ^ w := by omega
      have h0 : (0 : Int) ≤ Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0) := by
        rw [hAcast]; exact Int.ofNat_nonneg _
      have hltI : Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0) < (2 : Int) ^ w := by
        rw [hAcast, two_pow_int]
        show ((A + if b then 2 ^ j else 0 : Nat) : Int) < ((2 ^ w : Nat) : Int)
        omega
      -- The disjoint-bit OR identity: the accumulator carries only bits below `j`
      -- (`hAlt : A < 2^j`), so OR-ing the lane weight `2^j` (or 0) equals the sum.
      have hlor : Int.lor (Int.ofNat A) (if b then Int.ofNat (2 ^ j) else 0)
          = Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0) := by
        cases b with
        | true =>
          rw [if_pos rfl, int_lor_two_pow_of_lt hAlt]
          show Int.ofNat (A + 2 ^ j) = Int.ofNat A + Int.ofNat (2 ^ j)
          simp
        | false =>
          rw [if_neg (by simp), int_lor_ofNat_zero]; simp
      have hBinOp := run_stepBinOpOrInt resultTy w (Int.ofNat A)
        (if b then Int.ofNat (2 ^ j) else 0) (ValueId.mk (base + 1 + 5 * j))
        (ValueId.mk (base + 5 + 5 * j)) S4 hacc4 hcontrib4 hlor h0 hltI
      have hnext4 : S4.nextValueId = base + 6 + 5 * j := by
        rw [← hS4]; simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext4] at hBinOp
      rw [runInsts_cons_value _ _ _ _ _ hBinOp]
      -- Recurse on the remaining lanes from the post-`Or` state.
      generalize hS5 : bindOne S4 (.int w (Int.ofNat A + if b then Int.ofNat (2 ^ j) else 0)) = S5
      have hpres5 : ∀ id : ValueId, id.index < base → S5.lookupValue id = s0.lookupValue id := by
        intro id hid
        rw [← hS5, pres1 _ _ _ (by rw [hnext4]; omega), ← hS4,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by rw [hnext]; omega)]
        exact hpres id hid
      have hzero5 : S5.lookupValue (ValueId.mk base) = some (.int w 0) := by
        rw [← hS5, pres1 _ _ _ (by simp only [hnext4]; omega), ← hS4,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hzero
      have hnext5 : S5.nextValueId = base + 2 + 5 * (j + 1) := by
        rw [← hS5]; simp only [bindOne_nextValueId, hnext4]; omega
      have hacc5 : S5.lookupValue (ValueId.mk (base + 1 + 5 * (j + 1)))
          = some (.int w (Int.ofNat (A + if b then 2 ^ j else 0))) := by
        rw [← hS5]
        have h := lookup_bindOne_self S4 (.int w (Int.ofNat A + if b then Int.ofNat (2 ^ j) else 0))
        have hn : S4.nextValueId = base + 1 + 5 * (j + 1) := by rw [hnext4]; omega
        rw [hn] at h; rw [h, hAcast]
      have hmask5 : ∀ k, (trustIrListGet? maskLanes ((j + 1) + k)) = ((trustIrListGet? rest k)).map (Value.bool ·) := by
        intro k
        have h := hmask (k + 1)
        simp only [trustIrListGetConsSucc] at h
        rw [show (j + 1) + k = j + (k + 1) by omega]; exact h
      have hbound5 : (A + if b then 2 ^ j else 0) + boolListBits rest (j + 1) < 2 ^ w := by
        omega
      -- Disjointness invariant for the next lane: the updated accumulator stays
      -- below `2^(j+1)` (it gained at most the single bit `2^j`, and `A < 2^j`).
      have hAlt5 : (A + if b then 2 ^ j else 0) < 2 ^ (j + 1) := by
        have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
        cases b <;> simp_all <;> omega
      obtain ⟨s6, hrun6, hnext6, hmem6, hperm6, href6, hacc6⟩ :=
        ih S5 (j + 1) (A + if b then 2 ^ j else 0) hpres5 hzero5 hnext5 hacc5 hmask5 hAlt5 hbound5
          (by simp only [List.length_cons] at hjw; omega)
      refine ⟨s6, hrun6, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext6]; simp only [List.length_cons]; omega
      · rw [hmem6, ← hS5, ← hS4]; simp
      · rw [hperm6, ← hS5, ← hS4]; simp
      · rw [href6, ← hS5, ← hS4]; simp
      · have hidxeq : j + (b :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq, hacc6]
        congr 2
        simp only [boolListBits]
        generalize (if b then 2 ^ j else 0) = z
        congr 1
        omega
  } {
    -- A single fresh bind preserves any id strictly below the pre-state counter.
    have pres1 : ∀ (id : ValueId) (st : MachineState) (c : Value),
        id.index < st.nextValueId → (bindOne st c).lookupValue id = st.lookupValue id :=
      fun id st c h => lookup_bindOne_ne st c id (Nat.ne_of_lt h)
    intro bits
    induction bits with
    | nil =>
      intro s j A _ _ hnext hacc _ _ _ _
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [maskLoopFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · simp only [List.length_nil, Nat.add_zero, boolListBits]; exact hacc
    | cons b rest ih =>
      intro s j A hpres hzero hnext hacc hmask hAlt hbound hjw
      -- The lane index is in bounds of the (at most 16-lane) mask, and below the
      -- result width (`hjw`), so both per-lane immediates are residues.
      have hj16 : j < 17 := by
        have hg := hmask 0
        simp only [Nat.add_zero, trustIrListGetConsZero, Option.map_some] at hg
        have := lt_length_of_get?_some hg
        have := executableVectorLanePayloadMatches_length_le hpay
        omega
      have hpowI : (Int.ofNat (2 ^ j)) < (2 : Int) ^ w := by
        rw [two_pow_int]
        have hle : (2 : Nat) ^ (j + 1) ≤ 2 ^ w :=
          Nat.pow_le_pow_right (by decide) (by simp only [List.length_cons] at hjw; omega)
        have hpos : 0 < (2 : Nat) ^ j := Nat.two_pow_pos j
        exact Int.ofNat_lt.mpr (by omega)
      -- Unfold one lane block of the loop.
      have hunfold : maskLoopFrom resultTy maskId base j (b :: rest).length
          = Inst.Const .I64 (.int (Int.ofNat j))
            :: Inst.ExtractElement .Bool maskId (ValueId.mk (base + 2 + 5 * j))
            :: Inst.Const resultTy (.int (Int.ofNat (2 ^ j)))
            :: Inst.Select resultTy (ValueId.mk (base + 3 + 5 * j))
                 (ValueId.mk (base + 4 + 5 * j)) (ValueId.mk base)
            :: Inst.BinOp .Or resultTy (ValueId.mk (base + 1 + 5 * j))
                 (ValueId.mk (base + 5 + 5 * j))
            :: maskLoopFrom resultTy maskId base (j + 1) rest.length := by
        simp only [List.length_cons, maskLoopFrom]
      rw [hunfold]
      -- Step 1: index `Const` binds `i64 j` at `base + 2 + 5*j`.
      have hConstIdx : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat j)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat j))) :=
        run_stepConstInt .I64 (Int.ofNat j) 64 s rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 hj16)
      rw [runInsts_cons_value _ _ _ _ _ hConstIdx]
      -- Step 2: bool `ExtractElement` reads lane `j`.
      have harr1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue maskId
          = some (.vector maskLanes) := by
        rw [pres1 maskId s (.int 64 (Int.ofNat j)) (by rw [hnext]; omega),
            hpres maskId hmaskDom]; exact hmask0
      have hidx1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 2 + 5 * j))
          = some (.int 64 (Int.ofNat j)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat j)); rwa [hnext] at h
      have hgetlane : (trustIrListGet? maskLanes j) = some (.bool b) := by
        have h := hmask 0; simpa using h
      have hExtract := run_stepExtractElementBool maskId (ValueId.mk (base + 2 + 5 * j))
        (bindOne s (.int 64 (Int.ofNat j))) maskLanes j b harr1 hidx1 hpay hgetlane
      have hnext1 : (bindOne s (.int 64 (Int.ofNat j))).nextValueId = base + 3 + 5 * j := by
        rw [bindOne_nextValueId, hnext]; omega
      rw [hnext1] at hExtract
      rw [runInsts_cons_value _ _ _ _ _ hExtract]
      -- Step 3: power-of-two `Const` binds `2^j` at `base + 4 + 5*j`.
      have hConstPow : Sem.run (stepInst (.Const resultTy (.int (Int.ofNat (2 ^ j)))))
          (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          = .ok (.value (some (ValueId.mk (base + 4 + 5 * j))),
                 bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
                   (.int w (Int.ofNat (2 ^ j)))) := by
        have h := run_stepConstInt resultTy (Int.ofNat (2 ^ j)) w
          (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b)) hbw hInteger (Int.ofNat_nonneg _) hpowI
        have hn : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b)).nextValueId
            = base + 4 + 5 * j := by simp only [bindOne_nextValueId, hnext]; omega
        rwa [hn] at h
      rw [runInsts_cons_value _ _ _ _ _ hConstPow]
      -- Step 4: scalar-bool `Select` picks `2^j` (lane set) or the shared zero.
      have hcond : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).lookupValue (ValueId.mk (base + 3 + 5 * j))
          = some (.bool b) := by
        rw [pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega)]
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat j))) (.bool b)
        rwa [hnext1] at h
      have hthen : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).lookupValue (ValueId.mk (base + 4 + 5 * j))
          = some (.int w (Int.ofNat (2 ^ j))) := by
        have h := lookup_bindOne_self (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))
        have hn : (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b)).nextValueId
            = base + 4 + 5 * j := by simp only [bindOne_nextValueId, hnext]; omega
        rwa [hn] at h
      have helse : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).lookupValue (ValueId.mk base) = some (.int w 0) := by
        rw [pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hzero
      have hSelect := run_stepSelectScalarBool resultTy (ValueId.mk (base + 3 + 5 * j))
        (ValueId.mk (base + 4 + 5 * j)) (ValueId.mk base)
        (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))) b (.int w (Int.ofNat (2 ^ j))) (.int w 0)
        hcond hthen helse
      have hnext3 : (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))).nextValueId = base + 5 + 5 * j := by
        simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext3] at hSelect
      rw [runInsts_cons_value _ _ _ _ _ hSelect]
      -- The `Select`ed value, pushed inside the `Value.int` constructor.
      have hSel : (if b then Value.int w (Int.ofNat (2 ^ j)) else Value.int w 0)
          = Value.int w (if b then Int.ofNat (2 ^ j) else 0) := by cases b <;> simp
      rw [hSel]
      -- Step 5: integer `Or` folds the contribution into the accumulator.
      generalize hS4 : bindOne (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
        (.int w (Int.ofNat (2 ^ j)))) (Value.int w (if b then Int.ofNat (2 ^ j) else 0)) = S4
      have hacc4 : S4.lookupValue (ValueId.mk (base + 1 + 5 * j))
          = some (.int w (Int.ofNat A)) := by
        rw [← hS4, pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hacc
      have hcontrib4 : S4.lookupValue (ValueId.mk (base + 5 + 5 * j))
          = some (.int w (if b then Int.ofNat (2 ^ j) else 0)) := by
        rw [← hS4]
        have h := lookup_bindOne_self (bindOne (bindOne (bindOne s (.int 64 (Int.ofNat j))) (.bool b))
          (.int w (Int.ofNat (2 ^ j)))) (Value.int w (if b then Int.ofNat (2 ^ j) else 0))
        rwa [hnext3] at h
      -- Bound bookkeeping: the per-lane contribution keeps the sum under the modulus.
      have hbound' : A + ((if b then 2 ^ j else 0) + boolListBits rest (j + 1)) < 2 ^ w := by
        have := hbound; simp only [boolListBits] at this; exact this
      -- Push `Value.int`'s payload through the lane contribution: the Int sum equals the cast
      -- of a single Nat sum (`hAcast`), so `omega` never sees a raw `Int.ofNat` constructor
      -- (which it treats as a sign-free opaque atom, distinct from the `↑` cast). The order
      -- obligations then reduce to the Nat bound `hltN`.
      have hAcast : Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0)
          = Int.ofNat (A + if b then 2 ^ j else 0) := by cases b <;> simp <;> omega
      have hltN : (A + if b then 2 ^ j else 0) < 2 ^ w := by omega
      have h0 : (0 : Int) ≤ Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0) := by
        rw [hAcast]; exact Int.ofNat_nonneg _
      have hltI : Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0) < (2 : Int) ^ w := by
        rw [hAcast, two_pow_int]
        show ((A + if b then 2 ^ j else 0 : Nat) : Int) < ((2 ^ w : Nat) : Int)
        omega
      -- The disjoint-bit OR identity: the accumulator carries only bits below `j`
      -- (`hAlt : A < 2^j`), so OR-ing the lane weight `2^j` (or 0) equals the sum.
      have hlor : Int.lor (Int.ofNat A) (if b then Int.ofNat (2 ^ j) else 0)
          = Int.ofNat A + (if b then Int.ofNat (2 ^ j) else 0) := by
        cases b with
        | true =>
          rw [if_pos rfl, int_lor_two_pow_of_lt hAlt]
          show Int.ofNat (A + 2 ^ j) = Int.ofNat A + Int.ofNat (2 ^ j)
          simp
        | false =>
          rw [if_neg (by simp), int_lor_ofNat_zero]; simp
      have hBinOp := run_stepBinOpOrInt resultTy w (Int.ofNat A)
        (if b then Int.ofNat (2 ^ j) else 0) (ValueId.mk (base + 1 + 5 * j))
        (ValueId.mk (base + 5 + 5 * j)) S4 hacc4 hcontrib4 hlor h0 hltI
      have hnext4 : S4.nextValueId = base + 6 + 5 * j := by
        rw [← hS4]; simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext4] at hBinOp
      rw [runInsts_cons_value _ _ _ _ _ hBinOp]
      -- Recurse on the remaining lanes from the post-`Or` state.
      generalize hS5 : bindOne S4 (.int w (Int.ofNat A + if b then Int.ofNat (2 ^ j) else 0)) = S5
      have hpres5 : ∀ id : ValueId, id.index < base → S5.lookupValue id = s0.lookupValue id := by
        intro id hid
        rw [← hS5, pres1 _ _ _ (by rw [hnext4]; omega), ← hS4,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by rw [hnext]; omega)]
        exact hpres id hid
      have hzero5 : S5.lookupValue (ValueId.mk base) = some (.int w 0) := by
        rw [← hS5, pres1 _ _ _ (by simp only [hnext4]; omega), ← hS4,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hzero
      have hnext5 : S5.nextValueId = base + 2 + 5 * (j + 1) := by
        rw [← hS5]; simp only [bindOne_nextValueId, hnext4]; omega
      have hacc5 : S5.lookupValue (ValueId.mk (base + 1 + 5 * (j + 1)))
          = some (.int w (Int.ofNat (A + if b then 2 ^ j else 0))) := by
        rw [← hS5]
        have h := lookup_bindOne_self S4 (.int w (Int.ofNat A + if b then Int.ofNat (2 ^ j) else 0))
        have hn : S4.nextValueId = base + 1 + 5 * (j + 1) := by rw [hnext4]; omega
        rw [hn] at h; rw [h, hAcast]
      have hmask5 : ∀ k, (trustIrListGet? maskLanes ((j + 1) + k)) = ((trustIrListGet? rest k)).map (Value.bool ·) := by
        intro k
        have h := hmask (k + 1)
        simp only [trustIrListGetConsSucc] at h
        rw [show (j + 1) + k = j + (k + 1) by omega]; exact h
      have hbound5 : (A + if b then 2 ^ j else 0) + boolListBits rest (j + 1) < 2 ^ w := by
        omega
      -- Disjointness invariant for the next lane: the updated accumulator stays
      -- below `2^(j+1)` (it gained at most the single bit `2^j`, and `A < 2^j`).
      have hAlt5 : (A + if b then 2 ^ j else 0) < 2 ^ (j + 1) := by
        have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
        cases b <;> simp_all <;> omega
      obtain ⟨s6, hrun6, hnext6, hmem6, hperm6, href6, hacc6⟩ :=
        ih S5 (j + 1) (A + if b then 2 ^ j else 0) hpres5 hzero5 hnext5 hacc5 hmask5 hAlt5 hbound5
          (by simp only [List.length_cons] at hjw; omega)
      refine ⟨s6, hrun6, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext6]; simp only [List.length_cons]; omega
      · rw [hmem6, ← hS5, ← hS4]; simp
      · rw [hperm6, ← hS5, ← hS4]; simp
      · rw [href6, ← hS5, ← hS4]; simp
      · have hidxeq : j + (b :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq, hacc6]
        congr 2
        simp only [boolListBits]
        generalize (if b then 2 ^ j else 0) = z
        congr 1
        omega
  }

/-!
## Refinement Lemma: vector.mask_to_bits

Discharged with a genuine proof (no axiom or proof placeholder):
`runsAgreeFrom_mask_to_bits` establishes dialect/lowering agreement against
the faithful, fresh-id-threaded `lowerMaskToBitsFrom` (two zero-seed
`Const`s — the shared `Select` else-branch and the seed accumulator —
followed by the per-lane fold chain `maskLoopFrom`), using the multi-lane
induction core `run_maskLoopFrom`. The former placeholder
`vectorLower.lowerMaskToBits` (which emitted only a descending sequence of
`ExtractElement .Bool` ops and never reassembled the integer) could not
satisfy the statement — its final bound value is a `.bool`, not the
dialect's packed `.int`; the seed/fold rewrite is what makes the agreement
true. The shape/width hypotheses pin the bounded executable bool mask (2 or
4 lanes) and hold by `rfl`/`decide` at the supported shapes
(`<4 x i1> → i32`, `<2 x i1> → i64`; see the corollaries below); `hdom` is
the well-typed-operands refinement precondition.
-/

/-- **Faithful refinement of `vector.mask_to_bits`.** The dialect denotation
    (`runMaskToBits`, which folds an all-bool mask into a packed integer) and
    the base-threaded lowering `lowerMaskToBitsFrom` agree on every state in the
    refinement domain (`hdom`: the single operand is bound to a bool mask vector
    of the declared lane count). Genuine discharge of the obligation formerly
    taken as `axiom runsAgree_mask_to_bits`. -/
theorem runsAgreeFrom_mask_to_bits
    (op : DialectOpSem) (spec : MaskToBitsSpec) (w : Nat)
    (hRun : op.runOp = runSpec op.inst (.maskToBits spec))
    (hbw : spec.resultTy.bitWidth = some w)
    (hInteger : spec.resultTy.isInteger = true)
    (hrw : resultWidth spec.resultTy = w)
    (hshape : spec.lanes = 16 ∨ spec.lanes = 8 ∨ spec.lanes = 4 ∨ spec.lanes = 2)
    (hlanes_le : spec.lanes ≤ w)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ (maskId : ValueId) (bits : List Bool),
                op.inst.operands = [maskId] ∧
                s.lookupValue maskId = some (.vector (bits.map (Value.bool ·))) ∧
                bits.length = spec.lanes) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerMaskToBitsFrom spec.resultTy ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) := by
  trustIrCompilerProof {
    intro s hdomS
    obtain ⟨maskId, bits, hops, hmaskVal, hbitsLen⟩ := hdom s hdomS
    have hmaskDom : maskId.index < s.nextValueId :=
      hdomS maskId (by rw [hops]; exact trustIrListMemConsSelf maskId [])
    have hget : (trustIrVectorGet! op.inst.operands 0) = maskId := by rw [hops]; rfl
    -- Every lane of the bool mask satisfies the bool payload predicate.
    have hall : (bits.map (Value.bool ·)).all Value.isBool = true := by
      have hgen : ∀ l : List Bool, (l.map (Value.bool ·)).all Value.isBool = true := by
        intro l; induction l with
        | nil => rfl
        | cons b bs ih => simp only [List.map_cons, List.all_cons, ih]; rfl
      exact hgen bits
    -- The dialect's mask-shape gate holds on the bool mask of the declared length.
    have hpayMatch : boolMaskPayloadMatches spec (bits.map (Value.bool ·)) = true := by
      unfold boolMaskPayloadMatches
      rw [List.length_map, hbitsLen, beq_self_eq_true, Bool.true_and]
      exact hall
    -- The dialect fold on `bits.map Value.bool` is exactly `boolListBits`.
    have hmaskBits : maskBits (bits.map (Value.bool ·)) = .ok (0 + boolListBits bits 0) := by
      unfold maskBits; exact maskBitsAux_map bits 0 0
    -- The lane payload hypothesis required by the induction core.
    have hpay : Ty.executableVectorLanePayloadMatches .Bool (bits.map (Value.bool ·)) = true := by
      simp only [Ty.executableVectorLanePayloadMatches,
        show Ty.executableIntLane? .Bool = none from rfl, List.length_map, hall, Bool.and_true]
      rw [hbitsLen]
      rcases hshape with h | h | h | h <;> simp [h]
    -- The dialect takes its success path, binding the packed integer.
    have hrunOk : op.runOp s
        = .ok (bindFreshValue s (.int w (Int.ofNat (0 + boolListBits bits 0)))) := by
      rw [hRun]
      simp only [runSpec, runMaskToBits, hops, hmaskVal, hpayMatch, hmaskBits, hrw,
        bind, Except.bind, pure, Except.pure, if_true]
      rfl
    -- The lowering: step the two zero seeds, then run the fold chain at j = 0.
    have hC1 : Sem.run (stepInst (.Const spec.resultTy (.int 0))) s
        = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w 0)) :=
      run_stepConstInt spec.resultTy 0 w s hbw hInteger (Int.le_refl 0) (two_pow_pos_int w)
    have hC2 : Sem.run (stepInst (.Const spec.resultTy (.int 0))) (bindOne s (.int w 0))
        = .ok (.value (some (ValueId.mk (bindOne s (.int w 0)).nextValueId)),
               bindOne (bindOne s (.int w 0)) (.int w 0)) :=
      run_stepConstInt spec.resultTy 0 w (bindOne s (.int w 0)) hbw hInteger (Int.le_refl 0)
        (two_pow_pos_int w)
    -- Hypotheses for the induction core, entering the loop with counter `base + 2`.
    have hpres0 : ∀ id : ValueId, id.index < s.nextValueId →
        (bindOne (bindOne s (.int w 0)) (.int w 0)).lookupValue id = s.lookupValue id := by
      intro id hid
      rw [lookup_bindOne_below (bindOne s (.int w 0)) (.int w 0) id s.nextValueId hid
            (by rw [bindOne_nextValueId]; omega),
          lookup_bindOne_below s (.int w 0) id s.nextValueId hid (Nat.le_refl _)]
    have hzero0 : (bindOne (bindOne s (.int w 0)) (.int w 0)).lookupValue (ValueId.mk s.nextValueId)
        = some (.int w 0) := by
      rw [lookup_bindOne_ne (bindOne s (.int w 0)) (.int w 0) (ValueId.mk s.nextValueId)
            (by simp only [bindOne_nextValueId]; omega)]
      exact lookup_bindOne_self s (.int w 0)
    have hnext0 : (bindOne (bindOne s (.int w 0)) (.int w 0)).nextValueId
        = s.nextValueId + 2 + 5 * 0 := by simp only [bindOne_nextValueId]
    have hacc0 : (bindOne (bindOne s (.int w 0)) (.int w 0)).lookupValue
        (ValueId.mk (s.nextValueId + 1 + 5 * 0)) = some (.int w (Int.ofNat 0)) := by
      have h := lookup_bindOne_self (bindOne s (.int w 0)) (.int w 0)
      rw [bindOne_nextValueId] at h
      simpa using h
    have hmaskAgree : ∀ k,
        (trustIrListGet? (bits.map (Value.bool ·)) (0 + k)) = ((trustIrListGet? bits k)).map (Value.bool ·) := by
      intro k; simp only [Nat.zero_add, List.get?_map]
    have hbnd0 : 0 + boolListBits bits 0 < 2 ^ w := by
      have h1 := boolListBits_add_lt bits 0
      simp only [Nat.pow_zero, Nat.zero_add] at h1
      have h2 : (2 : Nat) ^ bits.length ≤ 2 ^ w :=
        Nat.pow_le_pow_right (by omega) (by rw [hbitsLen]; exact hlanes_le)
      omega
    -- The seed accumulator is 0, below `2^0 = 1`: the disjointness invariant base.
    have hAlt0 : (0 : Nat) < 2 ^ 0 := by simp
    obtain ⟨sF, hrunF, hnextF, hmemF, hpermF, hrefF, haccF⟩ :=
      run_maskLoopFrom spec.resultTy w maskId s.nextValueId (bits.map (Value.bool ·)) s
        hbw hInteger hpay hmaskDom hmaskVal
        bits (bindOne (bindOne s (.int w 0)) (.int w 0)) 0 0
        hpres0 hzero0 hnext0 hacc0 hmaskAgree hAlt0 hbnd0 (by rw [hbitsLen]; omega)
    rw [hrunOk]
    refine ⟨(), sF, ?_, ?_, .int w (Int.ofNat (0 + boolListBits bits 0)),
      .int w (Int.ofNat (0 + boolListBits bits 0)), ?_, ?_, rfl⟩
    · -- the full lowering run
      show Sem.run (runInsts (lowerMaskToBitsFrom spec.resultTy
        ((trustIrVectorGet! op.inst.operands 0)) spec.lanes s.nextValueId)) s = .ok ((), sF)
      rw [hget]
      unfold lowerMaskToBitsFrom
      rw [runInsts_cons_value _ _ _ _ _ hC1, runInsts_cons_value _ _ _ _ _ hC2, ← hbitsLen]
      exact hrunF
    · -- state agreement (memory / permissions / refcounts)
      show state_equiv_except_locals
        (bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))) sF
      refine ⟨?_, ?_, ?_⟩
      · rw [hmemF]; simp
      · rw [hpermF]; simp
      · rw [hrefF]; simp
    · -- dialect result value at the final fresh id
      show (bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))).lookupValue
        (ValueId.mk ((bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))).nextValueId - 1))
        = some (.int w (Int.ofNat (0 + boolListBits bits 0)))
      have hn1 : (bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))).nextValueId - 1
          = s.nextValueId := by rw [bindOne_nextValueId]; omega
      rw [hn1]; exact lookup_bindOne_self s _
    · -- lowering result value, identical to the dialect's
      have hid : sF.nextValueId - 1 = s.nextValueId + 1 + 5 * (0 + bits.length) := by
        rw [hnextF]; omega
      rw [hid]; exact haccF
  } {
    intro s hdomS
    obtain ⟨maskId, bits, hops, hmaskVal, hbitsLen⟩ := hdom s hdomS
    have hmaskDom : maskId.index < s.nextValueId :=
      hdomS maskId (by rw [hops]; exact trustIrListMemConsSelf maskId [])
    have hget : (trustIrVectorGet! op.inst.operands 0) = maskId := by rw [hops]; rfl
    -- Every lane of the bool mask satisfies the bool payload predicate.
    have hall : (bits.map (Value.bool ·)).all Value.isBool = true := by
      have hgen : ∀ l : List Bool, (l.map (Value.bool ·)).all Value.isBool = true := by
        intro l; induction l with
        | nil => rfl
        | cons b bs ih => simp only [List.map_cons, List.all_cons, ih]; rfl
      exact hgen bits
    -- The dialect's mask-shape gate holds on the bool mask of the declared length.
    have hpayMatch : boolMaskPayloadMatches spec (bits.map (Value.bool ·)) = true := by
      unfold boolMaskPayloadMatches
      rw [List.length_map, hbitsLen, beq_self_eq_true, Bool.true_and]
      exact hall
    -- The dialect fold on `bits.map Value.bool` is exactly `boolListBits`.
    have hmaskBits : maskBits (bits.map (Value.bool ·)) = .ok (0 + boolListBits bits 0) := by
      unfold maskBits; exact maskBitsAux_map bits 0 0
    -- The lane payload hypothesis required by the induction core.
    have hpay : Ty.executableVectorLanePayloadMatches .Bool (bits.map (Value.bool ·)) = true := by
      simp only [Ty.executableVectorLanePayloadMatches,
        show Ty.executableIntLane? .Bool = none from rfl, List.length_map, hall, Bool.and_true]
      rw [hbitsLen]
      rcases hshape with h | h | h | h <;> simp [h]
    -- The dialect takes its success path, binding the packed integer.
    have hrunOk : op.runOp s
        = .ok (bindFreshValue s (.int w (Int.ofNat (0 + boolListBits bits 0)))) := by
      rw [hRun]
      simp only [runSpec, runMaskToBits, hops, hmaskVal, hpayMatch, hmaskBits, hrw,
        bind, Except.bind, pure, Except.pure, if_true]
      rfl
    -- The lowering: step the two zero seeds, then run the fold chain at j = 0.
    have hC1 : Sem.run (stepInst (.Const spec.resultTy (.int 0))) s
        = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w 0)) :=
      run_stepConstInt spec.resultTy 0 w s hbw hInteger (Int.le_refl 0) (two_pow_pos_int w)
    have hC2 : Sem.run (stepInst (.Const spec.resultTy (.int 0))) (bindOne s (.int w 0))
        = .ok (.value (some (ValueId.mk (bindOne s (.int w 0)).nextValueId)),
               bindOne (bindOne s (.int w 0)) (.int w 0)) :=
      run_stepConstInt spec.resultTy 0 w (bindOne s (.int w 0)) hbw hInteger (Int.le_refl 0)
        (two_pow_pos_int w)
    -- Hypotheses for the induction core, entering the loop with counter `base + 2`.
    have hpres0 : ∀ id : ValueId, id.index < s.nextValueId →
        (bindOne (bindOne s (.int w 0)) (.int w 0)).lookupValue id = s.lookupValue id := by
      intro id hid
      rw [lookup_bindOne_below (bindOne s (.int w 0)) (.int w 0) id s.nextValueId hid
            (by rw [bindOne_nextValueId]; omega),
          lookup_bindOne_below s (.int w 0) id s.nextValueId hid (Nat.le_refl _)]
    have hzero0 : (bindOne (bindOne s (.int w 0)) (.int w 0)).lookupValue (ValueId.mk s.nextValueId)
        = some (.int w 0) := by
      rw [lookup_bindOne_ne (bindOne s (.int w 0)) (.int w 0) (ValueId.mk s.nextValueId)
            (by simp only [bindOne_nextValueId]; omega)]
      exact lookup_bindOne_self s (.int w 0)
    have hnext0 : (bindOne (bindOne s (.int w 0)) (.int w 0)).nextValueId
        = s.nextValueId + 2 + 5 * 0 := by simp only [bindOne_nextValueId]
    have hacc0 : (bindOne (bindOne s (.int w 0)) (.int w 0)).lookupValue
        (ValueId.mk (s.nextValueId + 1 + 5 * 0)) = some (.int w (Int.ofNat 0)) := by
      have h := lookup_bindOne_self (bindOne s (.int w 0)) (.int w 0)
      rw [bindOne_nextValueId] at h
      simpa using h
    have hmaskAgree : ∀ k,
        (trustIrListGet? (bits.map (Value.bool ·)) (0 + k)) = ((trustIrListGet? bits k)).map (Value.bool ·) := by
      intro k; simp only [Nat.zero_add, CompilerCompat.listGetConstructive_map]
    have hbnd0 : 0 + boolListBits bits 0 < 2 ^ w := by
      have h1 := boolListBits_add_lt bits 0
      simp only [Nat.pow_zero, Nat.zero_add] at h1
      have h2 : (2 : Nat) ^ bits.length ≤ 2 ^ w :=
        Nat.pow_le_pow_right (by omega) (by rw [hbitsLen]; exact hlanes_le)
      omega
    -- The seed accumulator is 0, below `2^0 = 1`: the disjointness invariant base.
    have hAlt0 : (0 : Nat) < 2 ^ 0 := by simp
    obtain ⟨sF, hrunF, hnextF, hmemF, hpermF, hrefF, haccF⟩ :=
      run_maskLoopFrom spec.resultTy w maskId s.nextValueId (bits.map (Value.bool ·)) s
        hbw hInteger hpay hmaskDom hmaskVal
        bits (bindOne (bindOne s (.int w 0)) (.int w 0)) 0 0
        hpres0 hzero0 hnext0 hacc0 hmaskAgree hAlt0 hbnd0 (by rw [hbitsLen]; omega)
    rw [hrunOk]
    refine ⟨(), sF, ?_, ?_, .int w (Int.ofNat (0 + boolListBits bits 0)),
      .int w (Int.ofNat (0 + boolListBits bits 0)), ?_, ?_, rfl⟩
    · -- the full lowering run
      show Sem.run (runInsts (lowerMaskToBitsFrom spec.resultTy
        ((trustIrVectorGet! op.inst.operands 0)) spec.lanes s.nextValueId)) s = .ok ((), sF)
      rw [hget]
      unfold lowerMaskToBitsFrom
      rw [runInsts_cons_value _ _ _ _ _ hC1, runInsts_cons_value _ _ _ _ _ hC2, ← hbitsLen]
      exact hrunF
    · -- state agreement (memory / permissions / refcounts)
      show state_equiv_except_locals
        (bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))) sF
      refine ⟨?_, ?_, ?_⟩
      · rw [hmemF]; simp
      · rw [hpermF]; simp
      · rw [hrefF]; simp
    · -- dialect result value at the final fresh id
      show (bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))).lookupValue
        (ValueId.mk ((bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))).nextValueId - 1))
        = some (.int w (Int.ofNat (0 + boolListBits bits 0)))
      have hn1 : (bindOne s (.int w (Int.ofNat (0 + boolListBits bits 0)))).nextValueId - 1
          = s.nextValueId := by rw [bindOne_nextValueId]; omega
      rw [hn1]; exact lookup_bindOne_self s _
    · -- lowering result value, identical to the dialect's
      have hid : sF.nextValueId - 1 = s.nextValueId + 1 + 5 * (0 + bits.length) := by
        rw [hnextF]; omega
      rw [hid]; exact haccF
  }

/-- `<16 x i1> → i32` instance of `runsAgreeFrom_mask_to_bits`: the dialect's
    widest bool mask. The width/shape hypotheses discharge by `rfl`/`omega`,
    leaving only the genuine refinement-domain precondition `hdom`. Witnesses
    non-vacuity at the largest supported mask shape (`16 ≤ 32 = w`), now that the
    executable bool subset admits 16-lane masks. -/
theorem runsAgreeFrom_mask_to_bits_v16_bool
    (op : DialectOpSem) (spec : MaskToBitsSpec)
    (hRun : op.runOp = runSpec op.inst (.maskToBits spec))
    (hres : spec.resultTy = .I32)
    (hlanes : spec.lanes = 16)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ (maskId : ValueId) (bits : List Bool),
                op.inst.operands = [maskId] ∧
                s.lookupValue maskId = some (.vector (bits.map (Value.bool ·))) ∧
                bits.length = spec.lanes) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerMaskToBitsFrom spec.resultTy ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) :=
  runsAgreeFrom_mask_to_bits op spec 32 hRun (by rw [hres]; rfl) (by rw [hres]; rfl) (by rw [hres]; rfl)
    (Or.inl hlanes) (by omega) hdom

/-- `<8 x i1> → i32` instance of `runsAgreeFrom_mask_to_bits`; companion to the
    `<16 x i1>` corollary above (`8 ≤ 32 = w`). -/
theorem runsAgreeFrom_mask_to_bits_v8_bool
    (op : DialectOpSem) (spec : MaskToBitsSpec)
    (hRun : op.runOp = runSpec op.inst (.maskToBits spec))
    (hres : spec.resultTy = .I32)
    (hlanes : spec.lanes = 8)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ (maskId : ValueId) (bits : List Bool),
                op.inst.operands = [maskId] ∧
                s.lookupValue maskId = some (.vector (bits.map (Value.bool ·))) ∧
                bits.length = spec.lanes) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerMaskToBitsFrom spec.resultTy ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) :=
  runsAgreeFrom_mask_to_bits op spec 32 hRun (by rw [hres]; rfl) (by rw [hres]; rfl) (by rw [hres]; rfl)
    (Or.inr (Or.inl hlanes)) (by omega) hdom

/-- `<4 x i1> → i32` instance of `runsAgreeFrom_mask_to_bits`: the width/shape
    hypotheses discharge by `rfl`/`omega`, leaving only the genuine
    refinement-domain precondition `hdom`. Witnesses non-vacuity at a supported
    mask shape. -/
theorem runsAgreeFrom_mask_to_bits_v4_bool
    (op : DialectOpSem) (spec : MaskToBitsSpec)
    (hRun : op.runOp = runSpec op.inst (.maskToBits spec))
    (hres : spec.resultTy = .I32)
    (hlanes : spec.lanes = 4)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ (maskId : ValueId) (bits : List Bool),
                op.inst.operands = [maskId] ∧
                s.lookupValue maskId = some (.vector (bits.map (Value.bool ·))) ∧
                bits.length = spec.lanes) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerMaskToBitsFrom spec.resultTy ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) :=
  runsAgreeFrom_mask_to_bits op spec 32 hRun (by rw [hres]; rfl) (by rw [hres]; rfl) (by rw [hres]; rfl)
    (Or.inr (Or.inr (Or.inl hlanes))) (by omega) hdom

/-- `<2 x i1> → i64` instance of `runsAgreeFrom_mask_to_bits`; companion to the
    `<4 x i1>` corollary above. -/
theorem runsAgreeFrom_mask_to_bits_v2_bool
    (op : DialectOpSem) (spec : MaskToBitsSpec)
    (hRun : op.runOp = runSpec op.inst (.maskToBits spec))
    (hres : spec.resultTy = .I64)
    (hlanes : spec.lanes = 2)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ (maskId : ValueId) (bits : List Bool),
                op.inst.operands = [maskId] ∧
                s.lookupValue maskId = some (.vector (bits.map (Value.bool ·))) ∧
                bits.length = spec.lanes) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerMaskToBitsFrom spec.resultTy ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) :=
  runsAgreeFrom_mask_to_bits op spec 64 hRun (by rw [hres]; rfl) (by rw [hres]; rfl) (by rw [hres]; rfl)
    (Or.inr (Or.inr (Or.inr hlanes))) (by omega) hdom

/-!
## Faithful base-threaded lowering for `vector.reduce`

`reduceLoopFrom` is the SSA-allocator-threaded refinement of the production
Rust pass (`lower_reduce`): for each lane `j` it emits an index `Const`, an
`ExtractElement` of the lane, and an integer `BinOp` (`Add` for kind `add`,
`Or` for kind `or`) folding the lane into the running accumulator. With the
loop body starting at allocator counter `base + 1` (after the seed
accumulator `Const 0` at `base` — the fold identity for both kinds), the
*j*-th lane block binds:

* `base + 1 + 3*j` — the lane index constant (`i64 j`),
* `base + 2 + 3*j` — the extracted lane,
* `base + 3 + 3*j` — the new accumulator (`= base + 3*(j+1)`),

so the accumulator feeding lane `j` is uniformly at `base + 3*j`
(`= base` = the seed for `j = 0`). These are exactly the ids
`MachineState.bindValue` hands out when execution reaches the loop with
`nextValueId = base + 1`.

Unlike `mask_to_bits` (where `Or` had to be reconciled with `Add` through
disjoint-bit reasoning), the dialect denotation's fold step (`reduceStep`)
is *definitionally* the `semIntBinOp` success payload of the folded core op
(`semIntBinOp_reduceStep`), so both sides thread bit-identical accumulator
representations with no numeric side conditions. -/

/-- The dialect fold step IS the core `BinOp` step: `reduceStep` was defined
    as the fixed-width wrap of the kind's integer operation, matching
    `semIntBinOp`'s `Add`/`Or` arms definitionally. This is the load-bearing
    alignment between `runReduce` and the shipped Rust pass's `BinOp` chain. -/
theorem semIntBinOp_reduceStep (kind : ReduceKind) (w : Nat) (acc lane : Int) :
    semIntBinOp (reduceKindOp kind) w acc lane = .ok (reduceStep kind w acc lane) := by
  cases kind <;> rfl

/-- Pure `Int` denotation of the lane fold: fold `vals` into accumulator `acc`
    with the kind's wrapping step. The dialect-side `reduceAux` equals this on
    an all-int lane payload (`reduceAux_map`). -/
def reduceInts (kind : ReduceKind) (w : Nat) : List Int → Int → Int
  | [], acc => acc
  | lane :: rest, acc => reduceInts kind w rest (reduceStep kind w acc lane)

/-- On an all-int payload `vals.map (Value.int w' ·)`, the dialect fold
    `reduceAux` is exactly the pure fold `reduceInts` (the stored lane width is
    not consulted by the fold; the payload check upstream pins it). -/
theorem reduceAux_map (kind : ReduceKind) (w w' : Nat) (vals : List Int) (acc : Int) :
    reduceAux kind w (vals.map (fun i => Value.int w' i)) acc
      = .ok (reduceInts kind w vals acc) := by
  induction vals generalizing acc with
  | nil => rfl
  | cons lane rest ih =>
    simp only [List.map_cons, reduceAux, reduceInts]
    exact ih _

/-- Every lane of an int-mapped payload satisfies the width predicate. -/
theorem all_map_int_isIntWidth (w : Nat) (vals : List Int) :
    (vals.map (fun i => Value.int w i)).all (Value.isIntWidth w) = true := by
  induction vals with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.all_cons, ih, Bool.and_true]
    simp [Value.isIntWidth]

/-- `Sem.run` of an `ExtractElement` reading lane `j` of a supported lane
    vector. Generalises `run_stepExtractElementBool` from bool lanes to any
    stored lane value admitted by the executable payload check. -/
theorem run_stepExtractElementLane (elemTy : Ty) (vecId idxId : ValueId)
    (s : MachineState) (vecLanes : List Value) (j : Nat) (lane : Value)
    (harr : s.lookupValue vecId = some (.vector vecLanes))
    (hidx : s.lookupValue idxId = some (.int 64 (Int.ofNat j)))
    (hpay : Ty.executableVectorLanePayloadMatches elemTy vecLanes = true)
    (hget : (trustIrListGet? vecLanes j) = some lane) :
    Sem.run (stepInst (.ExtractElement elemTy vecId idxId)) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s lane) := by
  have hlt : ¬ ((↑j : Int) < 0) := Int.not_lt.mpr (Int.ofNat_nonneg j)
  have hget' : getVectorElement elemTy (.vector vecLanes) j = .ok lane := by
    exact getVectorElement_of_executablePayload hpay hget
  simp [stepInst, Ty.bitWidthFor, semExtractElement, semExtractElementUsing, Sem.rejectPartial, Sem.lookupValue, harr, hidx, hlt, hget',
        Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
        StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
        bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]

/-- `Sem.run` of an integer `BinOp` whose `semIntBinOp` result is supplied by
    the caller. Generalises `run_stepBinOpOrInt` from the disjoint-bit `Or`
    special case to any op/payload with a successful integer evaluation. -/
theorem run_stepBinOpIntOk (op : BinOp) (resultTy : Ty) (w : Nat) (a c r : Int)
    (lhsId rhsId : ValueId) (s : MachineState)
    (hlhs : s.lookupValue lhsId = some (.int w a))
    (hrhs : s.lookupValue rhsId = some (.int w c))
    (hsem : semIntBinOp op w a c = .ok r) :
    Sem.run (stepInst (.BinOp op resultTy lhsId rhsId)) s
      = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w r)) := by
  have noChoice : op.isMinMax = false := by
    cases op <;> first | rfl | cases hsem
  simp [stepInst, Ty.bitWidthFor, semBinOp, noChoice, semBinOpDeterministic,
        semBinOpValues, Sem.rejectPartial, Sem.lookupValue, hlhs, hrhs, hsem,
        Sem.getState, Sem.setState, Sem.bindFresh, Sem.run, Sem.run_bind, Sem.run_pure,
        StateT.run, StateT.bind, StateT.set, StateT.get, StateT.lift, StateT.pure,
        bind, pure, Except.bind, Except.pure, MachineState.bindValue, bindOne]

/-- Base-threaded per-lane fold chain of the Rust `lower_reduce`: index
    `Const`, lane `ExtractElement`, accumulator `BinOp`. -/
def reduceLoopFrom (elemTy : Ty) (op : BinOp) (vecId : ValueId) (base : Nat) :
    Nat → Nat → List Inst
  | _, 0 => []
  | j, count + 1 =>
    Inst.Const .I64 (.int (Int.ofNat j)) ::
    Inst.ExtractElement elemTy vecId (ValueId.mk (base + 1 + 3 * j)) ::
    Inst.BinOp op elemTy (ValueId.mk (base + 3 * j)) (ValueId.mk (base + 2 + 3 * j)) ::
    reduceLoopFrom elemTy op vecId base (j + 1) count

/-- The full reduce lowering: a seed-accumulator `Const 0` (the fold identity
    for both kinds), then the per-lane fold chain. Matches the Rust
    `lower_reduce` emission exactly. -/
def lowerReduceFrom (elemTy : Ty) (kind : ReduceKind) (vecId : ValueId)
    (lanes : Nat) (base : Nat) : List Inst :=
  Inst.Const elemTy (.int 0) ::
  reduceLoopFrom elemTy (reduceKindOp kind) vecId base 0 lanes

/-- **Faithful refinement of `vector.reduce` (induction core).** Running the
    per-lane fold chain from a state whose allocator counter is exactly
    `base + 1 + 3*j`, with the running accumulator bound at
    `ValueId.mk (base + 3*j)` and the source vector readable at `vecId`,
    reproduces the dialect fold `reduceInts`: the chain terminates, leaves
    memory/permissions/refcounts untouched, and binds the folded accumulator at
    the final fresh id. Each `BinOp` step is *definitionally* the dialect's
    `reduceStep` (`semIntBinOp_reduceStep`), so both sides thread identical
    accumulator representations with no numeric side conditions. -/
theorem run_reduceLoopFrom (elemTy : Ty) (w : Nat) (kind : ReduceKind)
    (vecId : ValueId) (base : Nat) (vecLanes : List Value) (s0 : MachineState)
    (hbw : elemTy.bitWidth = some w)
    (hpay : Ty.executableVectorLanePayloadMatches elemTy vecLanes = true)
    (hvecDom : vecId.index < base)
    (hvec0 : s0.lookupValue vecId = some (.vector vecLanes)) :
    ∀ (vals : List Int) (s : MachineState) (j : Nat) (A : Int),
      (∀ id : ValueId, id.index < base → s.lookupValue id = s0.lookupValue id) →
      s.nextValueId = base + 1 + 3 * j →
      s.lookupValue (ValueId.mk (base + 3 * j)) = some (.int w A) →
      (∀ k, (trustIrListGet? vecLanes (j + k)) = ((trustIrListGet? vals k)).map (fun i => Value.int w i)) →
      ∃ s2 : MachineState,
        Sem.run (runInsts (reduceLoopFrom elemTy (reduceKindOp kind) vecId base j vals.length)) s
          = .ok ((), s2) ∧
        s2.nextValueId = base + 1 + 3 * (j + vals.length) ∧
        s2.memory = s.memory ∧ s2.permissions = s.permissions ∧
        s2.refCounts = s.refCounts ∧
        s2.lookupValue (ValueId.mk (base + 3 * (j + vals.length)))
          = some (.int w (reduceInts kind w vals A)) := by
  trustIrCompilerProof {
    -- A single fresh bind preserves any id strictly below the pre-state counter.
    have pres1 : ∀ (id : ValueId) (st : MachineState) (c : Value),
        id.index < st.nextValueId → (bindOne st c).lookupValue id = st.lookupValue id :=
      fun id st c h => lookup_bindOne_ne st c id (Nat.ne_of_lt h)
    intro vals
    induction vals with
    | nil =>
      intro s j A _ hnext hacc _
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [reduceLoopFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · simp only [List.length_nil, Nat.add_zero, reduceInts]; exact hacc
    | cons lane rest ih =>
      intro s j A hpres hnext hacc hlanes
      -- Unfold one lane block of the loop.
      have hunfold : reduceLoopFrom elemTy (reduceKindOp kind) vecId base j (lane :: rest).length
          = Inst.Const .I64 (.int (Int.ofNat j))
            :: Inst.ExtractElement elemTy vecId (ValueId.mk (base + 1 + 3 * j))
            :: Inst.BinOp (reduceKindOp kind) elemTy (ValueId.mk (base + 3 * j))
                 (ValueId.mk (base + 2 + 3 * j))
            :: reduceLoopFrom elemTy (reduceKindOp kind) vecId base (j + 1) rest.length := by
        simp only [List.length_cons, reduceLoopFrom]
      rw [hunfold]
      -- Step 1: index `Const` binds `i64 j` at `base + 1 + 3*j`.
      have hConstIdx : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat j)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat j))) :=
        run_stepConstInt .I64 (Int.ofNat j) 64 s rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 (by
            have hg := hlanes 0
            simp only [Nat.add_zero, trustIrListGetConsZero, Option.map_some'] at hg
            have := lt_length_of_get?_some hg
            have := executableVectorLanePayloadMatches_length_le hpay
            omega))
      rw [runInsts_cons_value _ _ _ _ _ hConstIdx]
      -- Step 2: `ExtractElement` reads lane `j` of the source vector.
      have harr1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue vecId
          = some (.vector vecLanes) := by
        rw [pres1 vecId s _ (by rw [hnext]; omega), hpres vecId hvecDom]
        exact hvec0
      have hidx1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 1 + 3 * j))
          = some (.int 64 (Int.ofNat j)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat j)); rwa [hnext] at h
      have hgetlane : (trustIrListGet? vecLanes j) = some (Value.int w lane) := by
        have h := hlanes 0; simpa using h
      have hExtract := run_stepExtractElementLane elemTy vecId (ValueId.mk (base + 1 + 3 * j))
        (bindOne s (.int 64 (Int.ofNat j))) vecLanes j (Value.int w lane)
        harr1 hidx1 hpay hgetlane
      have hnext1 : (bindOne s (.int 64 (Int.ofNat j))).nextValueId = base + 2 + 3 * j := by
        rw [bindOne_nextValueId, hnext]; omega
      rw [hnext1] at hExtract
      rw [runInsts_cons_value _ _ _ _ _ hExtract]
      -- Step 3: `BinOp` folds the lane into the accumulator.
      generalize hS2 : bindOne (bindOne s (.int 64 (Int.ofNat j))) (Value.int w lane) = S2
      have hacc2 : S2.lookupValue (ValueId.mk (base + 3 * j)) = some (.int w A) := by
        rw [← hS2, pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hacc
      have hlane2 : S2.lookupValue (ValueId.mk (base + 2 + 3 * j)) = some (.int w lane) := by
        rw [← hS2]
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat j))) (Value.int w lane)
        rwa [hnext1] at h
      have hBinOp := run_stepBinOpIntOk (reduceKindOp kind) elemTy w A lane
        (reduceStep kind w A lane) (ValueId.mk (base + 3 * j)) (ValueId.mk (base + 2 + 3 * j))
        S2 hacc2 hlane2 (semIntBinOp_reduceStep kind w A lane)
      have hnext2 : S2.nextValueId = base + 3 + 3 * j := by
        rw [← hS2]; simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext2] at hBinOp
      rw [runInsts_cons_value _ _ _ _ _ hBinOp]
      -- Recurse on the remaining lanes from the post-`BinOp` state.
      generalize hS3 : bindOne S2 (Value.int w (reduceStep kind w A lane)) = S3
      have hpres3 : ∀ id : ValueId, id.index < base → S3.lookupValue id = s0.lookupValue id := by
        intro id hid
        rw [← hS3, pres1 _ _ _ (by rw [hnext2]; omega), ← hS2,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by rw [hnext]; omega)]
        exact hpres id hid
      have hnext3 : S3.nextValueId = base + 1 + 3 * (j + 1) := by
        rw [← hS3]; simp only [bindOne_nextValueId, hnext2]; omega
      have hacc3 : S3.lookupValue (ValueId.mk (base + 3 * (j + 1)))
          = some (.int w (reduceStep kind w A lane)) := by
        rw [← hS3]
        have h := lookup_bindOne_self S2 (Value.int w (reduceStep kind w A lane))
        have hn : S2.nextValueId = base + 3 * (j + 1) := by rw [hnext2]; omega
        rwa [hn] at h
      have hlanes3 : ∀ k, (trustIrListGet? vecLanes ((j + 1) + k))
          = ((trustIrListGet? rest k)).map (fun i => Value.int w i) := by
        intro k
        have h := hlanes (k + 1)
        simp only [trustIrListGetConsSucc] at h
        rw [show (j + 1) + k = j + (k + 1) by omega]; exact h
      obtain ⟨s4, hrun4, hnext4, hmem4, hperm4, href4, hacc4⟩ :=
        ih S3 (j + 1) (reduceStep kind w A lane) hpres3 hnext3 hacc3 hlanes3
      refine ⟨s4, hrun4, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext4]; simp only [List.length_cons]; omega
      · rw [hmem4, ← hS3, ← hS2]; simp
      · rw [hperm4, ← hS3, ← hS2]; simp
      · rw [href4, ← hS3, ← hS2]; simp
      · have hidxeq : j + (lane :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq]
        exact hacc4
  } {
    -- A single fresh bind preserves any id strictly below the pre-state counter.
    have pres1 : ∀ (id : ValueId) (st : MachineState) (c : Value),
        id.index < st.nextValueId → (bindOne st c).lookupValue id = st.lookupValue id :=
      fun id st c h => lookup_bindOne_ne st c id (Nat.ne_of_lt h)
    intro vals
    induction vals with
    | nil =>
      intro s j A _ hnext hacc _
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [reduceLoopFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · simp only [List.length_nil, Nat.add_zero, reduceInts]; exact hacc
    | cons lane rest ih =>
      intro s j A hpres hnext hacc hlanes
      -- Unfold one lane block of the loop.
      have hunfold : reduceLoopFrom elemTy (reduceKindOp kind) vecId base j (lane :: rest).length
          = Inst.Const .I64 (.int (Int.ofNat j))
            :: Inst.ExtractElement elemTy vecId (ValueId.mk (base + 1 + 3 * j))
            :: Inst.BinOp (reduceKindOp kind) elemTy (ValueId.mk (base + 3 * j))
                 (ValueId.mk (base + 2 + 3 * j))
            :: reduceLoopFrom elemTy (reduceKindOp kind) vecId base (j + 1) rest.length := by
        simp only [List.length_cons, reduceLoopFrom]
      rw [hunfold]
      -- Step 1: index `Const` binds `i64 j` at `base + 1 + 3*j`.
      have hConstIdx : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat j)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat j))) :=
        run_stepConstInt .I64 (Int.ofNat j) 64 s rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 (by
            have hg := hlanes 0
            simp only [Nat.add_zero, trustIrListGetConsZero, Option.map_some] at hg
            have := lt_length_of_get?_some hg
            have := executableVectorLanePayloadMatches_length_le hpay
            omega))
      rw [runInsts_cons_value _ _ _ _ _ hConstIdx]
      -- Step 2: `ExtractElement` reads lane `j` of the source vector.
      have harr1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue vecId
          = some (.vector vecLanes) := by
        rw [pres1 vecId s _ (by rw [hnext]; omega), hpres vecId hvecDom]
        exact hvec0
      have hidx1 : (bindOne s (.int 64 (Int.ofNat j))).lookupValue (ValueId.mk (base + 1 + 3 * j))
          = some (.int 64 (Int.ofNat j)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat j)); rwa [hnext] at h
      have hgetlane : (trustIrListGet? vecLanes j) = some (Value.int w lane) := by
        have h := hlanes 0; simpa using h
      have hExtract := run_stepExtractElementLane elemTy vecId (ValueId.mk (base + 1 + 3 * j))
        (bindOne s (.int 64 (Int.ofNat j))) vecLanes j (Value.int w lane)
        harr1 hidx1 hpay hgetlane
      have hnext1 : (bindOne s (.int 64 (Int.ofNat j))).nextValueId = base + 2 + 3 * j := by
        rw [bindOne_nextValueId, hnext]; omega
      rw [hnext1] at hExtract
      rw [runInsts_cons_value _ _ _ _ _ hExtract]
      -- Step 3: `BinOp` folds the lane into the accumulator.
      generalize hS2 : bindOne (bindOne s (.int 64 (Int.ofNat j))) (Value.int w lane) = S2
      have hacc2 : S2.lookupValue (ValueId.mk (base + 3 * j)) = some (.int w A) := by
        rw [← hS2, pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hacc
      have hlane2 : S2.lookupValue (ValueId.mk (base + 2 + 3 * j)) = some (.int w lane) := by
        rw [← hS2]
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat j))) (Value.int w lane)
        rwa [hnext1] at h
      have hBinOp := run_stepBinOpIntOk (reduceKindOp kind) elemTy w A lane
        (reduceStep kind w A lane) (ValueId.mk (base + 3 * j)) (ValueId.mk (base + 2 + 3 * j))
        S2 hacc2 hlane2 (semIntBinOp_reduceStep kind w A lane)
      have hnext2 : S2.nextValueId = base + 3 + 3 * j := by
        rw [← hS2]; simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext2] at hBinOp
      rw [runInsts_cons_value _ _ _ _ _ hBinOp]
      -- Recurse on the remaining lanes from the post-`BinOp` state.
      generalize hS3 : bindOne S2 (Value.int w (reduceStep kind w A lane)) = S3
      have hpres3 : ∀ id : ValueId, id.index < base → S3.lookupValue id = s0.lookupValue id := by
        intro id hid
        rw [← hS3, pres1 _ _ _ (by rw [hnext2]; omega), ← hS2,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by rw [hnext]; omega)]
        exact hpres id hid
      have hnext3 : S3.nextValueId = base + 1 + 3 * (j + 1) := by
        rw [← hS3]; simp only [bindOne_nextValueId, hnext2]; omega
      have hacc3 : S3.lookupValue (ValueId.mk (base + 3 * (j + 1)))
          = some (.int w (reduceStep kind w A lane)) := by
        rw [← hS3]
        have h := lookup_bindOne_self S2 (Value.int w (reduceStep kind w A lane))
        have hn : S2.nextValueId = base + 3 * (j + 1) := by rw [hnext2]; omega
        rwa [hn] at h
      have hlanes3 : ∀ k, (trustIrListGet? vecLanes ((j + 1) + k))
          = ((trustIrListGet? rest k)).map (fun i => Value.int w i) := by
        intro k
        have h := hlanes (k + 1)
        simp only [trustIrListGetConsSucc] at h
        rw [show (j + 1) + k = j + (k + 1) by omega]; exact h
      obtain ⟨s4, hrun4, hnext4, hmem4, hperm4, href4, hacc4⟩ :=
        ih S3 (j + 1) (reduceStep kind w A lane) hpres3 hnext3 hacc3 hlanes3
      refine ⟨s4, hrun4, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext4]; simp only [List.length_cons]; omega
      · rw [hmem4, ← hS3, ← hS2]; simp
      · rw [hperm4, ← hS3, ← hS2]; simp
      · rw [href4, ← hS3, ← hS2]; simp
      · have hidxeq : j + (lane :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq]
        exact hacc4
  }

/-!
## Refinement Lemma: vector.reduce

Discharged with a genuine proof (no axiom or proof placeholder):
`runsAgreeFrom_reduce` establishes dialect/lowering agreement against the
faithful, fresh-id-threaded `lowerReduceFrom` (a zero-seed `Const` — the
fold identity for both kinds — followed by the per-lane
`ExtractElement`/`BinOp` fold chain), using the induction core
`run_reduceLoopFrom`. The shape/width characterisation hypotheses pin the
bounded executable lane type and hold by `rfl` at the supported shapes
(`<4 x i32>`, `<2 x i64>`; see the corollaries below); `hdom` is the
well-typed-operands refinement precondition, exactly as for
`pack_lanes`/`mask_to_bits`.
-/

/-- **Faithful refinement of `vector.reduce`.** The dialect denotation
    (`runReduce`, an identity-seeded left fold over the integer lanes) and the
    base-threaded lowering `lowerReduceFrom` agree on every state in the
    refinement domain (`hdom`: the single operand is bound to an int lane
    vector of the declared lane count and width). -/
theorem runsAgreeFrom_reduce
    (op : DialectOpSem) (spec : ReduceSpec) (lenN w : Nat)
    (hRun : op.runOp = runSpec op.inst (.reduce spec))
    (hlanes : spec.lanes = lenN)
    (hbw : spec.elemTy.bitWidth = some w)
    (hrw : resultWidth spec.elemTy = w)
    (hcharVec : ∀ ls : List Value, spec.vectorTy.executableVectorPayloadMatches ls
        = (ls.length == lenN && ls.all (Value.isIntWidth w)))
    (hcharLane : ∀ ls : List Value, spec.elemTy.executableVectorLanePayloadMatches ls
        = (ls.length == lenN && ls.all (Value.isIntWidth w)))
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
        ∃ (vecId : ValueId) (vals : List Int),
          op.inst.operands = [vecId] ∧
          s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int w i))) ∧
          vals.length = lenN) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerReduceFrom spec.elemTy spec.kind ((trustIrVectorGet! op.inst.operands 0))
        spec.lanes base) := by
  trustIrCompilerProof {
    intro s hdomS
    obtain ⟨vecId, vals, hops, hvecVal, hvalsLen⟩ := hdom s hdomS
    have hvecDom : vecId.index < s.nextValueId :=
      hdomS vecId (by rw [hops]; exact trustIrListMemConsSelf vecId [])
    have hget : (trustIrVectorGet! op.inst.operands 0) = vecId := by rw [hops]; rfl
    have hall : (vals.map (fun i => Value.int w i)).all (Value.isIntWidth w) = true :=
      all_map_int_isIntWidth w vals
    -- The dialect's vector-shape gate holds on the well-typed payload.
    have hpayVec : spec.vectorTy.executableVectorPayloadMatches
        (vals.map (fun i => Value.int w i)) = true := by
      rw [hcharVec, List.length_map, hvalsLen, beq_self_eq_true, Bool.true_and]
      exact hall
    -- The lane payload hypothesis required by the extract steps.
    have hpayLane : spec.elemTy.executableVectorLanePayloadMatches
        (vals.map (fun i => Value.int w i)) = true := by
      rw [hcharLane, List.length_map, hvalsLen, beq_self_eq_true, Bool.true_and]
      exact hall
    have hInteger : spec.elemTy.isInteger = true := by
      cases ht : spec.elemTy <;> first
        | rfl
        | (simp [ht, Ty.executableVectorLanePayloadMatches, Ty.executableIntLane?] at hpayLane; done)
        | (cases vals <;> simp [ht, Ty.executableVectorLanePayloadMatches,
            Ty.executableIntLane?, Value.isBool] at hpayLane)
    -- The dialect fold on the mapped payload is exactly `reduceInts`.
    have hfold : reduceAux spec.kind w (vals.map (fun i => Value.int w i)) 0
        = .ok (reduceInts spec.kind w vals 0) :=
      reduceAux_map spec.kind w w vals 0
    -- The dialect takes its success path, binding the folded scalar.
    have hrunOk : op.runOp s
        = .ok (bindFreshValue s (.int w (reduceInts spec.kind w vals 0))) := by
      rw [hRun]
      simp only [runSpec, runReduce, hops, hvecVal, hpayVec, hrw, hfold,
        bind, Except.bind, pure, Except.pure, if_true]
    -- The lowering: step the seed const, then run the fold chain at j = 0.
    have hC0 : Sem.run (stepInst (.Const spec.elemTy (.int 0))) s
        = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w 0)) :=
      run_stepConstInt spec.elemTy 0 w s hbw hInteger (Int.le_refl 0) (two_pow_pos_int w)
    -- Hypotheses for the induction core, entering the loop with counter `base + 1`.
    have hpres0 : ∀ id : ValueId, id.index < s.nextValueId →
        (bindOne s (.int w 0)).lookupValue id = s.lookupValue id := fun id hid =>
      lookup_bindOne_below s (.int w 0) id s.nextValueId hid (Nat.le_refl _)
    have hnext0 : (bindOne s (.int w 0)).nextValueId = s.nextValueId + 1 + 3 * 0 := by
      rw [bindOne_nextValueId]
    have hacc0 : (bindOne s (.int w 0)).lookupValue (ValueId.mk (s.nextValueId + 3 * 0))
        = some (.int w 0) := by
      simpa using lookup_bindOne_self s (.int w 0)
    have hlanes0 : ∀ k, (trustIrListGet? (vals.map (fun i => Value.int w i)) (0 + k))
        = ((trustIrListGet? vals k)).map (fun i => Value.int w i) := by
      intro k; simp only [Nat.zero_add, List.get?_map]
    obtain ⟨s2, hrun2, hnext2, hmem2, hperm2, href2, hacc2⟩ :=
      run_reduceLoopFrom spec.elemTy w spec.kind vecId s.nextValueId
        (vals.map (fun i => Value.int w i)) s hbw hpayLane hvecDom hvecVal
        vals (bindOne s (.int w 0)) 0 0
        hpres0 hnext0 hacc0 hlanes0
    rw [hrunOk]
    refine ⟨(), s2, ?_, ?_, .int w (reduceInts spec.kind w vals 0),
      .int w (reduceInts spec.kind w vals 0), ?_, ?_, rfl⟩
    · -- the full lowering run
      show Sem.run (runInsts (lowerReduceFrom spec.elemTy spec.kind
        ((trustIrVectorGet! op.inst.operands 0)) spec.lanes s.nextValueId)) s = .ok ((), s2)
      rw [hget]
      unfold lowerReduceFrom
      rw [runInsts_cons_value _ _ _ _ _ hC0, hlanes, ← hvalsLen]
      exact hrun2
    · -- state agreement (memory / permissions / refcounts)
      show state_equiv_except_locals
        (bindOne s (.int w (reduceInts spec.kind w vals 0))) s2
      refine ⟨?_, ?_, ?_⟩
      · rw [hmem2]; simp
      · rw [hperm2]; simp
      · rw [href2]; simp
    · -- dialect result value at the final fresh id
      show (bindOne s (.int w (reduceInts spec.kind w vals 0))).lookupValue
        (ValueId.mk ((bindOne s (.int w (reduceInts spec.kind w vals 0))).nextValueId - 1))
        = some (.int w (reduceInts spec.kind w vals 0))
      have hn1 : (bindOne s (.int w (reduceInts spec.kind w vals 0))).nextValueId - 1
          = s.nextValueId := by rw [bindOne_nextValueId]; omega
      rw [hn1]; exact lookup_bindOne_self s _
    · -- lowering result value, identical to the dialect's
      have hid : s2.nextValueId - 1 = s.nextValueId + 3 * (0 + vals.length) := by
        rw [hnext2]; omega
      rw [hid]; exact hacc2
  } {
    intro s hdomS
    obtain ⟨vecId, vals, hops, hvecVal, hvalsLen⟩ := hdom s hdomS
    have hvecDom : vecId.index < s.nextValueId :=
      hdomS vecId (by rw [hops]; exact trustIrListMemConsSelf vecId [])
    have hget : (trustIrVectorGet! op.inst.operands 0) = vecId := by rw [hops]; rfl
    have hall : (vals.map (fun i => Value.int w i)).all (Value.isIntWidth w) = true :=
      all_map_int_isIntWidth w vals
    -- The dialect's vector-shape gate holds on the well-typed payload.
    have hpayVec : spec.vectorTy.executableVectorPayloadMatches
        (vals.map (fun i => Value.int w i)) = true := by
      rw [hcharVec, List.length_map, hvalsLen, beq_self_eq_true, Bool.true_and]
      exact hall
    -- The lane payload hypothesis required by the extract steps.
    have hpayLane : spec.elemTy.executableVectorLanePayloadMatches
        (vals.map (fun i => Value.int w i)) = true := by
      rw [hcharLane, List.length_map, hvalsLen, beq_self_eq_true, Bool.true_and]
      exact hall
    have hInteger : spec.elemTy.isInteger = true := by
      cases ht : spec.elemTy <;> first
        | rfl
        | (simp [ht, Ty.executableVectorLanePayloadMatches, Ty.executableIntLane?] at hpayLane; done)
        | (cases vals <;> simp [ht, Ty.executableVectorLanePayloadMatches,
            Ty.executableIntLane?, Value.isBool] at hpayLane)
    -- The dialect fold on the mapped payload is exactly `reduceInts`.
    have hfold : reduceAux spec.kind w (vals.map (fun i => Value.int w i)) 0
        = .ok (reduceInts spec.kind w vals 0) :=
      reduceAux_map spec.kind w w vals 0
    -- The dialect takes its success path, binding the folded scalar.
    have hrunOk : op.runOp s
        = .ok (bindFreshValue s (.int w (reduceInts spec.kind w vals 0))) := by
      rw [hRun]
      simp only [runSpec, runReduce, hops, hvecVal, hpayVec, hrw, hfold,
        bind, Except.bind, pure, Except.pure, if_true]
    -- The lowering: step the seed const, then run the fold chain at j = 0.
    have hC0 : Sem.run (stepInst (.Const spec.elemTy (.int 0))) s
        = .ok (.value (some (ValueId.mk s.nextValueId)), bindOne s (.int w 0)) :=
      run_stepConstInt spec.elemTy 0 w s hbw hInteger (Int.le_refl 0) (two_pow_pos_int w)
    -- Hypotheses for the induction core, entering the loop with counter `base + 1`.
    have hpres0 : ∀ id : ValueId, id.index < s.nextValueId →
        (bindOne s (.int w 0)).lookupValue id = s.lookupValue id := fun id hid =>
      lookup_bindOne_below s (.int w 0) id s.nextValueId hid (Nat.le_refl _)
    have hnext0 : (bindOne s (.int w 0)).nextValueId = s.nextValueId + 1 + 3 * 0 := by
      rw [bindOne_nextValueId]
    have hacc0 : (bindOne s (.int w 0)).lookupValue (ValueId.mk (s.nextValueId + 3 * 0))
        = some (.int w 0) := by
      simpa using lookup_bindOne_self s (.int w 0)
    have hlanes0 : ∀ k, (trustIrListGet? (vals.map (fun i => Value.int w i)) (0 + k))
        = ((trustIrListGet? vals k)).map (fun i => Value.int w i) := by
      intro k; simp only [Nat.zero_add, CompilerCompat.listGetConstructive_map]
    obtain ⟨s2, hrun2, hnext2, hmem2, hperm2, href2, hacc2⟩ :=
      run_reduceLoopFrom spec.elemTy w spec.kind vecId s.nextValueId
        (vals.map (fun i => Value.int w i)) s hbw hpayLane hvecDom hvecVal
        vals (bindOne s (.int w 0)) 0 0
        hpres0 hnext0 hacc0 hlanes0
    rw [hrunOk]
    refine ⟨(), s2, ?_, ?_, .int w (reduceInts spec.kind w vals 0),
      .int w (reduceInts spec.kind w vals 0), ?_, ?_, rfl⟩
    · -- the full lowering run
      show Sem.run (runInsts (lowerReduceFrom spec.elemTy spec.kind
        ((trustIrVectorGet! op.inst.operands 0)) spec.lanes s.nextValueId)) s = .ok ((), s2)
      rw [hget]
      unfold lowerReduceFrom
      rw [runInsts_cons_value _ _ _ _ _ hC0, hlanes, ← hvalsLen]
      exact hrun2
    · -- state agreement (memory / permissions / refcounts)
      show state_equiv_except_locals
        (bindOne s (.int w (reduceInts spec.kind w vals 0))) s2
      refine ⟨?_, ?_, ?_⟩
      · rw [hmem2]; simp
      · rw [hperm2]; simp
      · rw [href2]; simp
    · -- dialect result value at the final fresh id
      show (bindOne s (.int w (reduceInts spec.kind w vals 0))).lookupValue
        (ValueId.mk ((bindOne s (.int w (reduceInts spec.kind w vals 0))).nextValueId - 1))
        = some (.int w (reduceInts spec.kind w vals 0))
      have hn1 : (bindOne s (.int w (reduceInts spec.kind w vals 0))).nextValueId - 1
          = s.nextValueId := by rw [bindOne_nextValueId]; omega
      rw [hn1]; exact lookup_bindOne_self s _
    · -- lowering result value, identical to the dialect's
      have hid : s2.nextValueId - 1 = s.nextValueId + 3 * (0 + vals.length) := by
        rw [hnext2]; omega
      rw [hid]; exact hacc2
  }

/-- `<4 x i32>` instance of `runsAgreeFrom_reduce` (both kinds): every shape
    and width hypothesis discharges by `rfl`, leaving only the genuine
    refinement-domain precondition `hdom`. Witnesses non-vacuity at a
    supported vector shape. -/
theorem runsAgreeFrom_reduce_v4i32
    (op : DialectOpSem) (spec : ReduceSpec)
    (hRun : op.runOp = runSpec op.inst (.reduce spec))
    (hvec : spec.vectorTy = .Vector 4 .I32)
    (helem : spec.elemTy = .I32)
    (hlanes : spec.lanes = 4)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
        ∃ (vecId : ValueId) (vals : List Int),
          op.inst.operands = [vecId] ∧
          s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int 32 i))) ∧
          vals.length = 4) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerReduceFrom spec.elemTy spec.kind ((trustIrVectorGet! op.inst.operands 0))
        spec.lanes base) :=
  runsAgreeFrom_reduce op spec 4 32 hRun hlanes
    (by rw [helem]; rfl) (by rw [helem]; rfl)
    (fun ls => by rw [hvec]; rfl) (fun ls => by rw [helem]; rfl) hdom

/-- `<2 x i64>` instance of `runsAgreeFrom_reduce`; companion to the
    `<4 x i32>` corollary above. -/
theorem runsAgreeFrom_reduce_v2i64
    (op : DialectOpSem) (spec : ReduceSpec)
    (hRun : op.runOp = runSpec op.inst (.reduce spec))
    (hvec : spec.vectorTy = .Vector 2 .I64)
    (helem : spec.elemTy = .I64)
    (hlanes : spec.lanes = 2)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
        ∃ (vecId : ValueId) (vals : List Int),
          op.inst.operands = [vecId] ∧
          s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int 64 i))) ∧
          vals.length = 2) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerReduceFrom spec.elemTy spec.kind ((trustIrVectorGet! op.inst.operands 0))
        spec.lanes base) :=
  runsAgreeFrom_reduce op spec 2 64 hRun hlanes
    (by rw [helem]; rfl) (by rw [helem]; rfl)
    (fun ls => by rw [hvec]; rfl) (fun ls => by rw [helem]; rfl) hdom

/-- Mapping the `Const`→`Value` lane coercion over an all-zero `Int` constant
    seed yields the all-zero `Int w` lane list. The pack-lanes zero seed
    `Const (.vector (replicate lanes (.int 0)))` therefore decodes to an
    `executableVectorPayloadMatches`-good zero vector. -/
theorem map_replicate_int_zero (elemTy : Ty) (m w : Nat) :
    ((List.replicate m (Constant.int 0)).map (fun c => match c with
      | .int i => Value.intAt w i | other => constValueAt elemTy other))
      = List.replicate m (Value.int w 0) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    show (Value.intAt w 0) :: ((List.replicate k (Constant.int 0)).map _)
      = (Value.int w 0) :: List.replicate k (Value.int w 0)
    rw [ih, intAt_zero]

/-!
## Faithful base-threaded lowering for `vector.shuffle`

`shuffleInsertsFrom` is the SSA-allocator-threaded refinement of the
production Rust pass (`lower_shuffle`): starting from a freshly-built zero
vector at `ValueId.mk base`, it emits, for each result lane `j` with source
index `indices[j]`, a source-index `Const`, an `ExtractElement` from the
ORIGINAL source vector (never overwritten — the chain binds only fresh ids),
a destination-index `Const`, and an `InsertElement` into the running result
vector. The *j*-th block binds:

* `base + 1 + 4*j` — the source-index constant (`i64 indices[j]`),
* `base + 2 + 4*j` — the extracted source lane,
* `base + 3 + 4*j` — the destination-index constant (`i64 j`),
* `base + 4 + 4*j` — the updated vector (`= base + 4*(j+1)`),

so the running vector feeding lane `j` is uniformly at `base + 4*j`
(`= base` = the zero seed for `j = 0`). These are exactly the ids
`MachineState.bindValue` hands out when execution reaches the loop with
`nextValueId = base + 1`. -/

/-- Cons-decomposition for a successful `shuffleGather`: the head index
    resolves in the source vector and the tail gathers successfully.
    Companion to `lookupOperands_cons`. -/
theorem shuffleGather_cons {vecLanes : List Value} {src : Nat} {rest : List Nat}
    {gvals : List Value}
    (h : shuffleGather vecLanes (src :: rest) = .ok gvals) :
    ∃ v grest, gvals = v :: grest ∧ (trustIrListGet? vecLanes src) = some v ∧
               shuffleGather vecLanes rest = .ok grest := by
  unfold shuffleGather at h
  cases hl : (trustIrListGet? vecLanes src) with
  | none => rw [hl] at h; simp [ub] at h
  | some v =>
    rw [hl] at h
    simp only [bind, Except.bind] at h
    cases hr : shuffleGather vecLanes rest with
    | error e => rw [hr] at h; simp at h
    | ok grest =>
      rw [hr] at h
      simp only [Except.bind] at h
      exact ⟨v, grest, by injection h with h'; exact h'.symm, rfl, rfl⟩

/-- In-range indices always gather: totality of `shuffleGather` on the
    refinement domain (the decoder range-checks every index). -/
theorem shuffleGather_ok_of_lt (vecLanes : List Value) :
    ∀ (idxs : List Nat), (∀ i ∈ idxs, i < vecLanes.length) →
    ∃ gvals, shuffleGather vecLanes idxs = .ok gvals ∧ gvals.length = idxs.length := by
  trustIrCompilerProof {
    intro idxs
    induction idxs with
    | nil => intro _; exact ⟨[], rfl, rfl⟩
    | cons src rest ih =>
      intro hlt
      obtain ⟨grest, hg, hlen⟩ := ih (fun i hi => hlt i (List.mem_cons_of_mem src hi))
      have hsrc : src < vecLanes.length := hlt src (trustIrListMemConsSelf src rest)
      refine ⟨vecLanes.get ⟨src, hsrc⟩ :: grest, ?_, by simp [hlen]⟩
      unfold shuffleGather
      rw [List.get?_eq_get hsrc, hg]
      rfl
  } {
    intro idxs
    induction idxs with
    | nil => intro _; exact ⟨[], rfl, rfl⟩
    | cons src rest ih =>
      intro hlt
      obtain ⟨grest, hg, hlen⟩ := ih (fun i hi => hlt i (List.mem_cons_of_mem src hi))
      have hsrc : src < vecLanes.length := hlt src (trustIrListMemConsSelf src rest)
      refine ⟨vecLanes.get ⟨src, hsrc⟩ :: grest, ?_, by simp [hlen]⟩
      unfold shuffleGather
      rw [CompilerCompat.listGet?_eq_get hsrc, hg]
      rfl
  }

/-- A positional lookup out of an `all`-true payload satisfies the predicate. -/
theorem all_get?_of_all {P : Value → Bool} :
    ∀ {lanes : List Value} {i : Nat} {v : Value},
      lanes.all P = true → (trustIrListGet? lanes i) = some v → P v = true := by
  trustIrCompilerProof {
    intro lanes
    induction lanes with
    | nil => intro i v _ h; rw [List.get?_nil] at h; cases h
    | cons a t ih =>
      intro i v hall hget
      rw [List.all_cons, Bool.and_eq_true] at hall
      cases i with
      | zero =>
        rw [trustIrListGetConsZero, Option.some.injEq] at hget
        rw [← hget]
        exact hall.1
      | succ k =>
        rw [trustIrListGetConsSucc] at hget
        exact ih hall.2 hget
  } {
    intro lanes
    induction lanes with
    | nil => intro i v _ h; rw [CompilerCompat.listGetConstructive_nil] at h; cases h
    | cons a t ih =>
      intro i v hall hget
      rw [List.all_cons, Bool.and_eq_true] at hall
      cases i with
      | zero =>
        rw [trustIrListGetConsZero, Option.some.injEq] at hget
        rw [← hget]
        exact hall.1
      | succ k =>
        rw [trustIrListGetConsSucc] at hget
        exact ih hall.2 hget
  }

/-- The all-zero seed payload is width-good in every lane. -/
theorem all_replicate_int_isIntWidth (m w : Nat) :
    (List.replicate m (Value.int w 0)).all (Value.isIntWidth w) = true := by
  induction m with
  | zero => rfl
  | succ k ih =>
    show ((Value.int w 0) :: List.replicate k (Value.int w 0)).all (Value.isIntWidth w) = true
    rw [List.all_cons, ih, Bool.and_true]
    simp [Value.isIntWidth]

/-- Base-threaded per-lane chain of the Rust `lower_shuffle`: source-index
    `Const`, source-lane `ExtractElement`, destination-index `Const`, and the
    running-vector `InsertElement`. -/
def shuffleInsertsFrom (vt elemTy : Ty) (vecId : ValueId) (base : Nat) :
    Nat → List Nat → List Inst
  | _, [] => []
  | j, src :: rest =>
    Inst.Const .I64 (.int (Int.ofNat src)) ::
    Inst.ExtractElement elemTy vecId (ValueId.mk (base + 1 + 4 * j)) ::
    Inst.Const .I64 (.int (Int.ofNat j)) ::
    Inst.InsertElement vt (ValueId.mk (base + 4 * j)) (ValueId.mk (base + 3 + 4 * j))
      (ValueId.mk (base + 2 + 4 * j)) ::
    shuffleInsertsFrom vt elemTy vecId base (j + 1) rest

/-- The full shuffle lowering: build a zero seed vector (every lane is
    subsequently overwritten — the sequence carries no undef/poison value),
    then chain the per-lane extract/insert blocks. Matches the Rust
    `lower_shuffle` emission exactly. -/
def lowerShuffleFrom (vt elemTy : Ty) (vecId : ValueId) (indices : List Nat)
    (lanes : Nat) (base : Nat) : List Inst :=
  Inst.Const vt (.vector (List.replicate lanes (.int 0))) ::
  shuffleInsertsFrom vt elemTy vecId base 0 indices

/-- **Faithful refinement of `vector.shuffle` (induction core).** Running the
    per-lane extract/insert chain from a state whose allocator counter is
    exactly `base + 1 + 4*j`, with the running vector for the already-written
    prefix bound at `ValueId.mk (base + 4*j)` and the source vector readable
    at `vecId`, reproduces the dialect gather: the chain terminates, leaves
    memory/permissions/refcounts untouched, and binds
    `curLanes.take j ++ gvals` (the untouched prefix plus the gathered lanes)
    at the final fresh id. The genuine multi-lane generalisation combining
    `run_packInsertsFrom`'s insert-chain reasoning with the source-vector
    extract of `run_stepExtractElementLane`. -/
theorem run_shuffleInsertsFrom (n lenN w base : Nat) (elemTy : Ty)
    (vecId : ValueId) (vecLanes : List Value) (s0 : MachineState)
    (hchar : ∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
               = (ls.length == lenN && ls.all (Value.isIntWidth w)))
    (hlaneV : ∀ v : Value, elemTy.executableVectorLaneValueMatches v = Value.isIntWidth w v)
    (hpaySrc : Ty.executableVectorLanePayloadMatches elemTy vecLanes = true)
    (hallSrc : vecLanes.all (Value.isIntWidth w) = true)
    (hvecDom : vecId.index < base)
    (hvec0 : s0.lookupValue vecId = some (.vector vecLanes)) :
    ∀ (idxs : List Nat) (gvals : List Value) (s : MachineState)
      (j : Nat) (curLanes : List Value),
      shuffleGather vecLanes idxs = .ok gvals →
      (∀ id : ValueId, id.index < base → s.lookupValue id = s0.lookupValue id) →
      s.nextValueId = base + 1 + 4 * j →
      s.lookupValue (ValueId.mk (base + 4 * j)) = some (.vector curLanes) →
      (Ty.Vector n elemTy).executableVectorPayloadMatches curLanes = true →
      j + idxs.length = curLanes.length →
      ∃ s2 : MachineState,
        Sem.run (runInsts (shuffleInsertsFrom (Ty.Vector n elemTy) elemTy vecId base j idxs)) s
          = .ok ((), s2) ∧
        s2.nextValueId = base + 1 + 4 * (j + idxs.length) ∧
        s2.memory = s.memory ∧ s2.permissions = s.permissions ∧
        s2.refCounts = s.refCounts ∧
        s2.lookupValue (ValueId.mk (base + 4 * (j + idxs.length)))
          = some (.vector (curLanes.take j ++ gvals)) := by
  trustIrCompilerProof {
    -- A single fresh bind preserves any id strictly below the pre-state counter.
    have pres1 : ∀ (id : ValueId) (st : MachineState) (c : Value),
        id.index < st.nextValueId → (bindOne st c).lookupValue id = st.lookupValue id :=
      fun id st c h => lookup_bindOne_ne st c id (Nat.ne_of_lt h)
    intro idxs
    induction idxs with
    | nil =>
      intro gvals s j curLanes hgather _ hnext hcur _ hsum
      -- Empty gather: `gvals = []`, the chain is empty, the vector is untouched.
      have hg : gvals = [] := by
        simp only [shuffleGather, Except.ok.injEq] at hgather
        exact hgather.symm
      subst hg
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [shuffleInsertsFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · have hj : j = curLanes.length := by simpa using hsum
        have hjlen : curLanes.take j = curLanes := by rw [hj]; exact List.take_length curLanes
        simp only [List.length_nil, Nat.add_zero, List.append_nil, hjlen]
        exact hcur
    | cons src rest ih =>
      intro gvals s j curLanes hgather hpres hnext hcur hpay hsum
      obtain ⟨v, grest, rfl, hsrc, hgrest⟩ := shuffleGather_cons hgather
      have hPv : Value.isIntWidth w v = true := all_get?_of_all hallSrc hsrc
      have hlen : curLanes.length = lenN := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h
        exact Nat.eq_of_beq_eq_true h.1
      have hallP : curLanes.all (Value.isIntWidth w) = true := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h; exact h.2
      have hsum' : j + (rest.length + 1) = curLanes.length := by
        simpa [List.length_cons] using hsum
      have hk : j < curLanes.length := by omega
      have hunfold : shuffleInsertsFrom (Ty.Vector n elemTy) elemTy vecId base j (src :: rest)
          = Inst.Const .I64 (.int (Int.ofNat src))
            :: Inst.ExtractElement elemTy vecId (ValueId.mk (base + 1 + 4 * j))
            :: Inst.Const .I64 (.int (Int.ofNat j))
            :: Inst.InsertElement (Ty.Vector n elemTy) (ValueId.mk (base + 4 * j))
                 (ValueId.mk (base + 3 + 4 * j)) (ValueId.mk (base + 2 + 4 * j))
            :: shuffleInsertsFrom (Ty.Vector n elemTy) elemTy vecId base (j + 1) rest := rfl
      rw [hunfold]
      -- Step 1: source-index `Const` binds `i64 src` at `base + 1 + 4*j`.
      have hConstSrc : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat src)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat src))) :=
        run_stepConstInt .I64 (Int.ofNat src) 64 s rfl i64_is_integer (Int.ofNat_nonneg src)
          (lane_index_lt_two_pow_64 (by
            have := lt_length_of_get?_some hsrc
            have := executableVectorLanePayloadMatches_length_le hpaySrc
            omega))
      rw [runInsts_cons_value _ _ _ _ _ hConstSrc]
      -- Step 2: `ExtractElement` reads source lane `src`.
      have harr1 : (bindOne s (.int 64 (Int.ofNat src))).lookupValue vecId
          = some (.vector vecLanes) := by
        rw [pres1 vecId s _ (by rw [hnext]; omega), hpres vecId hvecDom]
        exact hvec0
      have hidx1 : (bindOne s (.int 64 (Int.ofNat src))).lookupValue
          (ValueId.mk (base + 1 + 4 * j)) = some (.int 64 (Int.ofNat src)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat src)); rwa [hnext] at h
      have hExtract := run_stepExtractElementLane elemTy vecId (ValueId.mk (base + 1 + 4 * j))
        (bindOne s (.int 64 (Int.ofNat src))) vecLanes src v harr1 hidx1 hpaySrc hsrc
      have hnext1 : (bindOne s (.int 64 (Int.ofNat src))).nextValueId = base + 2 + 4 * j := by
        rw [bindOne_nextValueId, hnext]; omega
      rw [hnext1] at hExtract
      rw [runInsts_cons_value _ _ _ _ _ hExtract]
      -- Step 3: destination-index `Const` binds `i64 j` at `base + 3 + 4*j`.
      generalize hS2 : bindOne (bindOne s (.int 64 (Int.ofNat src))) v = S2
      have hConstDst : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat j)))) S2
          = .ok (.value (some (ValueId.mk S2.nextValueId)),
                 bindOne S2 (.int 64 (Int.ofNat j))) :=
        run_stepConstInt .I64 (Int.ofNat j) 64 S2 rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 (by
            have := executableVectorPayloadMatches_length_le hpay; omega))
      have hnext2 : S2.nextValueId = base + 3 + 4 * j := by
        rw [← hS2]; simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext2] at hConstDst
      rw [runInsts_cons_value _ _ _ _ _ hConstDst]
      -- Step 4: `InsertElement` writes the gathered lane into result lane `j`.
      generalize hS3 : bindOne S2 (Value.int 64 (Int.ofNat j)) = S3
      have hcur3 : S3.lookupValue (ValueId.mk (base + 4 * j)) = some (.vector curLanes) := by
        rw [← hS3, pres1 _ _ _ (by simp only [hnext2]; omega), ← hS2,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hcur
      have hidx3 : S3.lookupValue (ValueId.mk (base + 3 + 4 * j))
          = some (.int 64 (Int.ofNat j)) := by
        rw [← hS3]
        have h := lookup_bindOne_self S2 (Value.int 64 (Int.ofNat j))
        rwa [hnext2] at h
      have hval3 : S3.lookupValue (ValueId.mk (base + 2 + 4 * j)) = some v := by
        rw [← hS3, pres1 _ _ _ (by simp only [hnext2]; omega), ← hS2]
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat src))) v
        rwa [hnext1] at h
      have hlaneOk : elemTy.executableVectorLaneValueMatches v = true := by
        rw [hlaneV]; exact hPv
      have hInsert := run_stepInsertElementVec n elemTy (ValueId.mk (base + 4 * j))
        (ValueId.mk (base + 3 + 4 * j)) (ValueId.mk (base + 2 + 4 * j)) S3
        curLanes j v hcur3 hidx3 hval3 hpay hlaneOk hk
      have hnext3 : S3.nextValueId = base + 4 + 4 * j := by
        rw [← hS3]; simp only [bindOne_nextValueId, hnext2]; omega
      rw [hnext3] at hInsert
      rw [runInsts_cons_value _ _ _ _ _ hInsert]
      -- Recurse on the remaining lanes from the post-insert state.
      generalize hS4 : bindOne S3 (.vector (curLanes.set j v)) = S4
      have hpres4 : ∀ id : ValueId, id.index < base → S4.lookupValue id = s0.lookupValue id := by
        intro id hid
        rw [← hS4, pres1 _ _ _ (by rw [hnext3]; omega), ← hS3,
            pres1 _ _ _ (by rw [hnext2]; omega), ← hS2,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by rw [hnext]; omega)]
        exact hpres id hid
      have hnext4 : S4.nextValueId = base + 1 + 4 * (j + 1) := by
        rw [← hS4]; simp only [bindOne_nextValueId, hnext3]; omega
      have hcur4 : S4.lookupValue (ValueId.mk (base + 4 * (j + 1)))
          = some (.vector (curLanes.set j v)) := by
        rw [← hS4]
        have h := lookup_bindOne_self S3 (.vector (curLanes.set j v))
        have hn : S3.nextValueId = base + 4 * (j + 1) := by rw [hnext3]; omega
        rwa [hn] at h
      have hpay4 : (Ty.Vector n elemTy).executableVectorPayloadMatches (curLanes.set j v)
          = true := by
        rw [hchar, Bool.and_eq_true]
        refine ⟨?_, all_set_of_all hallP hPv⟩
        simp [List.length_set, hlen]
      have hsum4 : (j + 1) + rest.length = (curLanes.set j v).length := by
        rw [List.length_set]; omega
      obtain ⟨s5, hrun5, hnext5, hmem5, hperm5, href5, hvec5⟩ :=
        ih grest S4 (j + 1) (curLanes.set j v) hgrest hpres4 hnext4 hcur4 hpay4 hsum4
      refine ⟨s5, hrun5, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext5]; simp only [List.length_cons]; omega
      · rw [hmem5, ← hS4, ← hS3, ← hS2]; simp
      · rw [hperm5, ← hS4, ← hS3, ← hS2]; simp
      · rw [href5, ← hS4, ← hS3, ← hS2]; simp
      · have hidxeq : j + (src :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq, hvec5, take_succ_set curLanes j v hk, List.append_assoc,
            List.singleton_append]
  } {
    -- A single fresh bind preserves any id strictly below the pre-state counter.
    have pres1 : ∀ (id : ValueId) (st : MachineState) (c : Value),
        id.index < st.nextValueId → (bindOne st c).lookupValue id = st.lookupValue id :=
      fun id st c h => lookup_bindOne_ne st c id (Nat.ne_of_lt h)
    intro idxs
    induction idxs with
    | nil =>
      intro gvals s j curLanes hgather _ hnext hcur _ hsum
      -- Empty gather: `gvals = []`, the chain is empty, the vector is untouched.
      have hg : gvals = [] := by
        simp only [shuffleGather, Except.ok.injEq] at hgather
        exact hgather.symm
      subst hg
      refine ⟨s, ?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp only [shuffleInsertsFrom, runInsts, Sem.run_pure]
      · simp only [List.length_nil, Nat.add_zero]; exact hnext
      · have hj : j = curLanes.length := by simpa using hsum
        have hjlen : curLanes.take j = curLanes := by rw [hj]; exact (List.take_length (l := curLanes))
        simp only [List.length_nil, Nat.add_zero, List.append_nil, hjlen]
        exact hcur
    | cons src rest ih =>
      intro gvals s j curLanes hgather hpres hnext hcur hpay hsum
      obtain ⟨v, grest, rfl, hsrc, hgrest⟩ := shuffleGather_cons hgather
      have hPv : Value.isIntWidth w v = true := all_get?_of_all hallSrc hsrc
      have hlen : curLanes.length = lenN := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h
        exact beq_iff_eq.mp h.1
      have hallP : curLanes.all (Value.isIntWidth w) = true := by
        have h := hpay; rw [hchar, Bool.and_eq_true] at h; exact h.2
      have hsum' : j + (rest.length + 1) = curLanes.length := by
        simpa [List.length_cons] using hsum
      have hk : j < curLanes.length := by omega
      have hunfold : shuffleInsertsFrom (Ty.Vector n elemTy) elemTy vecId base j (src :: rest)
          = Inst.Const .I64 (.int (Int.ofNat src))
            :: Inst.ExtractElement elemTy vecId (ValueId.mk (base + 1 + 4 * j))
            :: Inst.Const .I64 (.int (Int.ofNat j))
            :: Inst.InsertElement (Ty.Vector n elemTy) (ValueId.mk (base + 4 * j))
                 (ValueId.mk (base + 3 + 4 * j)) (ValueId.mk (base + 2 + 4 * j))
            :: shuffleInsertsFrom (Ty.Vector n elemTy) elemTy vecId base (j + 1) rest := rfl
      rw [hunfold]
      -- Step 1: source-index `Const` binds `i64 src` at `base + 1 + 4*j`.
      have hConstSrc : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat src)))) s
          = .ok (.value (some (ValueId.mk s.nextValueId)),
                 bindOne s (.int 64 (Int.ofNat src))) :=
        run_stepConstInt .I64 (Int.ofNat src) 64 s rfl i64_is_integer (Int.ofNat_nonneg src)
          (lane_index_lt_two_pow_64 (by
            have := lt_length_of_get?_some hsrc
            have := executableVectorLanePayloadMatches_length_le hpaySrc
            omega))
      rw [runInsts_cons_value _ _ _ _ _ hConstSrc]
      -- Step 2: `ExtractElement` reads source lane `src`.
      have harr1 : (bindOne s (.int 64 (Int.ofNat src))).lookupValue vecId
          = some (.vector vecLanes) := by
        rw [pres1 vecId s _ (by rw [hnext]; omega), hpres vecId hvecDom]
        exact hvec0
      have hidx1 : (bindOne s (.int 64 (Int.ofNat src))).lookupValue
          (ValueId.mk (base + 1 + 4 * j)) = some (.int 64 (Int.ofNat src)) := by
        have h := lookup_bindOne_self s (.int 64 (Int.ofNat src)); rwa [hnext] at h
      have hExtract := run_stepExtractElementLane elemTy vecId (ValueId.mk (base + 1 + 4 * j))
        (bindOne s (.int 64 (Int.ofNat src))) vecLanes src v harr1 hidx1 hpaySrc hsrc
      have hnext1 : (bindOne s (.int 64 (Int.ofNat src))).nextValueId = base + 2 + 4 * j := by
        rw [bindOne_nextValueId, hnext]; omega
      rw [hnext1] at hExtract
      rw [runInsts_cons_value _ _ _ _ _ hExtract]
      -- Step 3: destination-index `Const` binds `i64 j` at `base + 3 + 4*j`.
      generalize hS2 : bindOne (bindOne s (.int 64 (Int.ofNat src))) v = S2
      have hConstDst : Sem.run (stepInst (.Const .I64 (.int (Int.ofNat j)))) S2
          = .ok (.value (some (ValueId.mk S2.nextValueId)),
                 bindOne S2 (.int 64 (Int.ofNat j))) :=
        run_stepConstInt .I64 (Int.ofNat j) 64 S2 rfl i64_is_integer (Int.ofNat_nonneg j)
          (lane_index_lt_two_pow_64 (by
            have := executableVectorPayloadMatches_length_le hpay; omega))
      have hnext2 : S2.nextValueId = base + 3 + 4 * j := by
        rw [← hS2]; simp only [bindOne_nextValueId, hnext]; omega
      rw [hnext2] at hConstDst
      rw [runInsts_cons_value _ _ _ _ _ hConstDst]
      -- Step 4: `InsertElement` writes the gathered lane into result lane `j`.
      generalize hS3 : bindOne S2 (Value.int 64 (Int.ofNat j)) = S3
      have hcur3 : S3.lookupValue (ValueId.mk (base + 4 * j)) = some (.vector curLanes) := by
        rw [← hS3, pres1 _ _ _ (by simp only [hnext2]; omega), ← hS2,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by simp only [hnext]; omega)]
        exact hcur
      have hidx3 : S3.lookupValue (ValueId.mk (base + 3 + 4 * j))
          = some (.int 64 (Int.ofNat j)) := by
        rw [← hS3]
        have h := lookup_bindOne_self S2 (Value.int 64 (Int.ofNat j))
        rwa [hnext2] at h
      have hval3 : S3.lookupValue (ValueId.mk (base + 2 + 4 * j)) = some v := by
        rw [← hS3, pres1 _ _ _ (by simp only [hnext2]; omega), ← hS2]
        have h := lookup_bindOne_self (bindOne s (.int 64 (Int.ofNat src))) v
        rwa [hnext1] at h
      have hlaneOk : elemTy.executableVectorLaneValueMatches v = true := by
        rw [hlaneV]; exact hPv
      have hInsert := run_stepInsertElementVec n elemTy (ValueId.mk (base + 4 * j))
        (ValueId.mk (base + 3 + 4 * j)) (ValueId.mk (base + 2 + 4 * j)) S3
        curLanes j v hcur3 hidx3 hval3 hpay hlaneOk hk
      have hnext3 : S3.nextValueId = base + 4 + 4 * j := by
        rw [← hS3]; simp only [bindOne_nextValueId, hnext2]; omega
      rw [hnext3] at hInsert
      rw [runInsts_cons_value _ _ _ _ _ hInsert]
      -- Recurse on the remaining lanes from the post-insert state.
      generalize hS4 : bindOne S3 (.vector (curLanes.set j v)) = S4
      have hpres4 : ∀ id : ValueId, id.index < base → S4.lookupValue id = s0.lookupValue id := by
        intro id hid
        rw [← hS4, pres1 _ _ _ (by rw [hnext3]; omega), ← hS3,
            pres1 _ _ _ (by rw [hnext2]; omega), ← hS2,
            pres1 _ _ _ (by simp only [bindOne_nextValueId, hnext]; omega),
            pres1 _ _ _ (by rw [hnext]; omega)]
        exact hpres id hid
      have hnext4 : S4.nextValueId = base + 1 + 4 * (j + 1) := by
        rw [← hS4]; simp only [bindOne_nextValueId, hnext3]; omega
      have hcur4 : S4.lookupValue (ValueId.mk (base + 4 * (j + 1)))
          = some (.vector (curLanes.set j v)) := by
        rw [← hS4]
        have h := lookup_bindOne_self S3 (.vector (curLanes.set j v))
        have hn : S3.nextValueId = base + 4 * (j + 1) := by rw [hnext3]; omega
        rwa [hn] at h
      have hpay4 : (Ty.Vector n elemTy).executableVectorPayloadMatches (curLanes.set j v)
          = true := by
        rw [hchar, Bool.and_eq_true]
        refine ⟨?_, all_set_of_all hallP hPv⟩
        simp [List.length_set, hlen]
      have hsum4 : (j + 1) + rest.length = (curLanes.set j v).length := by
        rw [List.length_set]; omega
      obtain ⟨s5, hrun5, hnext5, hmem5, hperm5, href5, hvec5⟩ :=
        ih grest S4 (j + 1) (curLanes.set j v) hgrest hpres4 hnext4 hcur4 hpay4 hsum4
      refine ⟨s5, hrun5, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnext5]; simp only [List.length_cons]; omega
      · rw [hmem5, ← hS4, ← hS3, ← hS2]; simp
      · rw [hperm5, ← hS4, ← hS3, ← hS2]; simp
      · rw [href5, ← hS4, ← hS3, ← hS2]; simp
      · have hidxeq : j + (src :: rest).length = (j + 1) + rest.length := by
          simp only [List.length_cons]; omega
        rw [hidxeq, hvec5, take_succ_set curLanes j v hk, List.append_assoc,
            List.singleton_append]
  }

/-!
## Refinement Lemma: vector.shuffle

Discharged with a genuine proof (no axiom or proof placeholder):
`runsAgreeFrom_shuffle` establishes dialect/lowering agreement against the
faithful, fresh-id-threaded `lowerShuffleFrom` (a zero-seed `Const` followed
by the per-lane extract/insert chain), using the induction core
`run_shuffleInsertsFrom`. The shape hypotheses pin the bounded executable
lane type and hold by `rfl` at the supported shapes (`<4 x i32>`,
`<2 x i64>`; see the corollaries below); `hidxLen`/`hidxLt` are the
decoder-guaranteed index invariants; `hdom` is the well-typed-operands
refinement precondition.
-/

/-- **Faithful refinement of `vector.shuffle`.** The dialect denotation
    (`runShuffle`, a static gather across the source lanes) and the
    base-threaded lowering `lowerShuffleFrom` agree on every state in the
    refinement domain (`hdom`: the single operand is bound to an int lane
    vector of the declared lane count and width). -/
theorem runsAgreeFrom_shuffle
    (op : DialectOpSem) (spec : ShuffleSpec) (n lenN w : Nat) (elemTy : Ty)
    (hRun : op.runOp = runSpec op.inst (.shuffle spec))
    (helem : spec.elemTy = elemTy)
    (hvecTy : spec.vectorTy = Ty.Vector n elemTy)
    (hlanes : spec.lanes = lenN)
    (hbw : elemTy.bitWidth = some w)
    (hchar : ∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
        = (ls.length == lenN && ls.all (Value.isIntWidth w)))
    (hcharLane : ∀ ls : List Value, elemTy.executableVectorLanePayloadMatches ls
        = (ls.length == lenN && ls.all (Value.isIntWidth w)))
    (hlaneV : ∀ v : Value, elemTy.executableVectorLaneValueMatches v = Value.isIntWidth w v)
    (hidxLen : spec.indices.length = lenN)
    (hidxLt : ∀ i ∈ spec.indices, i < lenN)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
        ∃ (vecId : ValueId) (vals : List Int),
          op.inst.operands = [vecId] ∧
          s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int w i))) ∧
          vals.length = lenN) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerShuffleFrom spec.vectorTy spec.elemTy ((trustIrVectorGet! op.inst.operands 0))
        spec.indices spec.lanes base) := by
  intro s hdomS
  obtain ⟨vecId, vals, hops, hvecVal, hvalsLen⟩ := hdom s hdomS
  have hvecDom : vecId.index < s.nextValueId :=
    hdomS vecId (by rw [hops]; exact trustIrListMemConsSelf vecId [])
  have hget : (trustIrVectorGet! op.inst.operands 0) = vecId := by rw [hops]; rfl
  have hallSrc : (vals.map (fun i => Value.int w i)).all (Value.isIntWidth w) = true :=
    all_map_int_isIntWidth w vals
  have hpaySrc : elemTy.executableVectorLanePayloadMatches
      (vals.map (fun i => Value.int w i)) = true := by
    rw [hcharLane, List.length_map, hvalsLen, beq_self_eq_true, Bool.true_and]
    exact hallSrc
  -- The dialect's vector-shape gate holds on the well-typed payload.
  have hpayVec : spec.vectorTy.executableVectorPayloadMatches
      (vals.map (fun i => Value.int w i)) = true := by
    rw [hvecTy, hchar, List.length_map, hvalsLen, beq_self_eq_true, Bool.true_and]
    exact hallSrc
  -- The gather succeeds: every index is range-checked by the decoder.
  have hlenVec : (vals.map (fun i => Value.int w i)).length = lenN := by
    rw [List.length_map]; exact hvalsLen
  obtain ⟨gvals, hgather, hgvalsLen⟩ :=
    shuffleGather_ok_of_lt (vals.map (fun i => Value.int w i)) spec.indices
      (fun i hi => by rw [hlenVec]; exact hidxLt i hi)
  -- The dialect takes its success path, binding the gathered vector.
  have hrunOk : op.runOp s = .ok (bindFreshValue s (.vector gvals)) := by
    rw [hRun]
    simp only [runSpec, runShuffle, hops, hvecVal, hpayVec, hgather,
      bind, Except.bind, pure, Except.pure, if_true]
  -- The lowering: step the zero seed, then run the insert chain at j = 0.
  have hShape := executable_payload_shape n elemTy _ (by simpa only [hvecTy] using hpayVec)
  have hLenN : lenN = n := by simpa only [List.length_map, hvalsLen] using hShape.1
  have hInteger : elemTy.isInteger = true := by
    have h := hlaneV (.int w 0)
    cases elemTy <;> first
      | rfl
      | simp [Ty.executableVectorLaneValueMatches, Ty.executableIntLane?,
          Value.isIntWidth, Value.isBool] at h
  have hC0 : Sem.run (stepInst (.Const (.Vector n elemTy)
        (.vector (List.replicate lenN (.int 0))))) s
      = .ok (.value (some (ValueId.mk s.nextValueId)),
             bindOne s (.vector (List.replicate lenN (Value.int w 0)))) := by
    have h := run_stepConstVec n elemTy w (List.replicate lenN (.int 0)) s hbw
      hShape.2.1 (by simp [hLenN]) hShape.2.2
      (fun c hc => by
        have h : c = .int 0 := mem_replicate_constant_eq hc
        rw [h]
        exact .integer hInteger)
      (listHasSymbolAddr_replicate_int lenN 0)
    rwa [map_replicate_int_zero] at h
  have hpres0 : ∀ id : ValueId, id.index < s.nextValueId →
      (bindOne s (.vector (List.replicate lenN (Value.int w 0)))).lookupValue id
        = s.lookupValue id := fun id hid =>
    lookup_bindOne_below s _ id s.nextValueId hid (Nat.le_refl _)
  have hnext0 : (bindOne s (.vector (List.replicate lenN (Value.int w 0)))).nextValueId
      = s.nextValueId + 1 + 4 * 0 := by rw [bindOne_nextValueId]
  have hcur0 : (bindOne s (.vector (List.replicate lenN (Value.int w 0)))).lookupValue
      (ValueId.mk (s.nextValueId + 4 * 0))
      = some (.vector (List.replicate lenN (Value.int w 0))) := by
    simpa using lookup_bindOne_self s (.vector (List.replicate lenN (Value.int w 0)))
  have hpay0 : (Ty.Vector n elemTy).executableVectorPayloadMatches
      (List.replicate lenN (Value.int w 0)) = true := by
    rw [hchar, List.length_replicate, beq_self_eq_true, Bool.true_and]
    exact all_replicate_int_isIntWidth lenN w
  have hsum0 : 0 + spec.indices.length = (List.replicate lenN (Value.int w 0)).length := by
    rw [List.length_replicate, hidxLen]; omega
  obtain ⟨s2, hrun2, hnext2, hmem2, hperm2, href2, hvec2⟩ :=
    run_shuffleInsertsFrom n lenN w s.nextValueId elemTy vecId
      (vals.map (fun i => Value.int w i)) s hchar hlaneV hpaySrc hallSrc hvecDom hvecVal
      spec.indices gvals (bindOne s (.vector (List.replicate lenN (Value.int w 0)))) 0
      (List.replicate lenN (Value.int w 0))
      hgather hpres0 hnext0 hcur0 hpay0 hsum0
  rw [hrunOk]
  refine ⟨(), s2, ?_, ?_, .vector gvals, .vector gvals, ?_, ?_, rfl⟩
  · -- the full lowering run
    show Sem.run (runInsts (lowerShuffleFrom spec.vectorTy spec.elemTy
      ((trustIrVectorGet! op.inst.operands 0)) spec.indices spec.lanes s.nextValueId)) s = .ok ((), s2)
    rw [hget, hvecTy, helem, hlanes]
    unfold lowerShuffleFrom
    rw [runInsts_cons_value _ _ _ _ _ hC0]
    exact hrun2
  · -- state agreement (memory / permissions / refcounts)
    show state_equiv_except_locals (bindOne s (.vector gvals)) s2
    refine ⟨?_, ?_, ?_⟩
    · rw [hmem2]; simp
    · rw [hperm2]; simp
    · rw [href2]; simp
  · -- dialect result value at the final fresh id
    show (bindOne s (.vector gvals)).lookupValue
      (ValueId.mk ((bindOne s (.vector gvals)).nextValueId - 1)) = some (.vector gvals)
    have hn1 : (bindOne s (.vector gvals)).nextValueId - 1 = s.nextValueId := by
      rw [bindOne_nextValueId]; omega
    rw [hn1]; exact lookup_bindOne_self s _
  · -- lowering result value, identical to the dialect's
    have hid : s2.nextValueId - 1 = s.nextValueId + 4 * (0 + spec.indices.length) := by
      rw [hnext2]; omega
    rw [hid, hvec2, List.take_zero, List.nil_append]

/-- `<4 x i32>` instance of `runsAgreeFrom_shuffle`: every shape and width
    hypothesis discharges by `rfl`, leaving only the decoder-guaranteed index
    invariants and the genuine refinement-domain precondition `hdom`. -/
theorem runsAgreeFrom_shuffle_v4i32
    (op : DialectOpSem) (spec : ShuffleSpec)
    (hRun : op.runOp = runSpec op.inst (.shuffle spec))
    (helem : spec.elemTy = .I32)
    (hvec : spec.vectorTy = .Vector 4 .I32)
    (hlanes : spec.lanes = 4)
    (hidxLen : spec.indices.length = 4)
    (hidxLt : ∀ i ∈ spec.indices, i < 4)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
        ∃ (vecId : ValueId) (vals : List Int),
          op.inst.operands = [vecId] ∧
          s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int 32 i))) ∧
          vals.length = 4) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerShuffleFrom spec.vectorTy spec.elemTy ((trustIrVectorGet! op.inst.operands 0))
        spec.indices spec.lanes base) :=
  runsAgreeFrom_shuffle op spec 4 4 32 .I32 hRun helem hvec hlanes rfl
    (fun ls => rfl) (fun ls => rfl) (fun v => rfl) hidxLen hidxLt hdom

/-- `<2 x i64>` instance of `runsAgreeFrom_shuffle`; companion to the
    `<4 x i32>` corollary above. -/
theorem runsAgreeFrom_shuffle_v2i64
    (op : DialectOpSem) (spec : ShuffleSpec)
    (hRun : op.runOp = runSpec op.inst (.shuffle spec))
    (helem : spec.elemTy = .I64)
    (hvec : spec.vectorTy = .Vector 2 .I64)
    (hlanes : spec.lanes = 2)
    (hidxLen : spec.indices.length = 2)
    (hidxLt : ∀ i ∈ spec.indices, i < 2)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
        ∃ (vecId : ValueId) (vals : List Int),
          op.inst.operands = [vecId] ∧
          s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int 64 i))) ∧
          vals.length = 2) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerShuffleFrom spec.vectorTy spec.elemTy ((trustIrVectorGet! op.inst.operands 0))
        spec.indices spec.lanes base) :=
  runsAgreeFrom_shuffle op spec 2 2 64 .I64 hRun helem hvec hlanes rfl
    (fun ls => rfl) (fun ls => rfl) (fun v => rfl) hidxLen hidxLt hdom

/-!
## `DialectLowerSound`-style discharge for the Rust `VectorLoweringPass`

`vectorLowerFrom` is the *base-threaded* lowering selector: a function of the
runtime allocator counter (`base = s.nextValueId`) returning the exact core-IR
sequence the production Rust pass emits, for the ops that pass rewrites
(`pack_lanes`, `mask_to_bits`, `reduce`, `shuffle`). `vectorLowerFrom_sound` is the
`DialectLowerSound`-flavoured theorem: for any vector dialect op the pass
rewrites, in its refinement domain, the emitted sequence refines the dialect
denotation under `runsAgreeFrom` (equal-except-locals + result agreement — the
right relation for a fresh-id-allocating lowering; see the module header for why
the full-equality `TrustIr.DialectLowerSound` schema does not apply here). -/

/-- Base-threaded lowering for the ops the Rust `VectorLoweringPass`
    rewrites. `none` for the ops the pass leaves as dialect payloads
    (`extract_lane` / `insert_lane`, and `vector.fma` — deliberately never
    scalar-lowered: an unfused `FMul`+`FAdd` expansion double-rounds, see the
    ratified policy in docs/roadmap/fast-4-vector-crosslane-ops.md) or for
    non-vector / malformed ops. The emitted sequences match
    `lower_pack_lanes` / `lower_mask_to_bits` / `lower_reduce` /
    `lower_shuffle` exactly. -/
noncomputable def vectorLowerFrom (op : DialectOpSem) : Option (Nat → List Inst) :=
  if op.dialect = dialectName then
    match op.op with
    | "pack_lanes" =>
      match decodePackLanes op.inst with
      | .ok spec =>
        some (fun base => lowerPackLanesFrom spec.vectorTy
          (List.replicate spec.lanes (.int 0)) op.inst.operands base)
      | .error _ => none
    | "mask_to_bits" =>
      match decodeMaskToBits op.inst with
      | .ok spec =>
        some (fun base => lowerMaskToBitsFrom spec.resultTy ((trustIrVectorGet! op.inst.operands 0))
          spec.lanes base)
      | .error _ => none
    | "reduce" =>
      match decodeReduce op.inst with
      | .ok spec =>
        some (fun base => lowerReduceFrom spec.elemTy spec.kind ((trustIrVectorGet! op.inst.operands 0))
          spec.lanes base)
      | .error _ => none
    | "shuffle" =>
      match decodeShuffle op.inst with
      | .ok spec =>
        some (fun base => lowerShuffleFrom spec.vectorTy spec.elemTy
          ((trustIrVectorGet! op.inst.operands 0)) spec.indices spec.lanes base)
      | .error _ => none
    | _ => none
  else
    none

/-- **`DialectLowerSound`-style soundness of the Rust vector lowering
    (`pack_lanes`).** For a `vector.pack_lanes` op, the base-threaded lowering
    refines the dialect denotation on every state in the refinement domain
    (`<4 x i32>` / `<2 x i64>` packs; shape hypotheses discharge by
    `rfl`/`decide`). The conclusion's lowering is exactly the one
    `vectorLowerFrom` returns for this op (see `vectorLowerFrom_sound`). -/
theorem vectorLowerFrom_pack_lanes_sound
    (op : DialectOpSem) (spec : PackLanesSpec) (n lenN w : Nat) (elemTy : Ty)
    (P : Value → Bool)
    (hRun : op.runOp = runSpec op.inst (.packLanes spec))
    (helem : spec.elemTy = elemTy)
    (hlanes : spec.lanes = lenN)
    (hbw : elemTy.bitWidth = some w)
    (hchar : ∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
               = (decide (ls.length = lenN) && ls.all P))
    (hlaneP : ∀ v : Value, elemTy.executableVectorLaneValueMatches v = P v)
    (hseedLen : (List.replicate lenN (Value.int w 0)).length = lenN)
    (hseedP : (List.replicate lenN (Value.int w 0)).all P = true)
    (hdom : ∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
              ∃ vals, lookupOperands op.inst.operands s = .ok vals ∧
                      vals.length = lenN ∧ vals.all P = true) :
    runsAgreeFrom op op.inst.operands
      (fun base => lowerPackLanesFrom (Ty.Vector n elemTy)
        (List.replicate lenN (.int 0)) op.inst.operands base) :=
  runsAgreeFrom_pack_lanes op spec n lenN w elemTy P
    (List.replicate lenN (.int 0)) (List.replicate lenN (Value.int w 0))
    hRun helem hlanes hbw hchar hlaneP (map_replicate_int_zero elemTy lenN w) hseedLen hseedP hdom

/-- Per-op refinement obligation discharged at one of the supported shapes:
    a `pack_lanes` proof (with its shape/domain side conditions), a
    `mask_to_bits` proof, or a `reduce` proof. This is the disjunction the
    caller supplies; each branch concludes
    `runsAgreeFrom op op.inst.operands lower`. -/
def VectorOpRefines (op : DialectOpSem) (lower : Nat → List Inst) : Prop :=
  (∃ (spec : PackLanesSpec) (n lenN w : Nat) (elemTy : Ty) (P : Value → Bool),
      lower = (fun base => lowerPackLanesFrom (Ty.Vector n elemTy)
        (List.replicate lenN (.int 0)) op.inst.operands base) ∧
      op.runOp = runSpec op.inst (.packLanes spec) ∧
      spec.elemTy = elemTy ∧ spec.lanes = lenN ∧ elemTy.bitWidth = some w ∧
      (∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
          = (decide (ls.length = lenN) && ls.all P)) ∧
      (∀ v : Value, elemTy.executableVectorLaneValueMatches v = P v) ∧
      (List.replicate lenN (Value.int w 0)).length = lenN ∧
      (List.replicate lenN (Value.int w 0)).all P = true ∧
      (∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
          ∃ vals, lookupOperands op.inst.operands s = .ok vals ∧
                  vals.length = lenN ∧ vals.all P = true))
  ∨
  (∃ (spec : MaskToBitsSpec) (w : Nat),
      lower = (fun base => lowerMaskToBitsFrom spec.resultTy
        ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) ∧
      op.runOp = runSpec op.inst (.maskToBits spec) ∧
      spec.resultTy.bitWidth = some w ∧ spec.resultTy.isInteger = true ∧ resultWidth spec.resultTy = w ∧
      (spec.lanes = 16 ∨ spec.lanes = 8 ∨ spec.lanes = 4 ∨ spec.lanes = 2) ∧
      spec.lanes ≤ w ∧
      (∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
          ∃ (maskId : ValueId) (bits : List Bool),
            op.inst.operands = [maskId] ∧
            s.lookupValue maskId = some (.vector (bits.map (Value.bool ·))) ∧
            bits.length = spec.lanes))
  ∨
  (∃ (spec : ReduceSpec) (lenN w : Nat),
      lower = (fun base => lowerReduceFrom spec.elemTy spec.kind
        ((trustIrVectorGet! op.inst.operands 0)) spec.lanes base) ∧
      op.runOp = runSpec op.inst (.reduce spec) ∧
      spec.lanes = lenN ∧ spec.elemTy.bitWidth = some w ∧
      resultWidth spec.elemTy = w ∧
      (∀ ls : List Value, spec.vectorTy.executableVectorPayloadMatches ls
          = (ls.length == lenN && ls.all (Value.isIntWidth w))) ∧
      (∀ ls : List Value, spec.elemTy.executableVectorLanePayloadMatches ls
          = (ls.length == lenN && ls.all (Value.isIntWidth w))) ∧
      (∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
          ∃ (vecId : ValueId) (vals : List Int),
            op.inst.operands = [vecId] ∧
            s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int w i))) ∧
            vals.length = lenN))
  ∨
  (∃ (spec : ShuffleSpec) (n lenN w : Nat) (elemTy : Ty),
      lower = (fun base => lowerShuffleFrom spec.vectorTy spec.elemTy
        ((trustIrVectorGet! op.inst.operands 0)) spec.indices spec.lanes base) ∧
      op.runOp = runSpec op.inst (.shuffle spec) ∧
      spec.elemTy = elemTy ∧ spec.vectorTy = Ty.Vector n elemTy ∧
      spec.lanes = lenN ∧ elemTy.bitWidth = some w ∧
      (∀ ls : List Value, (Ty.Vector n elemTy).executableVectorPayloadMatches ls
          = (ls.length == lenN && ls.all (Value.isIntWidth w))) ∧
      (∀ ls : List Value, elemTy.executableVectorLanePayloadMatches ls
          = (ls.length == lenN && ls.all (Value.isIntWidth w))) ∧
      (∀ v : Value, elemTy.executableVectorLaneValueMatches v = Value.isIntWidth w v) ∧
      spec.indices.length = lenN ∧
      (∀ i ∈ spec.indices, i < lenN) ∧
      (∀ s : MachineState, (∀ o ∈ op.inst.operands, o.index < s.nextValueId) →
          ∃ (vecId : ValueId) (vals : List Int),
            op.inst.operands = [vecId] ∧
            s.lookupValue vecId = some (.vector (vals.map (fun i => Value.int w i))) ∧
            vals.length = lenN))

/-- `vectorLowerFrom` fires only on the ops the Rust `VectorLoweringPass`
    rewrites: a `some` result forces `op.dialect = "vector"` and an op name of
    `pack_lanes`, `mask_to_bits`, `reduce`, or `shuffle`. This is the
    structural tie between the soundness theorem below and the production
    pass. -/
theorem vectorLowerFrom_some_dialect_op {op : DialectOpSem} {lower : Nat → List Inst}
    (hsel : vectorLowerFrom op = some lower) :
    op.dialect = dialectName
      ∧ (op.op = "pack_lanes" ∨ op.op = "mask_to_bits" ∨ op.op = "reduce"
          ∨ op.op = "shuffle") := by
  unfold vectorLowerFrom at hsel
  by_cases hdl : op.dialect = dialectName
  · rw [if_pos hdl] at hsel
    refine ⟨hdl, ?_⟩
    -- Split the inner `match op.op with ...` (compiled to nested string `if`s);
    -- only the rewritten arms can return `some`. `split` records the
    -- op-name equality for each arm.
    split at hsel
    · exact Or.inl (by assumption)
    · exact Or.inr (Or.inl (by assumption))
    · exact Or.inr (Or.inr (Or.inl (by assumption)))
    · exact Or.inr (Or.inr (Or.inr (by assumption)))
    · -- wildcard arm: `hsel : none = some lower`, impossible.
      exact absurd hsel (by simp)
  · rw [if_neg hdl] at hsel; exact absurd hsel (by simp)

/-- **`DialectLowerSound`-style discharge for the Rust `VectorLoweringPass`.**
    Whenever `vectorLowerFrom` fires on a vector op (i.e. the pass rewrites it)
    selecting base-threaded lowering `lower`, and the op's per-shape refinement
    obligation `VectorOpRefines` holds, that lowering refines the dialect
    denotation under `runsAgreeFrom` — the equal-except-locals + result-agreement
    relation appropriate for a fresh-id-allocating lowering. This is the
    pointwise condition that makes the registry's fixpoint lowering sound,
    specialised to the production pass (cf. `TrustIr.DialectLowerSound` /
    `dummy_lower_sound`, which use full-state `runsAgree` for non-allocating
    lowerings). The four `VectorOpRefines` branches are witnessed by
    `vectorLowerFrom_pack_lanes_sound`, `runsAgreeFrom_mask_to_bits`,
    `runsAgreeFrom_reduce`, and `runsAgreeFrom_shuffle` (with the shape side
    conditions `rfl`/`decide`-true at every supported shape). -/
theorem vectorLowerFrom_sound
    (op : DialectOpSem) (lower : Nat → List Inst)
    (hsel : vectorLowerFrom op = some lower)
    (href : VectorOpRefines op lower) :
    runsAgreeFrom op op.inst.operands lower := by
  -- `hsel` ties this to the Rust pass: it fired only for the rewritten ops.
  have ⟨_hdl, _hop⟩ := vectorLowerFrom_some_dialect_op hsel
  -- `href` discharges the matching per-shape refinement.
  rcases href with
    ⟨spec, n, lenN, w, elemTy, P, hlow, hRun, helem, hlanes, hbw, hchar, hlaneP,
       hseedLen, hseedP, hdom⟩
    | ⟨spec, w, hlow, hRun, hbw, hInteger, hrw, hshape, hlanes_le, hdom⟩
    | ⟨spec, lenN, w, hlow, hRun, hlanes, hbw, hrw, hcharVec, hcharLane, hdom⟩
    | ⟨spec, n, lenN, w, elemTy, hlow, hRun, helem, hvecTy, hlanes, hbw, hchar,
       hcharLane, hlaneV, hidxLen, hidxLt, hdom⟩
  · rw [hlow]
    exact vectorLowerFrom_pack_lanes_sound op spec n lenN w elemTy P
      hRun helem hlanes hbw hchar hlaneP hseedLen hseedP hdom
  · rw [hlow]
    exact runsAgreeFrom_mask_to_bits op spec w hRun hbw hInteger hrw hshape hlanes_le hdom
  · rw [hlow]
    exact runsAgreeFrom_reduce op spec lenN w hRun hlanes hbw hrw hcharVec hcharLane hdom
  · rw [hlow]
    exact runsAgreeFrom_shuffle op spec n lenN w elemTy hRun helem hvecTy hlanes hbw
      hchar hcharLane hlaneV hidxLen hidxLt hdom

end VectorDialect
end TrustIr
