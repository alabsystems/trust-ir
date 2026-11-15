-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr

/-- The complete top-level integer policy, independently of the producing
    instruction and of the integer carrier's width. -/
theorem ssaChar_int_success_iff (width : Nat) (raw : Int) :
    checkSSACharValue .Char (.int width raw) = .ok () ↔
      0 ≤ raw ∧ validChar raw.toNat := by
  by_cases negative : raw < 0
  · have nonnegative : ¬ 0 ≤ raw := by omega
    simp [checkSSACharValue, negative, nonnegative]
  · have nonnegative : 0 ≤ raw := by omega
    by_cases valid : validChar raw.toNat <;>
      simp [checkSSACharValue, negative, nonnegative, valid]

theorem ssaChar_width_independent (first second : Nat) (raw : Int) :
    checkSSACharValue .Char (.int first raw) =
      checkSSACharValue .Char (.int second raw) := rfl

theorem ssaChar_non_integer_transport (value : Value)
    (notInt : ∀ width raw, value ≠ .int width raw) :
    checkSSACharValue .Char value = .ok () := by
  cases value <;> first | rfl | exact False.elim (notInt _ _ rfl)

theorem ssaChar_other_type (ty : Ty) (value : Value) (h : ty ≠ .Char) :
    checkSSACharValue ty value = .ok () := by
  cases ty <;> first | contradiction | rfl

theorem ssaChar_poison_transport (ty poisonTy : Ty) :
    checkSSACharValue ty (.undef poisonTy) = .ok () := by
  cases ty <;> rfl

theorem ssaChar_partial_transport (ty : Ty) (image : List (Option UInt8)) :
    checkSSACharValue ty (.partial image) = .ok () := by
  cases ty <;> rfl

theorem ssaChar_uninit_transport (ty : Ty) :
    checkSSACharValue ty .uninit = .ok () := by
  cases ty <;> rfl

/-- No recursive Char policy is imposed on aggregate payloads. -/
theorem ssaChar_aggregate_transport (ty : Ty) (values : List Value) :
    checkSSACharValue ty (.aggregate values) = .ok () := by
  cases ty <;> rfl

theorem ssaChar_valid_edges :
    ([0, 0xD7FF, 0xE000, 0xFFFF, 0x10FFFF] : List Int).map
      (fun raw => checkSSACharValue .Char (.int 32 raw)) =
      List.replicate 5 (.ok ()) := rfl

theorem ssaChar_invalid_edges :
    ([-1, 0xD800, 0xDFFF, 0x110000, 0xFFFFFFFF, 0x100000041] : List Int).map
      (fun raw => checkSSACharValue .Char (.int 32 raw)) =
      List.replicate 6 (.error (.ub "char value is not a Unicode scalar value")) := rfl

theorem ssaChar_u32_control (width : Nat) (raw : Int) :
    checkSSACharValue .U32 (.int width raw) = .ok () := rfl

theorem ssaChar_mixed_top_level_only :
    checkSSACharValues [.U32, .Char, .Tuple [.Char]]
      [.int 32 0xD800, .int 32 65, .aggregate [.int 32 0xD800]] = .ok () := rfl

theorem ssaChar_block_parameter_valid (s : MachineState) :
    Sem.run (bindBlockParamsChecked [(⟨42⟩, .Char)] [.int 32 0x10FFFF]) s =
      Sem.run (bindBlockParams [(⟨42⟩, .Char)] [.int 32 0x10FFFF]) s := rfl

theorem ssaChar_block_parameter_invalid (s : MachineState) :
    Sem.run (bindBlockParamsChecked [(⟨42⟩, .Char)] [.int 32 0xD800]) s =
      .error (.ub "char value is not a Unicode scalar value") := rfl

theorem ssaChar_block_arity_priority (s : MachineState) :
    Sem.run (bindBlockParamsChecked [(⟨42⟩, .Char)] [.int 32 0xD800, .uninit]) s =
      Sem.run (bindBlockParams [(⟨42⟩, .Char)] [.int 32 0xD800, .uninit]) s := rfl

theorem ssaChar_manual_source_declaration :
    ssaInstructionResultTypes none (fun _ => none) (fun _ => none)
      (.Cast .Trunc .U64 .Char ⟨7⟩) [] 1 = .ok [.Char] := rfl

theorem ssaChar_source_missing_destination :
    ssaInstructionResultTypes (some (fun _ => none)) (fun _ => none) (fun _ => none)
      (.Const .Char (.int 65)) [⟨42⟩] 1 =
      .error (.typeError "SSA types: result destination has no declaration") := rfl

theorem ssaChar_source_result_count :
    ssaInstructionResultTypes (some (fun _ => some .Char)) (fun _ => none) (fun _ => none)
      (.Const .Char (.int 65)) [] 1 =
      .error (.typeError "instruction result count mismatch") := rfl

theorem ssaChar_manual_borrow_boundary :
    ssaInstructionResultTypes none (fun _ => none) (fun _ => none)
      (.Borrow ⟨7⟩) [⟨42⟩] 1 =
      .error (.unsupported .ssaTypeTable "SSA result types: Borrow requires original declarations") := rfl

theorem ssaChar_manual_header_boundary :
    ssaInstructionResultTypes none (fun _ => none) (fun _ => none)
      (.Call ⟨7⟩ []) [⟨42⟩] 1 =
      .error (.unsupported .ssaTypeTable "SSA result types: original callee header is unavailable") := rfl

theorem ssaChar_classification_result_count :
    ssaInstructionResultTypes none (fun _ => none) (fun _ => none)
      (.Overflow .AddOverflow .U8 ⟨0⟩ ⟨1⟩) [⟨42⟩] 1 =
      .error (.typeError "SSA types: instruction result classification count mismatch") := rfl

/-- The fallback reads the actual produced id even when a manual block uses
    its historical fresh-result convention and discards the instruction. -/
theorem ssaChar_discarded_result_checked (ctx : EvalContext) (s : MachineState) :
    Sem.run (({ ctx with localTypes := none }).bindInstructionResults
        (.Cast .Trunc .U64 .Char ⟨7⟩) (.value (some ⟨42⟩)) [])
      { s with locals := s.locals.set ⟨42⟩ (.int 32 0xD800) } =
      .error (.ub "char value is not a Unicode scalar value") := rfl

theorem ssaChar_missing_association_before_value_check (ctx : EvalContext) (s : MachineState) :
    Sem.run (({ ctx with localTypes := some (fun _ => none) }).bindInstructionResults
        (.Cast .Trunc .U64 .Char ⟨7⟩) (.value (some ⟨42⟩)) [⟨42⟩])
      { s with locals := s.locals.set ⟨42⟩ (.int 32 0xD800) } =
      .error (.typeError "SSA types: result destination has no declaration") := rfl

theorem ssaChar_manual_call_result_order :
    ssaInstructionResultTypes none
      (fun _ => some { params := [], returns := [.U32, .Char], isVararg := false })
      (fun _ => none) (.Call ⟨7⟩ []) [⟨42⟩, ⟨99⟩] 2 = .ok [.U32, .Char] := rfl

/-- A source-declared non-Char result has no extra value policy. The premise
    is the actual declaration association, not successful execution. -/
theorem checkInstructionResults_single_nonChar (ctx : EvalContext) (inst : Inst)
    (dest : ValueId) (ty : Ty) (value : Value)
    (types : ctx.instructionResultTypes inst [dest] 1 = .ok [ty])
    (notChar : ty ≠ .Char) :
    ctx.checkInstructionResults inst [dest] [value] = pure () := by
  have valid : checkSSACharValues [ty] [value] = .ok () := by
    simp only [checkSSACharValues, ssaChar_other_type ty value notChar]
    rfl
  simp only [EvalContext.checkInstructionResults, List.length_cons, List.length_nil,
    types, pure_bind, valid]

/-- Full-computation normalization, including undefined-result errors and
    complete post-state: the added pure source check does not duplicate a
    successful result publication or require a returning-run hypothesis. -/
theorem bindInstructionResults_single_nonChar (ctx : EvalContext) (inst : Inst)
    (dest result : ValueId) (ty : Ty)
    (types : ctx.instructionResultTypes inst [dest] 1 = .ok [ty])
    (notChar : ty ≠ .Char) :
    ctx.bindInstructionResults inst (.value (some result)) [dest] =
      bindInstrResultDests (.value (some result)) [dest] := by
  simp only [EvalContext.bindInstructionResults,
    checkInstructionResults_single_nonChar ctx inst dest ty _ types notChar, pure_bind]
  funext state
  cases h : state.lookupValue result <;>
    simp [bindInstrResultDests, Sem.lookupValue, Sem.getState, Sem.throwTypeError,
      Bind.bind, Pure.pure, StateT.bind, StateT.get, StateT.pure, StateT.lift,
      Except.bind, Except.pure, h] <;> rfl

theorem single_result_private_retired (value : Value) (world : MachineState) :
    (Sem.run (bindInstrResultDests (.value (some ⟨0⟩)) [⟨42⟩])
      { world with locals := ValueMap.empty.set ⟨0⟩ value, nextValueId := 1 }).map
      (fun pair => [pair.snd.lookupValue ⟨0⟩, pair.snd.lookupValue ⟨42⟩]) =
      .ok [none, some value] := rfl

/-- An actual destination equal to the fresh id is never retired. This is
    equality of the complete computation with direct destination publication. -/
theorem single_result_same_id (value : Value) (world : MachineState) :
    Sem.run (bindInstrResultDests (.value (some ⟨0⟩)) [⟨0⟩])
        { world with locals := ValueMap.empty.set ⟨0⟩ value, nextValueId := 1 } =
      Sem.run (bindResultDests [⟨0⟩] [value])
        { world with locals := ValueMap.empty.set ⟨0⟩ value, nextValueId := 1 } := rfl

theorem single_result_implicit_keeps_fresh (result : ValueId) :
    bindInstrResultDests (.value (some result)) [] = pure () := rfl

/-- A later original source declaration does not make an earlier private
    temporary an observable definition of that name. The table comes from
    the actual two source nodes and includes the future destination zero. -/
theorem single_result_future_declaration_retired (ctx : EvalContext) (world : MachineState) :
    let original := match inferLocalTypes (fun _ => none) (fun _ => none) []
        [(.Const .U64 (.int 7), [⟨42⟩]), (.Copy .U64 ⟨42⟩, [⟨0⟩])] with
      | .ok table => some table
      | .error _ => none
    (Sem.run (({ ctx with localTypes := original }).bindInstructionResults
        (.Const .U64 (.int 7)) (.value (some ⟨0⟩)) [⟨42⟩])
      { world with locals := ValueMap.empty.set ⟨0⟩ (.int 64 7), nextValueId := 1 }).map
      (fun pair => [pair.snd.lookupValue ⟨0⟩, pair.snd.lookupValue ⟨42⟩]) =
      .ok [none, some (.int 64 7)] := rfl

theorem single_result_later_source_destination (world : MachineState) :
    (Sem.run (do
        let first ← Sem.bindFresh (.int 64 7)
        bindInstrResultDests (.value (some first)) [⟨42⟩]
        let value ← Sem.lookupValue ⟨42⟩
        let second ← Sem.bindFresh value
        bindInstrResultDests (.value (some second)) [⟨0⟩])
      { world with locals := ValueMap.empty, nextValueId := 0 }).map
      (fun pair => [pair.snd.lookupValue ⟨0⟩, pair.snd.lookupValue ⟨42⟩,
        pair.snd.lookupValue ⟨43⟩]) =
      .ok [some (.int 64 7), some (.int 64 7), none] := rfl

end TrustIr

#trustIrAxioms TrustIr.ssaChar_int_success_iff <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact TrustIr.ssaChar_width_independent == []
#trustIrAxiomsExact TrustIr.ssaChar_non_integer_transport == []
#trustIrAxiomsExact TrustIr.ssaChar_other_type == []
#trustIrAxiomsExact TrustIr.ssaChar_poison_transport == []
#trustIrAxiomsExact TrustIr.ssaChar_partial_transport == []
#trustIrAxiomsExact TrustIr.ssaChar_uninit_transport == []
#trustIrAxiomsExact TrustIr.ssaChar_aggregate_transport == []
#trustIrAxiomsExact TrustIr.ssaChar_valid_edges == []
#trustIrAxiomsExact TrustIr.ssaChar_invalid_edges == []
#trustIrAxiomsExact TrustIr.ssaChar_u32_control == []
#trustIrAxiomsExact TrustIr.ssaChar_mixed_top_level_only == []
#trustIrAxiomsExact TrustIr.ssaChar_block_parameter_valid == []
#trustIrAxiomsExact TrustIr.ssaChar_block_parameter_invalid == []
#trustIrAxiomsExact TrustIr.ssaChar_block_arity_priority == []
#trustIrAxiomsPinned TrustIr.ssaChar_manual_source_declaration == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_source_missing_destination == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_source_result_count == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_manual_borrow_boundary == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_manual_header_boundary == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_classification_result_count == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_discarded_result_checked == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_missing_association_before_value_check == [propext, Classical.choice, Quot.sound] modern []
#trustIrAxiomsPinned TrustIr.ssaChar_manual_call_result_order == [propext, Classical.choice, Quot.sound] modern []
