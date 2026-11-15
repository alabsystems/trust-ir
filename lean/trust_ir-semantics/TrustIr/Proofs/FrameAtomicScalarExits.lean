-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAggregateStores
import TrustIr.Proofs.FrameCastExits

namespace TrustIr.FrameLifetime

private theorem get_action : FrameActionValid (fun _ _ => True) Sem.getState := by
  intro state valid
  exact ⟨valid,True.intro,.refl _⟩

private theorem write_action (memory : Memory) :
    FrameActionValid (fun _ _ => True) (Sem.modifyState fun state => {state with memory}) := by
  intro state valid
  exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

private theorem atomic_prefix {α : Type} (post : Nat → α → Prop) (ctx : EvalContext)
    (operation : String) (ty : Ty) (pointer : ValueId) (next : Addr → Nat → MachineState → Sem α)
    (tail : ∀ address size snapshot, FrameActionValid post (next address size snapshot)) :
    FrameActionValid post (do
      let pointer ← Sem.lookupValue pointer
      Sem.rejectPartial pointer operation
      let (address,allocation) ← Sem.expectPointer operation pointer
      let size ← match ty.byteSizeFor ctx.byteModel with
        | some size => pure size
        | none => Sem.throwUnsupported .layout (operation ++ ": type has no byte size")
      let alignment ← Sem.accessAlign operation ty none ctx.byteModel
      let address ← Sem.checkedAccess operation address allocation size alignment ctx.byteModel
      let snapshot ← Sem.getState
      next address size snapshot) := by
  intro state valid
  apply FrameActionExit.bind MintedValue post _ _ state (lookup_value_frame_action pointer state valid)
  intro pointer state valid _
  apply FrameActionExit.bind (fun _ _ => True) post _ _ state (reject_partial_frame_action pointer operation state valid)
  intro unit state valid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) post _ _ state (expect_pointer_frame_action pointer operation state valid)
  intro pair state valid _
  obtain ⟨address,allocation⟩ := pair
  cases ty.byteSizeFor ctx.byteModel with
  | none => exact True.intro
  | some size =>
    simp only [pure_bind]
    apply FrameActionExit.bind (fun _ _ => True) post _ _ state (access_align_frame_action operation ty none ctx.byteModel state valid)
    intro alignment state valid _
    apply FrameActionExit.bind (fun _ _ => True) post _ _ state (checked_access_frame_action operation address allocation size alignment ctx.byteModel state valid)
    intro address state valid _
    apply FrameActionExit.bind (fun _ _ => True) post _ _ state (get_action state valid)
    intro snapshot state valid _
    exact tail address size snapshot state valid

theorem scalar_atomic_load_frame_exit (ctx : EvalContext) (ty : Ty) (pointer : ValueId) (ordering : MemOrdering) :
    FrameActionValid (fun _ _ => True) (semAtomicLoadUsing
      (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
      ty pointer ordering ctx.byteModel) := by
  intro state valid
  unfold semAtomicLoadUsing
  by_cases rejected : (!isValidLoadOrdering ordering) = true
  · simp only [rejected,↓reduceIte]
    exact True.intro
  · simp only [rejected,↓reduceIte,pure_bind]
    apply atomic_prefix (fun _ _ => True) ctx "AtomicLoad" ty pointer _ _ state valid
    intro address size snapshot state valid
    cases read : snapshot.memory.readBytes address size with
    | none => exact True.intro
    | some bytes =>
      simp only [pure_bind]
      have decodedSafe := decode_functions_frame_exit ctx.byteModel ctx.functionOrder snapshot.memory ty bytes
      cases decoded : decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder snapshot.memory ty bytes with
      | error error =>
        rw [decoded] at decodedSafe
        cases error <;> first | exact True.intro | exact False.elim decodedSafe
      | ok value =>
        rw [decoded] at decodedSafe
        exact fresh_minted_frame_exit value state valid (decodedSafe.mono (Nat.zero_le _))

theorem scalar_atomic_store_frame_exit (ctx : EvalContext) (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) :
    FrameActionValid (fun _ _ => True) (semAtomicStoreUsing
      (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty pointer value ordering ctx.byteModel) := by
  intro state valid
  unfold semAtomicStoreUsing
  by_cases rejected : (!isValidStoreOrdering ordering) = true
  · simp only [rejected,↓reduceIte]
    exact True.intro
  · simp only [rejected,↓reduceIte,pure_bind]
    apply atomic_prefix (fun _ _ => True) ctx "AtomicStore" ty pointer _ _ state valid
    intro address size snapshot state valid
    apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action value state valid)
    intro value state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (reject_partial_frame_action value "AtomicStore" state valid)
    intro unit state valid _
    cases unit
    cases encoded : encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty value with
    | error error =>
      cases error <;> first
        | exact True.intro
        | exact False.elim (encode_functions_no_unwind _ _ _ _ _ _ encoded)
    | ok bytes =>
      simp only [pure_bind]
      split
      · exact True.intro
      · try simp only [pure_bind]
        exact write_action _ state valid

theorem scalar_atomic_rmw_frame_exit (ctx : EvalContext) (op : AtomicRMWOp) (ty : Ty)
    (pointer operand : ValueId) (ordering : MemOrdering) :
    FrameActionValid (fun _ _ => True) (semAtomicRMWUsing
      (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
      (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) op ty pointer operand ordering ctx.byteModel) := by
  unfold semAtomicRMWUsing
  apply atomic_prefix (fun _ _ => True) ctx "AtomicRMW" ty pointer
  intro address size snapshot state valid
  cases snapshot.memory.readBytes address size with
  | none => exact True.intro
  | some bytes =>
    simp only [pure_bind]
    have decodedSafe := decode_functions_frame_exit ctx.byteModel ctx.functionOrder snapshot.memory ty bytes
    cases decoded : decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder snapshot.memory ty bytes with
    | error error =>
      rw [decoded] at decodedSafe
      cases error <;> first | exact True.intro | exact False.elim decodedSafe
    | ok current =>
      rw [decoded] at decodedSafe
      simp only [pure_bind]
      apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action operand state valid)
      intro operand state valid _
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (reject_partial_frame_action operand "AtomicRMW" state valid)
      intro unit state valid _
      cases unit
      cases current <;> try exact True.intro
      case int width raw =>
        cases operand <;> try exact True.intro
        case int operandWidth argument operandMinted =>
          try simp only [pure_bind]
          cases encoded : encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty (.int width (applyAtomicRMWOp op width raw argument)) with
          | error error =>
            cases error <;> first
              | exact True.intro
              | exact False.elim (encode_functions_no_unwind _ _ _ _ _ _ encoded)
          | ok bytes =>
            try simp only [pure_bind]
            apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
            intro snapshot state valid _
            apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (write_action (snapshot.memory.writeBytes address bytes) state valid)
            intro unit state valid _
            cases unit
            exact fresh_minted_frame_exit _ state valid (decodedSafe.mono (Nat.zero_le _))

private theorem compare_then {α : Type} (post : Nat → α → Prop) (ty : Ty) (left right : Value)
    (next : Bool → Sem α) (tail : ∀ answer, FrameActionValid post (next answer)) :
    FrameActionValid post (do
      let answer ← match left,right with
        | .float a,.float b => match floatToBitsAt ty a,floatToBitsAt ty b with
          | .ok x,.ok y => pure (x == y)
          | .error error,_ => throw error
          | _,.error error => throw error
        | .int _ a,.int _ b => pure (a == b)
        | .bool a,.bool b => pure (a == b)
        | .ptr a p,.ptr b q => pure (a == b && p == q)
        | .fnDef a f,.fnDef b g => pure (a == b && f == g)
        | .nullPtr,.nullPtr => pure true
        | _,_ => pure false
      next answer) := by
  trustIrCompilerProof {
    intro state valid
    repeat' first
      | (solve | exact tail _ state valid)
      | (simp only [pure_bind])
      | split
      | (dsimp only; split)
    case h_1.h_2 =>
      rename_i failure checked
      cases failure <;> first
        | exact True.intro
        | exact False.elim (cast_float_to_bits_no_unwind _ _ _ _ checked)
    case h_1.h_3 =>
      rename_i failure checked excluded
      cases failure <;> first
        | exact True.intro
        | exact False.elim (cast_float_to_bits_no_unwind _ _ _ _ checked)
  } {
    intro state valid
    repeat' first
      | (solve | exact tail _ state valid)
      | (simp only [pure_bind])
      | split
      | (dsimp only; split)
    case h_2 =>
      rename_i failure checked
      cases failure <;> first
        | exact True.intro
        | exact False.elim (cast_float_to_bits_no_unwind _ _ _ _ checked)
    case h_3 =>
      rename_i failure checked excluded
      cases failure <;> first
        | exact True.intro
        | exact False.elim (cast_float_to_bits_no_unwind _ _ _ _ checked)
  }

/-- Original scalar exchange, including bitwise float comparison, actual
conditional desired lookup/write and both original refusal paths. -/
theorem scalar_exchange_frame_exit (ctx : EvalContext) (ty : Ty) (pointer expected desired : ValueId) :
    FrameActionValid (fun bound (pair : Value × Bool) => MintedValue bound pair.1) (semCmpXchgExchangeUsing
      (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
      (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty pointer expected desired ctx.byteModel) := by
  unfold semCmpXchgExchangeUsing
  apply atomic_prefix (fun bound (pair : Value × Bool) => MintedValue bound pair.1) ctx "CmpXchg" ty pointer
  intro address size snapshot state valid
  cases snapshot.memory.readBytes address size with
  | none => exact True.intro
  | some bytes =>
    simp only [pure_bind]
    have decodedSafe := decode_functions_frame_exit ctx.byteModel ctx.functionOrder snapshot.memory ty bytes
    cases decoded : decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder snapshot.memory ty bytes with
    | error error =>
      rw [decoded] at decodedSafe
      cases error <;> first | exact True.intro | exact False.elim decodedSafe
    | ok current =>
      rw [decoded] at decodedSafe
      simp only [pure_bind]
      apply FrameActionExit.bind MintedValue (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (lookup_value_frame_action expected state valid)
      intro expected state valid _
      apply FrameActionExit.bind (fun _ _ => True) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (reject_partial_frame_action expected "CmpXchg expected" state valid)
      intro unit state valid _
      cases unit
      have finish (success : Bool) : FrameActionValid (fun bound (pair : Value × Bool) => MintedValue bound pair.1) (do
          if success then do
            let desired ← Sem.lookupValue desired
            Sem.rejectPartial desired "CmpXchg"
            let bytes ← match encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty desired with
              | .ok bytes => pure bytes
              | .error error => throw error
            let snapshot ← Sem.getState
            Sem.modifyState fun state => {state with memory := snapshot.memory.writeBytes address bytes}
          pure (current,success)) := by
        intro state valid
        cases success
        · simp only [Bool.false_eq_true,↓reduceIte,pure_bind]
          exact ⟨valid,decodedSafe.mono (Nat.zero_le _),.refl _⟩
        · simp only [↓reduceIte]
          apply FrameActionExit.bind MintedValue (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (lookup_value_frame_action desired state valid)
          intro desired state valid _
          apply FrameActionExit.bind (fun _ _ => True) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (reject_partial_frame_action desired "CmpXchg" state valid)
          intro unit state valid _
          cases unit
          cases encoded : encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty desired with
          | error error =>
            cases error <;> first
              | exact True.intro
              | exact False.elim (encode_functions_no_unwind _ _ _ _ _ _ encoded)
          | ok bytes =>
            try simp only [pure_bind]
            apply FrameActionExit.bind (fun _ _ => True) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (get_action state valid)
            intro snapshot state valid _
            apply FrameActionExit.bind (fun _ _ => True) (fun bound (pair : Value × Bool) => MintedValue bound pair.1) _ _ state (write_action (snapshot.memory.writeBytes address bytes) state valid)
            intro unit state valid _
            cases unit
            exact ⟨valid,decodedSafe.mono (Nat.zero_le _),.refl _⟩
      exact compare_then _ ty current expected _ finish state valid

end TrustIr.FrameLifetime
