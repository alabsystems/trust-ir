/- Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRSitedDivPanic

namespace SemR.SitedDivPanic.Check

-- Independently stated exact consumer questions for the general helper laws.
def TrueContract : Prop := ∀ (k : Core) (kind : DivPanicKind) (site : Site),
  on k kind site (.bool true) = .ok { k with pc := k.pc + 1 }
def FalseContract : Prop := ∀ (k : Core) (kind : DivPanicKind) (site : Site),
  on k kind site (.bool false) = .stop (.globalDivPanic ⟨kind, none, site.entry, site.global, 0⟩)
def SSATrueContract : Prop := ∀ (k : Core) (condition : Nat) (kind : DivPanicKind) (site : Site),
  getV k condition = .ok (.bool true) → step k condition kind site = .ok { k with pc := k.pc + 1 }
def SSAFalseContract : Prop := ∀ (k : Core) (condition : Nat) (kind : DivPanicKind) (site : Site),
  getV k condition = .ok (.bool false) → step k condition kind site =
    .stop (.globalDivPanic ⟨kind, none, site.entry, site.global, 0⟩)

def state (env : List (Nat × Val)) : Core :=
  { fn := ⟨0, 0, 0, [], []⟩, sig := ⟨[], [], false⟩,
    block := ⟨0, [], []⟩, pc := 7, env := env, depth := 3,
    stack := [], openFrames := [2], nextFrame := 5, mem := Mem.empty }

def site : Site := ⟨41, 1⟩
def model : Module :=
  { funcTys := [⟨[.ptr], [], false⟩], enums := [], functions := [⟨41, 0, 0, [], []⟩] }
def metadata : Metadata :=
  { module := model,
    entries := [⟨41, false⟩], globals := [⟨true, true⟩, ⟨false, false⟩] }

theorem sparse_bodyless_entry_admitted : admissible metadata site = true := by rfl
theorem missing_entry_refused : admissible metadata ⟨0, 1⟩ = false := by rfl
theorem missing_global_refused : admissible metadata ⟨41, 2⟩ = false := by rfl
theorem mutable_global_refused :
    admissible { metadata with globals := [⟨false, false⟩, ⟨true, false⟩] } site = false := by rfl
theorem tls_global_refused :
    admissible { metadata with globals := [⟨false, false⟩, ⟨false, true⟩] } site = false := by rfl
theorem weak_entry_refused : admissible { metadata with entries := [⟨41, true⟩] } site = false := by rfl
theorem missing_header_refused : admissible { metadata with entries := [] } site = false := by rfl
theorem duplicate_header_refused :
    admissible { metadata with entries := [⟨41, false⟩, ⟨41, false⟩] } site = false := by rfl
theorem duplicate_entry_refused :
    admissible { metadata with module := { metadata.module with
      functions := [⟨41, 0, 0, [], []⟩, ⟨41, 0, 0, [], []⟩] } } site = false := by rfl

def signatureMetadata (signature : FuncTy) : Metadata :=
  { metadata with module := { metadata.module with funcTys := [signature] } }

theorem wrong_parameter_refused : admissible (signatureMetadata ⟨[.int .usize], [], false⟩) site = false := by rfl
theorem wrong_arity_refused : admissible (signatureMetadata ⟨[.ptr, .ptr], [], false⟩) site = false := by rfl
theorem returning_entry_refused : admissible (signatureMetadata ⟨[.ptr], [.never], false⟩) site = false := by rfl
theorem variadic_entry_refused : admissible (signatureMetadata ⟨[.ptr], [], true⟩) site = false := by rfl
theorem missing_signature_refused :
    admissible { metadata with module := { metadata.module with funcTys := [] } } site = false := by rfl

theorem false_div_exact : step (state [(0, .bool false)]) 0 .divByZero site =
    .stop (.globalDivPanic ⟨.divByZero, none, 41, 1, 0⟩) := by rfl
theorem false_rem_exact : step (state [(0, .bool false)]) 0 .remByZero site =
    .stop (.globalDivPanic ⟨.remByZero, none, 41, 1, 0⟩) := by rfl
theorem true_preserves_all_state : step (state [(0, .bool true)]) 0 .divByZero site =
    .ok { state [(0, .bool true)] with pc := 8 } := by rfl
theorem invalid_site_is_not_read_on_true :
    step (state [(0, .bool true)]) 0 .divByZero ⟨999, 999⟩ = .ok (next (state [(0, .bool true)])) := by rfl
theorem missing_condition_precedes_site : step (state []) 0 .divByZero site =
    .stop (.typeError "MissingValue: value is not defined") := by rfl
theorem poison_condition_precedes_site : step (state [(0, .poison .bool)]) 0 .divByZero site =
    .stop (.ub "assert: use of an uninitialized value (poison)") := by
  let leftChars : List Char := [Char.ofNat 97, Char.ofNat 115, Char.ofNat 115, Char.ofNat 101, Char.ofNat 114, Char.ofNat 116]
  let rightChars : List Char := [Char.ofNat 58, Char.ofNat 32, Char.ofNat 117, Char.ofNat 115, Char.ofNat 101, Char.ofNat 32, Char.ofNat 111, Char.ofNat 102, Char.ofNat 32, Char.ofNat 97, Char.ofNat 110, Char.ofNat 32, Char.ofNat 117, Char.ofNat 110, Char.ofNat 105, Char.ofNat 110, Char.ofNat 105, Char.ofNat 116, Char.ofNat 105, Char.ofNat 97, Char.ofNat 108, Char.ofNat 105, Char.ofNat 122, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 118, Char.ofNat 97, Char.ofNat 108, Char.ofNat 117, Char.ofNat 101, Char.ofNat 32, Char.ofNat 40, Char.ofNat 112, Char.ofNat 111, Char.ofNat 105, Char.ofNat 115, Char.ofNat 111, Char.ofNat 110, Char.ofNat 41]
  have hleft : String.ofList leftChars = "assert" := by rfl
  have hright : String.ofList rightChars = ": use of an uninitialized value (poison)" := by rfl
  have hfull : String.ofList (leftChars ++ rightChars) = "assert: use of an uninitialized value (poison)" := by rfl
  have happend : "assert" ++ ": use of an uninitialized value (poison)" = "assert: use of an uninitialized value (poison)" :=
    (congrArg (fun x : String => x ++ ": use of an uninitialized value (poison)") hleft.symm).trans
      ((congrArg (fun y : String => String.ofList leftChars ++ y) hright.symm).trans
        ((String.ofList_append (l₁ := leftChars) (l₂ := rightChars)).symm.trans hfull))
  change R.stop (α := Core) (.ub (s!"{("assert" : String)}: use of an uninitialized value (poison)")) = _
  exact congrArg (fun msg => R.stop (α := Core) (.ub msg)) happend
theorem nonbool_condition_refused : step (state [(0, .int .u8 1)]) 0 .divByZero site =
    .stop (.typeError "TypeError: assert requires bool") := by rfl

theorem false_kind_swap_detected : on (state []) .divByZero site (.bool false) ≠
    .stop (.globalDivPanic ⟨.remByZero, none, 41, 1, 0⟩) := by intro h; cases h
theorem false_entry_swap_detected : on (state []) .divByZero site (.bool false) ≠
    .stop (.globalDivPanic ⟨.divByZero, none, 42, 1, 0⟩) := by intro h; cases h
theorem false_global_swap_detected : on (state []) .divByZero site (.bool false) ≠
    .stop (.globalDivPanic ⟨.divByZero, none, 41, 0, 0⟩) := by intro h; cases h
theorem false_offset_swap_detected : on (state []) .divByZero site (.bool false) ≠
    .stop (.globalDivPanic ⟨.divByZero, none, 41, 1, 1⟩) := by intro h; cases h
theorem false_operand_invention_detected : on (state []) .divByZero site (.bool false) ≠
    .stop (.globalDivPanic ⟨.divByZero, some [], 41, 1, 0⟩) := by intro h; cases h

-- Genuine false consumer questions, never assumptions of the positive proofs.
def WrongKind : Prop := on (state []) .divByZero site (.bool false) =
    .stop (.globalDivPanic ⟨.remByZero, none, 41, 1, 0⟩)
def WrongEntry : Prop := on (state []) .divByZero site (.bool false) =
    .stop (.globalDivPanic ⟨.divByZero, none, 42, 1, 0⟩)
def WrongGlobal : Prop := on (state []) .divByZero site (.bool false) =
    .stop (.globalDivPanic ⟨.divByZero, none, 41, 0, 0⟩)
def WrongOffset : Prop := on (state []) .divByZero site (.bool false) =
    .stop (.globalDivPanic ⟨.divByZero, none, 41, 1, 1⟩)
def WrongOperands : Prop := on (state []) .divByZero site (.bool false) =
    .stop (.globalDivPanic ⟨.divByZero, some [], 41, 1, 0⟩)
def WrongPreservation : Prop := on (state []) .divByZero site (.bool true) = .ok (state [])

def DivOutcome : Prop := on (state []) .divByZero site (.bool false) =
    .stop (.globalDivPanic ⟨.divByZero, none, 41, 1, 0⟩)
theorem div_outcome : DivOutcome := by rfl
def TrueOutcome : Prop := on (state []) .divByZero site (.bool true) =
    .ok { state [] with pc := 8 }
theorem true_outcome : TrueOutcome := by rfl

theorem siteless_false_unchanged : assertOn (state []) .divByZero (.bool false) =
    .stop (.panic "attempt to divide by zero") := by rfl

theorem tag66_still_refused : inst 54 #[] [66,0,1,1,41,0,1] =
    .err (.unsupported "inst.assert.sited") := by rfl
theorem tag67_still_refused : inst 54 #[] [67,0,1,2,41,0,1] =
    .err (.unsupported "inst.assert.sited") := by rfl
theorem nonempty_globals_still_refused : emptySection "globals" 54 #[] [1,0] =
    .err (.unsupported "globals") := by rfl
theorem compound_type_still_refused : ty 54 #[] [17,1,1] =
    .err (.unsupported "ty.compound") := by rfl

end SemR.SitedDivPanic.Check
