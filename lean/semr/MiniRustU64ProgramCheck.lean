/- Whole generated program typing and actual byte/model association controls.
   Wrong claims are definitions of propositions, never asserted theorems. -/
import MiniRustU64ProgramDecode

noncomputable section
namespace MiniRustU64ProgramCheck
open SemR MiniRustU64Program MiniRustU64ProgramTyping MiniRustU64ProgramDecode
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def RightProgram : Prop := ∀ (fuel literal input : Nat),
  literal < modulus 64 → input < modulus 64 →
    MRf.Program.check_wf (fuel + 80) (program literal input) = SOut.ok (.ok ())
theorem right_program : RightProgram := program_wellformed

def WrongRustStart : Prop := ∀ (fuel literal input : Nat),
  literal < modulus 64 → input < modulus 64 →
    MRf.Program.check_wf (fuel + 80) ((program literal input).set_start ⟨1⟩) = SOut.ok (.ok ())

/-- The same universal invalid-start subject is actually rejected by the
    generated checker. Comparing this proof to WrongRustStart changes the
    result, rather than normalizing two different large checker calls. -/
def RightRustStartRefusal : Prop := ∀ (fuel literal input : Nat),
  literal < modulus 64 → input < modulus 64 →
    MRf.Program.check_wf (fuel + 80) ((program literal input).set_start ⟨1⟩) =
      SOut.ok (.err (.IllFormed "Program: start function has invalid calling convention"))

/-- Recheck the actual function-pointer constant in the changed program;
    no well-formedness judgment is transported by comparing whole checkers. -/
theorem rust_start_pointer (fuel literal input : Nat) :
    MRf.Constant.check_wf (fuel + 2) (.FnPointer ⟨1⟩) (.Ptr .FnPtr)
      ((program literal input).set_start ⟨1⟩) = SOut.ok (.ok ()) := rfl

theorem rust_start_pointer_expression (fuel literal input : Nat)
    (locals : List (MR_LocalName × MR_Type)) :
    MRf.ValueExpr.check_wf (fuel + 20) (.Constant (.FnPointer ⟨1⟩) (.Ptr .FnPtr))
      locals ((program literal input).set_start ⟨1⟩) = SOut.ok (.ok (.Ptr .FnPtr)) := by
  apply constant_expression (fuel + 18)
  · exact pointer_type (fuel + 3) ((program literal input).set_start ⟨1⟩)
  · exact rust_start_pointer (fuel + 17) literal input

theorem rust_start_call (fuel literal input : Nat) (inputValid : input < modulus 64) :
    MRf.Terminator.check_wf (fuel + 40) (callTerm input) .Regular (entry input)
      ((program literal input).set_start ⟨1⟩) = SOut.ok (.ok ()) := by
  have ptrChecked (k : Nat) (locals : List (MR_LocalName × MR_Type)) :=
    rust_start_pointer_expression k literal input locals
  have argChecked (k : Nat) (locals : List (MR_LocalName × MR_Type)) :=
    u64_argument k input locals ((program literal input).set_start ⟨1⟩) inputValid
  have placeChecked (k : Nat) := result_place k input ((program literal input).set_start ⟨1⟩)
  have nextChecked (k : Nat) := next_block k input
  unfold callTerm
  simp only [MRf.Terminator.check_wf, ptrChecked, argChecked, placeChecked, nextChecked,
    MiniRustU64Function.layout_u64, SBool.not, SLoop.forS, SOut.bind, MRf.fn.ensure_wf,
    MRf.LayoutStrategy.is_sized]

theorem rust_start_entry (fuel literal input : Nat) (inputValid : input < modulus 64) :
    MRf.Function.check_wf (fuel + 64) (entry input)
      ((program literal input).set_start ⟨1⟩) = SOut.ok (.ok ()) := by
  have callChecked (k : Nat) := rust_start_call k literal input inputValid
  have storageChecked (k : Nat) := result_storage k input ((program literal input).set_start ⟨1⟩)
  have returnChecked (k : Nat) := return_block k input ((program literal input).set_start ⟨1⟩)
  have u64Checked (k : Nat) := u64_type k ((program literal input).set_start ⟨1⟩)
  have unitChecked (k : Nat) := unit_type k ((program literal input).set_start ⟨1⟩)
  simp only [MRf.Function.check_wf, entry_locals, entry_args, entry_ret, entry_blocks,
    callBlock, returnBlock, callChecked, storageChecked, returnChecked,
    u64Checked, unitChecked, MiniRustU64Function.layout_u64, MiniRustU64Program.unit_layout,
    SBool.not, SList.appendL, SList.push, SLoop.forS, SMap.contains_key, SMap.get,
    SMap.getL, SMap.values, SOption.is_some, SOut.bind, SRes.is_err,
    SSet.contains, SSet.try_insert, MR_LocalName.beq, MRf.fn.ensure_wf, MRf.LayoutStrategy.is_sized]

theorem right_rust_start_refusal : RightRustStartRefusal := by
  intro fuel literal input literalValid inputValid
  have entryChecked := rust_start_entry (fuel + 15) literal input inputValid
  have scalarChecked :=
    scalar_wellformed (fuel + 15) literal ((program literal input).set_start ⟨1⟩) literalValid
  simp only [Nat.add_assoc] at entryChecked scalarChecked
  dsimp only [MR_Program.set_start, program] at entryChecked scalarChecked
  simp only [MRf.Program.check_wf, MR_Program.set_start,
    program_functions, program_globals, program_traits, program_vtables,
    entryChecked, scalarChecked, MiniRustU64Call.function_convention,
    MR_CallingConvention.beq, MR_FnName.beq, SBool.not, SLoop.forS,
    SMap.get, SMap.getL, SMap.index_at, SMap.values, SOption.unwrap,
    SOut.bind, MRf.fn.ensure_wf, SInt.beq]

def WrongNoBounds : Prop := ∀ (fuel literal input : Nat),
  MRf.Program.check_wf (fuel + 80) (program literal input) = SOut.ok (.ok ())

def RightStartRefusal : Prop := ∀ (fuel : Nat),
  MRf.Program.check_wf (fuel + 80) ((program 7 3).set_start ⟨1⟩) =
    SOut.ok (.err (.IllFormed "Program: start function has invalid calling convention"))
theorem right_start_refusal : RightStartRefusal := by
  intro fuel
  rfl

def WrongStartAccepted : Prop := ∀ (fuel : Nat),
  MRf.Program.check_wf (fuel + 80) ((program 7 3).set_start ⟨1⟩) = SOut.ok (.ok ())

def RightInputRefusal : Prop := ∀ (fuel : Nat),
  MRf.Program.check_wf (fuel + 80) (program 7 (modulus 64)) =
    SOut.ok (.err (.IllFormed "Constant::Int: invalid int value"))
theorem right_input_refusal : RightInputRefusal := by
  intro fuel
  rfl

/-- Dropping the full64 bounds is semantically false, not merely a different
    number of arguments to the positive theorem. The actual generated checker
    rejects the explicit out-of-range input used by this countermodel. -/
def RightNoBoundsRefutation : Prop := ¬ WrongNoBounds

theorem right_no_bounds_refutation : RightNoBoundsRefutation := by
  intro alleged
  have impossible := alleged 0 7 (modulus 64)
  rw [right_input_refusal 0] at impossible
  cases impossible

def WrongInputAccepted : Prop := ∀ (fuel : Nat),
  MRf.Program.check_wf (fuel + 80) (program 7 (modulus 64)) = SOut.ok (.ok ())

def RightDecodedExact : Prop := ∀ (bytes : List Nat) (literal input : Nat),
  SemRU64ScalarProfile.Decodes bytes literal → fromBytes bytes input = some (program literal input)
theorem right_decoded_exact : RightDecodedExact := decoded_program_exact

def WrongDecodedLiteral : Prop := ∀ (bytes : List Nat) (literal input : Nat),
  SemRU64ScalarProfile.Decodes bytes literal → fromBytes bytes input = some (program (literal + 1) input)

def WrongDecodedInput : Prop := ∀ (bytes : List Nat) (literal input : Nat),
  SemRU64ScalarProfile.Decodes bytes literal → fromBytes bytes input = some (program literal (input + 1))

def RightDecodedTyping : Prop := ∀ (fuel literal input : Nat) (bytes : List Nat),
  SemRU64ScalarProfile.Decodes bytes literal → literal < modulus 64 → input < modulus 64 →
    (fromBytes bytes input).map (MRf.Program.check_wf (fuel + 80)) = some (SOut.ok (.ok ()))
theorem right_decoded_typing : RightDecodedTyping := decoded_program_wellformed

#print axioms right_program
#print axioms right_rust_start_refusal
#print axioms right_start_refusal
#print axioms right_input_refusal
#print axioms right_no_bounds_refutation
#print axioms right_decoded_exact
#print axioms right_decoded_typing

end MiniRustU64ProgramCheck
