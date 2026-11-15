/- Actual complete decoded IR bytes select the callee of the checked model
   program. This is a bounded model construction, not Rust/source translation. -/
import MiniRustU64ProgramTyping

noncomputable section
namespace MiniRustU64ProgramDecode
open SemR MiniRustU64Program MiniRustU64ProgramTyping
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def fromBytes (bytes : List Nat) (input : Nat) : Option MR_Program :=
  (MiniRustU64ScalarCorrespondence.modelOfBytes bytes).map (fun callee =>
    { functions := [(⟨0⟩, entry input), (⟨1⟩, callee)]
      start := ⟨0⟩, globals := [], traits := [], vtables := [] })

theorem decoded_program_exact (bytes : List Nat) (literal input : Nat)
    (checked : SemRU64ScalarProfile.Decodes bytes literal) :
    fromBytes bytes input = some (program literal input) := by
  unfold fromBytes
  rw [MiniRustU64ScalarCorrespondence.decoded_model_exact bytes literal checked]
  rfl

theorem decoded_program_wellformed (fuel literal input : Nat) (bytes : List Nat)
    (checked : SemRU64ScalarProfile.Decodes bytes literal)
    (literalValid : literal < modulus 64) (inputValid : input < modulus 64) :
    (fromBytes bytes input).map (MRf.Program.check_wf (fuel + 80)) =
      some (SOut.ok (.ok ())) := by
  rw [decoded_program_exact bytes literal input checked]
  change some (MRf.Program.check_wf (fuel + 80) (program literal input)) = some (SOut.ok (.ok ()))
  rw [program_wellformed fuel literal input literalValid inputValid]

end MiniRustU64ProgramDecode
