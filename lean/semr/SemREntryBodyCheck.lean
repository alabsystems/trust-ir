/- Copyright 2026 Andrew Yates. Apache-2.0.
   Existing operational checks only; no original Rust quotation or source
   certification is claimed by these bounded read/comparison controls. -/
import SemREntryBody
import SemREntryCheck

namespace SemR.EntryDomain.BodyCheck
open SemR
open SemR.EntryDomain.Check

def lanes (n : Nat) : List Val := [.int .i8 249, .bool true, .int .u64 n]

theorem actual_payload_value :
    evalExtract model (.int .u64) (.enum 7 (lanes 9)) 2 = .ok (.int .u64 9) := rfl

theorem missing_value_is_not_invented :
    evalExtract model (.int .u64) (.enum 7 [.int .i8 249, .bool true]) 2 =
      .stop (.ub "field is out of bounds") := rfl

theorem wrong_actual_value_type :
    evalExtract model (.int .u64) (.enum 7 [.int .i8 249, .bool true, .int .u8 9]) 2 =
      .stop (.typeError "TypeError: value does not have the expected type") := rfl

theorem out_of_range_payload_refuses :
    evalExtract model (.int .u64) (.enum 7 (lanes 18446744073709551616)) 2 =
      .stop (.typeError "TypeError: integer value is out of range for the target width") := rfl

theorem declaration_error_precedes_missing_value :
    evalExtract model (.int .u8) (.enum 7 [.int .i8 249]) 2 =
      .stop (.ub "enum lane belongs to no field of the active variant") := rfl

theorem wrong_active_variant_refuses :
    evalExtract model (.int .u64) (.enum 7 [.int .i8 42, .int .u64 9]) 1 =
      .stop (.ub "enum lane belongs to no field of the active variant") := rfl

/-- Value existence/type is not an initialization proof: the existing enum
    extraction preserves this unwritten lane. Inspection must still refuse. -/
theorem unwritten_value_does_not_gain_initialization :
    evalExtract model (.int .u64) (.enum 7 [.int .i8 249, .bool true, .unwritten (.int .u64)]) 2 =
      .ok (.unwritten (.int .u64)) := rfl

theorem comparison_still_refuses_unwritten :
    evalIcmp 64 .uge (.int .u64) (.unwritten (.int .u64)) (.int .u64 1) =
      .stop (.ub "integer use: use of an unwritten aggregate lane (uninit)") := rfl

theorem magnitude_true :
    (do let l ← evalExtract model (.int .u64) (.enum 7 (lanes 9)) 2
        let r ← evalExtract model (.int .u64) (.enum 7 (lanes 3)) 2
        evalIcmp 64 .uge (.int .u64) l r) = .ok (.bool true) := rfl

theorem magnitude_false :
    (do let l ← evalExtract model (.int .u64) (.enum 7 (lanes 3)) 2
        let r ← evalExtract model (.int .u64) (.enum 7 (lanes 9)) 2
        evalIcmp 64 .uge (.int .u64) l r) = .ok (.bool false) := rfl

/-- Future independent consumer negative: the honest read/comparison proof
    cannot justify a different returned value. -/
def WrongReadResult : Prop :=
    evalExtract model (.int .u64) (.enum 7 (lanes 9)) 2 = .ok (.int .u64 10)

theorem wrong_read_result_uninhabited : ¬ WrongReadResult := by intro h; cases h

def readCore : Core :=
  { fn := ⟨0, 0, 0, [], []⟩, sig := ⟨[], [], false⟩, block := ⟨0, [], []⟩,
    pc := 0, env := [(0, .enum 7 (lanes 9))], depth := 8, stack := [],
    openFrames := [], nextFrame := 0, mem := Mem.empty }

theorem actual_ssa_result_and_state :
    extractFieldStep model readCore ⟨.extractField (.int .u64) 0 2, [1]⟩ (.int .u64) 0 2 =
      .ok { next readCore with env := (1, .int .u64 9) :: readCore.env } := rfl

theorem wrong_result_arity_refuses :
    extractFieldStep model readCore ⟨.extractField (.int .u64) 0 2, [1, 2]⟩ (.int .u64) 0 2 =
      .stop (.typeError "MalformedInstruction: instruction result arity mismatch") := rfl

end SemR.EntryDomain.BodyCheck
