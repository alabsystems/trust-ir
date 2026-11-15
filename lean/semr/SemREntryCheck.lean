/- Copyright 2026 Andrew Yates. Apache-2.0.
   Operational controls for the exact enum entry contracts, not source
   certificates or native execution/initialization authority. -/
import SemREntry

namespace SemR.EntryDomain.Check

open SemR

def model : Module :=
  { funcTys := [], functions := [], enums := [
    { id := 7, tag := .i8, discs := [-7, 42],
      variants := [⟨[.bool, .int .u64]⟩, ⟨[.int .u8]⟩] }] }

theorem negative_noncontiguous_tag :
    activeFields model 7 [.int .i8 249] = .ok [.bool, .int .u64] := rfl

theorem positive_noncontiguous_tag :
    activeFields model 7 [.int .i8 42] = .ok [.int .u8] := rfl

theorem wrong_nominal_id :
    activeFields model 8 [.int .i8 249] = .stop (.typeError "TypeError: enum id not found in module") := rfl

theorem missing_tag_lane :
    activeFields model 7 [] = .stop (.typeError "TypeError: enum value has no integer tag lane") := rfl

theorem boolean_is_not_an_integer_tag :
    activeFields model 7 [.bool true] = .stop (.typeError "TypeError: enum value has no integer tag lane") := rfl

theorem unknown_tag :
    activeFields model 7 [.int .i8 43] = .stop (.typeError "TypeError: enum tag names no variant") := rfl

theorem payload_first_ordinal : checkLane model 7 [.int .i8 249] 1 .bool = .ok () := rfl

theorem payload_second_ordinal :
    checkLane model 7 [.int .i8 249] 2 (.int .u64) = .ok () := rfl

theorem wrong_payload_ordinal :
    checkLane model 7 [.int .i8 249] 1 (.int .u64) =
      .stop (.ub "enum lane belongs to no field of the active variant") := rfl

theorem inactive_variant_field :
    checkLane model 7 [.int .i8 42] 1 .bool =
      .stop (.ub "enum lane belongs to no field of the active variant") := rfl

theorem missing_payload_ordinal :
    checkLane model 7 [.int .i8 42] 2 (.int .u64) =
      .stop (.ub "enum lane belongs to no field of the active variant") := rfl

/-- Successful active-field lookup is not a bit-normalization certificate. -/
theorem noncanonical_raw_can_succeed :
    activeFields model 7 [.int .i8 298] = .ok [.int .u8] := rfl

theorem noncanonical_raw_exceeds_word : ¬ 298 < modulus 8 := by decide

/-- readInt is used as defined: masking this raw pattern would select -7. -/
theorem raw_bits_are_not_silently_masked :
    activeFields model 7 [.int .i8 505] = .stop (.typeError "TypeError: enum tag names no variant") := rfl

/-- The successful lookup did not establish that the lane uses d.tag. -/
theorem noncanonical_lane_type_can_succeed :
    activeFields model 7 [.int .u16 42] = .ok [.int .u8] := rfl

/-- checkLane checks the declaration; it does not supply missing value lanes. -/
theorem missing_payload_value_refuses_extract :
    evalExtract model .bool (.enum 7 [.int .i8 249]) 1 =
      .stop (.ub "field is out of bounds") := rfl

/-- A negative consumer question. The honest declared-field proof above cannot
    inhabit this stronger value-existence claim in an independent checker. -/
def WrongPayloadValue : Prop :=
  evalExtract model .bool (.enum 7 [.int .i8 249]) 1 = .ok (.bool false)

theorem wrong_payload_value_uninhabited : ¬ WrongPayloadValue := by
  intro h
  cases h

/-- Pointer-size cases are mathematical input data, not target execution. -/
def pointerModel (bytes : Nat) : Module :=
  { model with
    target := some ⟨[], bytes, false, none, 0⟩,
    enums := [⟨7, [⟨[.bool, .int .u64]⟩, ⟨[.int .u8]⟩], [-7, 42], .isize⟩] }


theorem pointer_width_32_signed_read :
    activeFields (pointerModel 4) 7 [.int .isize 4294967289] = .ok [.bool, .int .u64] := rfl

theorem pointer_width_64_signed_read :
    activeFields (pointerModel 8) 7 [.int .isize 18446744073709551609] =
      .ok [.bool, .int .u64] := rfl

end SemR.EntryDomain.Check
