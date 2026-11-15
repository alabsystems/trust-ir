/- Existing signed/noncontiguous declaration operations and ordered Switch.
   No Rust source/physical ABI or arbitrary valid-value embedding claim. -/
import SemREnumDiscriminant
namespace SemR.EnumDiscriminantCheck
open SemR EntryDomain
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

def model (pointerBytes : Nat) (signed : Bool := true) : Module :=
  {funcTys := [],functions := [],
   target := some ⟨(if pointerBytes == 4 then "wasm32" else "aarch64").toList.map Char.toNat,
      pointerBytes,false,none,0⟩,
   enums := [⟨7,[⟨[.int .u64]⟩,⟨[.int .u64]⟩],
      if signed then [-7,42] else [250,42],if signed then .i8 else .u8⟩]}
def signedLanes : List Val := [.int .i8 249,.int .u64 91]
def unsignedLanes : List Val := [.int .u8 250,.int .u64 91]

theorem actual_signed_read_32 :
    activeFields (model 4) 7 signedLanes = .ok [.int .u64] ∧
    evalExtract (model 4) (.int .i8) (.enum 7 signedLanes) 0 = .ok (.int .i8 249) ∧
    evalCast 32 .sext (.int .i8) (.int .isize) (.int .i8 249) =
      .ok (.int .isize 4294967289) := ⟨rfl,rfl,rfl⟩
theorem actual_signed_read_64 :
    activeFields (model 8) 7 signedLanes = .ok [.int .u64] ∧
    evalCast 64 .sext (.int .i8) (.int .isize) (.int .i8 249) =
      .ok (.int .isize 18446744073709551609) := ⟨rfl,rfl⟩
/-- The universal declaration-derived contract is actually instantiated here;
    the two run/entry facts below are checked operations, not authored bounds. -/
theorem connected_contract :
    ∃ (d : EnumDef) (i : Nat) (v : Variant),
      findEnum (model 8).enums 7 = some d ∧ d.id = 7 ∧ d ∈ (model 8).enums ∧
      nth? d.discs i = some (-7) ∧ nth? d.variants i = some v ∧
      v.fields = [.int .u64] ∧ 249 < modulus 8 ∧
      evalCast 64 .sext (.int .i8) (.int .isize) (.int .i8 249) =
        .ok (.int .isize 18446744073709551609) :=
  enum_discriminant_cast (m:=model 8) (id:=7) (lanes:=signedLanes) (fields:=[.int .u64]) (t:=.i8) (raw:=249) (destination:=.isize)
    (by rfl) (by rfl) (by decide)

theorem unsigned_high_bit_is_not_signed :
    activeFields (model 8 false) 7 unsignedLanes = .ok [.int .u64] ∧
    evalCast 64 .zext (.int .u8) (.int .isize) (.int .u8 250) = .ok (.int .isize 250) ∧
    evalCast 64 .sext (.int .u8) (.int .isize) (.int .u8 250) =
      .ok (.int .isize 18446744073709551610) := ⟨rfl,rfl,rfl⟩
theorem signed_zero_extension_is_wrong :
    evalCast 64 .zext (.int .i8) (.int .isize) (.int .i8 249) = .ok (.int .isize 249) ∧
    evalCast 64 .zext (.int .i8) (.int .isize) (.int .i8 249) ≠
      evalCast 64 .sext (.int .i8) (.int .isize) (.int .i8 249) := by
  exact ⟨rfl,by intro h; cases h⟩
/-- Ordered Switch case constants use the destination's signed spelling.
    The first matching case owns its successor; the later duplicate cannot win. -/
theorem signed_switch_first_case :
    switchTarget (model 8) (.int .isize 18446744073709551609)
      [(.int (resid 128 (-7)),11,[]),(.int (resid 128 (-7)),12,[]),(.int 42,22,[])] =
      .ok (some (11,[])) := rfl
theorem wrong_extension_switch_misses :
    switchTarget (model 8) (.int .isize 249)
      [(.int (resid 128 (-7)),11,[]),(.int 42,22,[])] = .ok none := rfl

theorem unknown_tag_refuses : activeFields (model 8) 7 [.int .i8 12,.int .u64 91] =
    .stop (.typeError "TypeError: enum tag names no variant") := rfl
theorem unknown_nominal_refuses : activeFields (model 8) 8 signedLanes =
    .stop (.typeError "TypeError: enum id not found in module") := rfl
theorem unbounded_raw_read_refuses :
    evalExtract (model 8) (.int .i8) (.enum 7 [.int .i8 505,.int .u64 91]) 0 =
      .stop (.typeError "TypeError: integer value is out of range for the target width") := rfl
/-- Existing activeFields deliberately does not perform the raw bound check.
    That fact alone must not satisfy the stronger tag-read/cast contract. -/
example : True := by
  fail_if_success
    have bad : evalExtract (model 8) (.int .i8)
      (.enum 7 [.int .i8 505,.int .u64 91]) 0 = .ok (.int .i8 505) := rfl
  trivial
theorem unsigned_entry_source_width_keeps_its_value :
    entryInt (model 8) .usize 32 4294967295 = .ok (.int .usize 4294967295) ∧
    entryInt (model 4) .usize 8 250 = .ok (.int .usize 250) := ⟨rfl,rfl⟩
end SemR.EnumDiscriminantCheck
