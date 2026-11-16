/- Copyright 2026 Andrew Yates. Apache-2.0.
   Original-parser transition and full-goal binding controls. Wrong goals are
   intentionally uninhabited by the corresponding proof, never new axioms. -/
import SemRDecodeCertificate

namespace SemR.DecodeCertificateCheck
open DecodeCertificate

def PureGoal : Prop := Parses (P.pure 7) 0 #[] [8] 7 [8]
theorem pure_control : PureGoal := pure_step 7 0 #[] [8]
def WrongPureGoal : Prop := Parses (P.pure 7) 0 #[] [8] 8 [8]

opaque boundInput : BoundBytes [7, 8] := ⟨[7, 8], rfl⟩
-- Equal expected bytes still do not make distinct opaque inputs interchangeable.
opaque otherBoundInput : BoundBytes [7, 8] := ⟨[7, 8], rfl⟩

def BoundGoal : Prop := boundInput.bytes = [7, 8]
theorem bound_control : BoundGoal := boundInput.equation
def WrongBoundGoal : Prop := boundInput.bytes = [7, 9]
def WrongBoundIdentityGoal : Prop := otherBoundInput.bytes = [7, 8]

def ToBoundGoal : Prop := boundInput.bytes.length = 2
theorem to_bound_control : ToBoundGoal :=
  to_bound (predicate := fun bytes => bytes.length = 2) boundInput rfl
def WrongToBoundGoal : Prop := boundInput.bytes.length = 3

def FromBoundGoal : Prop := ([7, 8] : List Nat).length = 2
theorem from_bound_control : FromBoundGoal :=
  from_bound (predicate := fun bytes => bytes.length = 2) boundInput to_bound_control
def WrongFromBoundGoal : Prop := ([7, 9] : List Nat).length = 3

def SuffixGoal : Prop := ([7, 8, 9] : List Nat) = [7, 8, 9]
theorem suffix_control : SuffixGoal :=
  suffix_exact (actual := [7, 8, 9]) (head := [7, 8]) (tail := [9])
    (expectedHead := [7, 8]) (expectedTail := [9]) (expected := [7, 8, 9])
    rfl rfl rfl rfl
def WrongSuffixOrderGoal : Prop := ([7, 8, 9] : List Nat) = [7, 9, 8]
def WrongSuffixExtraGoal : Prop := ([7, 8, 9] : List Nat) = [7, 8, 9, 0]

def TransGoal : Prop := ∀ (root chain expected : List Nat),
  root = chain → chain = expected → root = expected
theorem trans_control : TransGoal := fun _ _ _ hRoot hChain => trans_exact hRoot hChain
def WrongTransGoal : Prop := ∀ (root chain expected : List Nat),
  root = chain → chain = expected → root = 0 :: expected

def ToBoundFromGoal : Prop := boundInput.bytes.length = 2
theorem to_bound_from_control : ToBoundFromGoal :=
  to_bound_from (actual := [7, 8]) (predicate := fun bytes => bytes.length = 2)
    rfl boundInput rfl
def WrongToBoundFromGoal : Prop := boundInput.bytes.length = 3
def WrongToBoundFromIdentityGoal : Prop := otherBoundInput.bytes.length = 2

def ByteGoal : Prop := Parses u8 0 #[] [7, 8] 7 [8]
theorem byte_control : ByteGoal := rfl
def WrongByteGoal : Prop := Parses u8 0 #[] [7, 8] 8 [8]

def BindGoal : Prop :=
  Parses (P.bind u8 (fun first => P.map (fun second => first + second) u8))
    0 #[] [7, 8, 9] 15 [9]
theorem bind_control : BindGoal := by
  have head : Parses u8 0 #[] [7, 8, 9] 7 [8, 9] := rfl
  have tail : Parses u8 0 #[] [8, 9] 8 [9] := rfl
  exact bind_step head (map_step (f := fun second => 7 + second) tail)
def WrongBindGoal : Prop :=
  Parses (P.bind u8 (fun first => P.map (fun second => first + second) u8))
    0 #[] [7, 8, 9] 14 [9]

def PrefixGoal : Prop := Parses (rep 3 u8) 0 #[] [7, 8, 9, 10] [7, 8, 9] [10]
theorem prefix_control : PrefixGoal := bytes_step [7, 8, 9] [10] 0 #[]
def WrongPrefixGoal : Prop := Parses (rep 3 u8) 0 #[] [7, 8, 9, 10] [7, 9, 8] [10]
def WrongSuffixGoal : Prop := Parses (rep 3 u8) 0 #[] [7, 8, 9, 10] [7, 8, 9] [10, 11]

def LengthGoal : Prop := (([7, 8] : List Nat) ++ [9]).length = 3
theorem length_control : LengthGoal := append_length rfl rfl
def WrongLengthGoal : Prop := (([7, 8] : List Nat) ++ [9]).length = 4

def RemainingGoal : Prop := Parses remaining 0 #[] [7, 8, 9] 3 [7, 8, 9]
theorem remaining_control : RemainingGoal := remaining_step rfl
def WrongRemainingGoal : Prop := Parses remaining 0 #[] [7, 8, 9] 4 [7, 8, 9]

def FailureGoal : Prop :=
  P.bind u8 (fun byte => P.pure byte) 0 #[] [] =
    .err (.malformed "unexpected end of input")
theorem failure_control : FailureGoal := bind_error rfl
def WrongFailureGoal : Prop := P.bind u8 (fun byte => P.pure byte) 0 #[] [] = .ok 0 []

def DecodeGoal : Prop := ∀ (bytes : List Nat) (decoded : Module),
  Witness bytes decoded → decode bytes = .ok decoded
theorem decode_control : DecodeGoal := fun _ _ witness => decode_exact witness
def WrongDecodeGoal : Prop := ∀ (bytes : List Nat) (decoded : Module),
  Witness bytes decoded → decode (0 :: bytes) = .ok decoded

def ConjunctionGoal : Prop := ∀ (bytes : List Nat) (decoded : Module) (fid : Nat),
  Witness bytes decoded →
  (BoolBody.checkConjunction decoded fid).isSome = true →
  ∀ (a b : Bool) (depth : Nat),
  runBlob bytes fid [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a && b)])
theorem conjunction_control : ConjunctionGoal :=
  fun _ _ _ witness accepted a b depth => conjunction witness accepted a b depth
def WrongFunctionGoal : Prop := ∀ (bytes : List Nat) (decoded : Module) (fid : Nat),
  Witness bytes decoded →
  (BoolBody.checkConjunction decoded fid).isSome = true →
  ∀ (a b : Bool) (depth : Nat),
  runBlob bytes (fid + 1) [.bool a, .bool b] 2 depth = .ok (.ret [.bool (a && b)])

end SemR.DecodeCertificateCheck
