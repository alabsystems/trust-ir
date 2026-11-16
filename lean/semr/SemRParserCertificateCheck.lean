/- Copyright 2026 Andrew Yates. Apache-2.0.
   Closed controls for the original v38–v70 parser composition facts.
   Negative goals deliberately change actual counts, order, suffixes or
   branch outcomes; they are not axioms or expected proof successes. -/
import SemRParserCertificate
import SemRDecodeCertificateCheck

namespace SemR.ParserCertificateCheck
open DecodeCertificate ParserCertificate

def TransportGoal : Prop := Parses u8 70 #[] [7, 8] 7 [8]
theorem transport_control : TransportGoal := transport rfl rfl rfl rfl
def WrongTransportInputGoal : Prop := Parses u8 70 #[] [9, 8] 7 [8]
def WrongTransportSuffixGoal : Prop := Parses u8 70 #[] [7, 8] 7 [8, 0]

def RepZeroGoal : Prop := Parses (rep 0 u8) 70 #[] [8] [] [8]
theorem rep_zero_control : RepZeroGoal := rep_zero u8 70 #[] [8]
def WrongRepZeroCountGoal : Prop := Parses (rep 1 u8) 70 #[] [8] [] [8]
def WrongRepZeroSuffixGoal : Prop := Parses (rep 0 u8) 70 #[] [8] [] []

def RepConsGoal : Prop := Parses (rep 3 u8) 70 #[] [7, 8, 9, 10] [7, 8, 9] [10]
theorem rep_cons_control : RepConsGoal := rep_cons (count := 2) rfl rfl
def WrongRepConsCountGoal : Prop :=
  Parses (rep 2 u8) 70 #[] [7, 8, 9, 10] [7, 8, 9] [10]
def WrongRepConsOrderGoal : Prop :=
  Parses (rep 3 u8) 70 #[] [7, 8, 9, 10] [7, 9, 8] [10]

def RepAppendEqGoal : Prop := ∀ (leftCount rightCount : Nat) (parser : P Nat),
  rep (leftCount + rightCount) parser =
    P.bind (rep leftCount parser) (fun left =>
      P.map (fun right => left ++ right) (rep rightCount parser))
theorem rep_append_eq_control : RepAppendEqGoal := rep_append_eq
def WrongRepAppendEqOrderGoal : Prop := ∀ (leftCount rightCount : Nat) (parser : P Nat),
  rep (leftCount + rightCount) parser =
    P.bind (rep leftCount parser) (fun left =>
      P.map (fun right => right ++ left) (rep rightCount parser))

def RepAppendGoal : Prop :=
  Parses (rep 4 u8) 70 #[] [7, 8, 9, 10, 11] ([7, 8] ++ [9, 10]) [11]
theorem rep_append_control : RepAppendGoal :=
  rep_append (leftCount := 2) (rightCount := 2)
    (bytes_step [7, 8] [9, 10, 11] 70 #[])
    (bytes_step [9, 10] [11] 70 #[])
def WrongRepAppendCountGoal : Prop :=
  Parses (rep 3 u8) 70 #[] [7, 8, 9, 10, 11] [7, 8, 9, 10] [11]
def WrongRepAppendOrderGoal : Prop :=
  Parses (rep 4 u8) 70 #[] [7, 8, 9, 10, 11] [7, 9, 8, 10] [11]
def WrongRepAppendSuffixGoal : Prop :=
  Parses (rep 4 u8) 70 #[] [7, 8, 9, 10, 11] [7, 8, 9, 10] [10, 11]

def BytesLengthGoal : Prop :=
  Parses (rep 3 u8) 70 #[] ([7, 8, 9] ++ [10]) [7, 8, 9] [10]
theorem bytes_length_control : BytesLengthGoal := bytes_step_of_length rfl
def WrongBytesLengthCountGoal : Prop :=
  Parses (rep 4 u8) 70 #[] [7, 8, 9, 10] [7, 8, 9] [10]
def WrongBytesLengthOrderGoal : Prop :=
  Parses (rep 3 u8) 70 #[] [7, 8, 9, 10] [9, 8, 7] [10]
def WrongBytesLengthSuffixGoal : Prop :=
  Parses (rep 3 u8) 70 #[] [7, 8, 9, 10] [7, 8, 9] [10, 11]

def CheckedLenGoal : Prop := Parses checkedLen 70 #[] [2, 42, 43, 44] 2 [42, 43, 44]
theorem checked_len_control : CheckedLenGoal :=
  checkedLen_step (available := 3) rfl rfl (by decide)
def WrongCheckedLenCountGoal : Prop :=
  Parses checkedLen 70 #[] [2, 42, 43, 44] 3 [42, 43, 44]
def WrongCheckedLenSuffixGoal : Prop :=
  Parses checkedLen 70 #[] [2, 42, 43, 44] 2 [42, 43]
def WrongCheckedLenBoundsGoal : Prop :=
  Parses checkedLen 70 #[] [4, 42, 43] 4 [42, 43]

def CheckedLenErrorGoal : Prop :=
  checkedLen 70 #[] [4, 42, 43] = .err (.malformed "declared count exceeds the input")
theorem checked_len_error_control : CheckedLenErrorGoal :=
  checkedLen_error (count := 4) (available := 2) rfl rfl (by decide)
def WrongCheckedLenErrorPayloadGoal : Prop :=
  checkedLen 70 #[] [4, 42, 43] = .err (.malformed "varint overflow")

def RawStrGoal : Prop := Parses rawStr 70 #[] [2, 194, 162, 9] [194, 162] [9]
/-- Ordinary constructor-normal proof data. The reference harness must check
    this against the unchanged parser proposition `RawStrGoal` before using
    it for any wrong-goal comparison; the constructor equation is no token. -/
theorem raw_str_control :
    (DRes.ok [194, 162] [9] : DRes (List Nat)) = DRes.ok [194, 162] [9] := rfl

/-- Retain the compositional proof of that same original parser proposition. -/
theorem raw_str_step_control : RawStrGoal :=
  rawStr_step (count := 2)
    (checkedLen_step (available := 3) rfl rfl (by decide))
    (bytes_step_of_length (bytes := [194, 162]) (rest := [9]) (length := 2) rfl) rfl
def WrongRawStrBytesGoal : Prop :=
  Parses rawStr 70 #[] [2, 194, 162, 9] [194, 163] [9]
def WrongRawStrSuffixGoal : Prop :=
  Parses rawStr 70 #[] [2, 194, 162, 9] [194, 162] [9, 0]
def WrongRawStrCountGoal : Prop :=
  Parses rawStr 70 #[] [1, 194, 162, 9] [194, 162] [9]
def WrongRawStrUtf8Goal : Prop :=
  Parses rawStr 70 #[] [1, 128, 9] [128] [9]

def RawStrLengthGoal : Prop := Parses rawStr 70 #[] [2, 194, 162, 9] [194, 162] [9]
theorem raw_str_length_control : RawStrLengthGoal :=
  rawStr_step_of_length (count := 2)
    (checkedLen_step (available := 3) rfl rfl (by decide))
    (bytes_step_of_length (bytes := [194, 162]) (rest := [9]) (length := 2) rfl) rfl rfl
def WrongRawStrLengthGoal : Prop :=
  Parses rawStr 70 #[] [2, 194, 162, 9] [194, 162, 9] []

def RawStrErrorGoal : Prop :=
  rawStr 70 #[] [1, 128, 9] = .err (.malformed "invalid UTF-8")
theorem raw_str_error_control : RawStrErrorGoal :=
  rawStr_error (count := 1) (bytes := [128]) (after := [9])
    (checkedLen_step (available := 2) rfl rfl (by decide))
    (bytes_step_of_length (bytes := [128]) (rest := [9]) (length := 1) rfl) rfl
def WrongRawStrErrorPayloadGoal : Prop :=
  rawStr 70 #[] [1, 128, 9] = .err (.malformed "unexpected end of input")

end SemR.ParserCertificateCheck
