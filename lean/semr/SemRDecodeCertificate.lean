/- Copyright 2026 Andrew Yates. Apache-2.0.
   Compositional certificates for the original decoder. Each transition is
   an equation checked by the kernel; a native parse result supplies none.
   No byte subject, decoder branch, resource limit or execution goal changes. -/
import SemRBoolBodyChecker
import SemRByteBinding

namespace SemR.DecodeCertificate

/-- A successful original parser transition, including its exact unconsumed
    suffix. Both sides remain ordinary applications of the original parser. -/
def Parses {α : Type} (parser : P α) (wire : Nat)
    (pool : Array (List Nat)) (before : List Nat) (value : α)
    (after : List Nat) : Prop :=
  parser wire pool before = .ok value after

theorem pure_step {α : Type} (value : α) (wire : Nat)
    (pool : Array (List Nat)) (bytes : List Nat) :
    Parses (P.pure value) wire pool bytes value bytes := rfl

theorem bind_step {α β : Type} {parser : P α} {next : α → P β}
    {wire : Nat} {pool : Array (List Nat)} {before middle after : List Nat}
    {first : α} {last : β}
    (head : Parses parser wire pool before first middle)
    (tail : Parses (next first) wire pool middle last after) :
    Parses (P.bind parser next) wire pool before last after := by
  unfold Parses at *
  simp only [P.bind, head, tail]

theorem map_step {α β : Type} {parser : P α} {f : α → β}
    {wire : Nat} {pool : Array (List Nat)} {before after : List Nat}
    {value : α} (step : Parses parser wire pool before value after) :
    Parses (P.map f parser) wire pool before (f value) after := by
  unfold Parses at *
  simp only [P.map, step]

/-- An original parser failure propagates through sequencing. Advice cannot
    turn a malformed/unsupported prefix into a successful composed parse. -/
theorem bind_error {α β : Type} {parser : P α} {next : α → P β}
    {wire : Nat} {pool : Array (List Nat)} {before : List Nat} {error : DErr}
    (failed : parser wire pool before = .err error) :
    P.bind parser next wire pool before = .err error := by
  simp only [P.bind, failed]

/-- Reading a complete quoted prefix preserves every byte and the exact
    suffix. This universal lemma permits checked chunks instead of a proof
    containing a separate reduction for each byte of the complete module. -/
theorem bytes_step (bytes rest : List Nat) (wire : Nat)
    (pool : Array (List Nat)) :
    Parses (rep bytes.length u8) wire pool (bytes ++ rest) bytes rest := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    unfold Parses at ih ⊢
    change P.bind u8 (fun first =>
      P.bind (rep bytes.length u8) (fun tail => P.pure (first :: tail)))
      wire pool ((byte :: bytes) ++ rest) = .ok (byte :: bytes) rest
    simp only [List.cons_append, P.bind, u8, ih, P.pure]

/-- Length evidence composes without traversing an already checked suffix. -/
theorem append_length {left right : List Nat} {leftLength rightLength : Nat}
    (leftExact : left.length = leftLength)
    (rightExact : right.length = rightLength) :
    (left ++ right).length = leftLength + rightLength := by
  simp only [List.length_append, leftExact, rightExact]

/-- A separately checked length equation can be reused at a remaining-bytes
    query. It is not a claimed length or a native cached parser result. -/
theorem remaining_step {wire : Nat} {pool : Array (List Nat)}
    {bytes : List Nat} {length : Nat} (hLength : bytes.length = length) :
    Parses remaining wire pool bytes length bytes := by
  simp only [Parses, remaining, hLength]

/-- The equations demanded by every branch of the original `decode`, including
    the original full `moduleBody` check. The suffix identities connect the
    stages; witnesses cannot omit, reorder or replace any input bytes. -/
structure Witness (bytes : List Nat) (decoded : Module) where
  wire : Nat
  stringCount : Nat
  strings : List (List Nat)
  afterVersion : List Nat
  afterCount : List Nat
  afterStrings : List Nat
  afterBody : List Nat
  magic : (bytes.take 8 != SemR.magic) = false
  version : Parses u32 0 #[] (bytes.drop 8) wire afterVersion
  supported : (wire < 38 || 70 < wire) = false
  count : Parses checkedLen wire #[] afterVersion stringCount afterCount
  pool : Parses (rep stringCount rawStr) wire #[] afterCount strings afterStrings
  body : Parses moduleBody wire strings.toArray afterStrings decoded afterBody

/-- Compose checked transitions into the complete original decoder equation.
    This theorem does no native parsing and adds no axiom or evaluator rule. -/
theorem decode_exact {bytes : List Nat} {decoded : Module}
    (witness : Witness bytes decoded) : decode bytes = .ok decoded := by
  obtain ⟨wire, count, strings, afterVersion, afterCount, afterStrings,
    afterBody, magic, version, supported, length, pool, body⟩ := witness
  simp only [Parses] at version length pool body
  simp only [decode, magic, Bool.false_eq_true, ↓reduceIte, version,
    supported, length, pool, body]

/-- The final equation is the same universally quantified full-byte root
    execution claim as `checked_blob`; its decoder premise is now compositional.
    Body acceptance is still an independently checked original predicate. -/
theorem conjunction {bytes : List Nat} {decoded : Module} {fid : Nat}
    (witness : Witness bytes decoded)
    (accepted : (BoolBody.checkConjunction decoded fid).isSome = true)
    (a b : Bool) (depth : Nat) :
    runBlob bytes fid [.bool a, .bool b] 2 depth =
      .ok (.ret [.bool (a && b)]) := by
  simp only [runBlob, decode_exact witness]
  exact congrArg Except.ok (BoolBody.checked_body accepted a b depth)

end SemR.DecodeCertificate
