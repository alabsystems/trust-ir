/- Copyright 2026 Andrew Yates. Apache-2.0.
   Composition facts for the original v38–v70 SemR parser. Every premise is
   an ordinary original-parser or data equation; no native parse result,
   claimed length, decoder-policy change or new reduction rule is admitted. -/
import SemRDecodeCertificate

namespace SemR.ParserCertificate
open DecodeCertificate

/-- Reuse a transition only through checked input, value and suffix equations.
    In particular an alleged cursor may not skip or duplicate input bytes. -/
theorem transport {α : Type} {parser : P α} {wire : Nat}
    {pool : Array (List Nat)} {before expectedBefore after expectedAfter : List Nat}
    {value expectedValue : α}
    (inputExact : before = expectedBefore) (valueExact : value = expectedValue)
    (suffixExact : after = expectedAfter)
    (step : Parses parser wire pool expectedBefore expectedValue expectedAfter) :
    Parses parser wire pool before value after := by
  simpa only [inputExact, valueExact, suffixExact] using step

/-- An empty repetition consumes no byte and returns no element. -/
theorem rep_zero {α : Type} (parser : P α) (wire : Nat)
    (pool : Array (List Nat)) (bytes : List Nat) :
    Parses (rep 0 parser) wire pool bytes [] bytes := rfl

/-- One checked element and the exact checked remainder compose in order. -/
theorem rep_cons {α : Type} {parser : P α} {wire : Nat}
    {pool : Array (List Nat)} {before middle after : List Nat}
    {first : α} {values : List α} {count : Nat}
    (head : Parses parser wire pool before first middle)
    (tail : Parses (rep count parser) wire pool middle values after) :
    Parses (rep (count + 1) parser) wire pool before (first :: values) after := by
  unfold Parses at head tail ⊢
  change P.bind parser (fun value =>
    P.bind (rep count parser) (fun rest => P.pure (value :: rest)))
    wire pool before = .ok (first :: values) after
  simp only [P.bind, head, tail, P.pure]

/-- The original repetition parser splits into two ordered repetitions.
    This is an equation of the original parsers, including error outcomes. -/
theorem rep_append_eq {α : Type} (leftCount rightCount : Nat) (parser : P α) :
    rep (leftCount + rightCount) parser =
      P.bind (rep leftCount parser) (fun left =>
        P.map (fun right => left ++ right) (rep rightCount parser)) := by
  induction leftCount with
  | zero =>
    rw [Nat.zero_add]
    funext wire pool bytes
    change rep rightCount parser wire pool bytes =
      P.bind (P.pure []) (fun left =>
        P.map (fun right => left ++ right) (rep rightCount parser)) wire pool bytes
    simp only [P.bind, P.pure, P.map]
    cases hRight : rep rightCount parser wire pool bytes <;>
      simp only [hRight, List.nil_append]
  | succ leftCount ih =>
    rw [Nat.succ_add]
    change P.bind parser (fun first =>
      P.bind (rep (leftCount + rightCount) parser)
        (fun values => P.pure (first :: values))) =
      P.bind (P.bind parser (fun first =>
        P.bind (rep leftCount parser) (fun values => P.pure (first :: values))))
        (fun left => P.map (fun right => left ++ right) (rep rightCount parser))
    rw [ih]
    funext wire pool bytes
    simp only [P.bind, P.map, P.pure]
    cases hParser : parser wire pool bytes with
    | err error => simp only [hParser]
    | ok first rest =>
      simp only [hParser]
      cases hLeft : rep leftCount parser wire pool rest with
      | err error => simp only [hLeft]
      | ok left middle =>
        simp only [hLeft]
        cases hRight : rep rightCount parser wire pool middle <;>
          simp only [hRight, List.cons_append]

/-- Checked repetition chunks meet at the same suffix and retain both counts.
    Neither a native count nor concatenation of unchecked parser results is
    evidence for this transition. -/
theorem rep_append {α : Type} {parser : P α} {wire : Nat}
    {pool : Array (List Nat)} {before middle after : List Nat}
    {left right : List α} {leftCount rightCount : Nat}
    (head : Parses (rep leftCount parser) wire pool before left middle)
    (tail : Parses (rep rightCount parser) wire pool middle right after) :
    Parses (rep (leftCount + rightCount) parser) wire pool before (left ++ right) after := by
  unfold Parses at head tail ⊢
  rw [rep_append_eq leftCount rightCount parser]
  simp only [P.bind, P.map, head, tail]

/-- Read exact quoted data using its independently proved length. The length
    equation replaces a repeated length reduction, not the original byte read. -/
theorem bytes_step_of_length {bytes rest : List Nat} {length wire : Nat}
    {pool : Array (List Nat)} (lengthExact : bytes.length = length) :
    Parses (rep length u8) wire pool (bytes ++ rest) bytes rest := by
  rw [← lengthExact]
  exact bytes_step bytes rest wire pool

/-- The original checked count still reads its own v32 and checks it against
    the length of the exact suffix left by that read. -/
theorem checkedLen_step {wire : Nat} {pool : Array (List Nat)}
    {before after : List Nat} {count available : Nat}
    (read : Parses v32 wire pool before count after)
    (lengthExact : after.length = available) (within : count ≤ available) :
    Parses checkedLen wire pool before count after := by
  unfold Parses at read ⊢
  change P.bind v32 (fun n => P.bind remaining (fun available =>
    if n ≤ available then P.pure n else bad "declared count exceeds the input"))
    wire pool before = .ok count after
  simp only [P.bind, read, remaining, lengthExact, within, P.pure,
    ↓reduceIte]

/-- An oversized count remains the original failure, even when its varint
    itself is well formed. -/
theorem checkedLen_error {wire : Nat} {pool : Array (List Nat)}
    {before after : List Nat} {count available : Nat}
    (read : Parses v32 wire pool before count after)
    (lengthExact : after.length = available) (outside : ¬ count ≤ available) :
    checkedLen wire pool before = .err (.malformed "declared count exceeds the input") := by
  unfold Parses at read
  change P.bind v32 (fun n => P.bind remaining (fun available =>
    if n ≤ available then P.pure n else bad "declared count exceeds the input"))
    wire pool before = .err (.malformed "declared count exceeds the input")
  simp only [P.bind, read, remaining, lengthExact, outside,
    ↓reduceIte, bad]

/-- A raw string retains the checked count, every byte, the exact suffix and
    the original UTF-8 predicate. -/
theorem rawStr_step {wire : Nat} {pool : Array (List Nat)}
    {before afterCount after bytes : List Nat} {count : Nat}
    (countRead : Parses checkedLen wire pool before count afterCount)
    (bytesRead : Parses (rep count u8) wire pool afterCount bytes after)
    (valid : utf8Ok bytes.length bytes = true) :
    Parses rawStr wire pool before bytes after := by
  unfold Parses at countRead bytesRead ⊢
  change P.bind checkedLen (fun count => P.bind (rep count u8) (fun bytes =>
    if utf8Ok bytes.length bytes then P.pure bytes else bad "invalid UTF-8"))
    wire pool before = .ok bytes after
  simp only [P.bind, countRead, bytesRead, valid, P.pure,
    ↓reduceIte]

/-- The UTF-8 fuel can also use the checked payload length. Its equality to
    the original length remains an explicit proof premise. -/
theorem rawStr_step_of_length {wire : Nat} {pool : Array (List Nat)}
    {before afterCount after bytes : List Nat} {count : Nat}
    (countRead : Parses checkedLen wire pool before count afterCount)
    (bytesRead : Parses (rep count u8) wire pool afterCount bytes after)
    (lengthExact : bytes.length = count) (valid : utf8Ok count bytes = true) :
    Parses rawStr wire pool before bytes after := by
  apply rawStr_step countRead bytesRead
  simpa only [lengthExact] using valid

/-- Invalid UTF-8 remains the original failure after successful count and
    byte transitions. Advice cannot classify a raw byte string as text. -/
theorem rawStr_error {wire : Nat} {pool : Array (List Nat)}
    {before afterCount after bytes : List Nat} {count : Nat}
    (countRead : Parses checkedLen wire pool before count afterCount)
    (bytesRead : Parses (rep count u8) wire pool afterCount bytes after)
    (invalid : utf8Ok bytes.length bytes = false) :
    rawStr wire pool before = .err (.malformed "invalid UTF-8") := by
  unfold Parses at countRead bytesRead
  change P.bind checkedLen (fun count => P.bind (rep count u8) (fun bytes =>
    if utf8Ok bytes.length bytes then P.pure bytes else bad "invalid UTF-8"))
    wire pool before = .err (.malformed "invalid UTF-8")
  simp only [P.bind, countRead, bytesRead, invalid,
    Bool.false_eq_true, ↓reduceIte, bad]

end SemR.ParserCertificate
