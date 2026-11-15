-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYDivisionInvariant

namespace TrustIr.AYGateCNF

/-- One program owns both results. Quotient references are least significant
first; each new source bit prepends the actual subtraction carry. -/
structure DivisionCode (width : Nat) where
  remainder : WordCode width
  quotient : List Nat

def DivisionCode.check {width : Nat} (code : DivisionCode width) (next : Nat) : Bool :=
  code.remainder.check next &&
    code.quotient.all (fun id => decide (id < next+code.remainder.gates.length))

theorem DivisionCode.check_iff {width : Nat} (code : DivisionCode width) (next : Nat) :
    code.check next = true ↔ code.remainder.check next = true ∧
      ∀ id ∈ code.quotient, id < next+code.remainder.gates.length := by
  simp [DivisionCode.check, Bool.and_eq_true]

/-- Narrow only after the entire wide trial has been compared and subtracted.
The flag still refers to the same wide graph, and narrowing emits one gate. -/
def WordCode.divisionRound {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat) : WordCode width :=
  let wide := WordCode.restoringStep divisor remainder bit next
  WordCode.append wide (WordCode.resize width wide.bits (next+wide.gates.length))

theorem WordCode.divisionRound_check {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next) :
    (WordCode.divisionRound divisor remainder bit next).check next = true := by
  have checked := WordCode.restoringStep_check divisor remainder bit next divisorBound remainderBound bitBound
  exact WordCode.append_check _ _ _ checked (WordCode.resize_check _ _ _ ((WordCode.check_iff _ _).mp checked).2)

theorem WordCode.divisionRound_length {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat) :
    (WordCode.divisionRound divisor remainder bit next).gates.length = 6*width+10 := by
  simp only [WordCode.divisionRound, WordCode.append, List.length_append, WordCode.restoringStep_length,
    WordCode.resize, WordCode.route, List.length_cons, List.length_nil]

theorem WordCode.divisionRound_numeric {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) :
    ((WordCode.divisionRound divisor remainder bit next).value env).toNat =
      ((WordCode.restoringStep divisor remainder bit next).value env).toNat % 2^width := by
  have checked := WordCode.restoringStep_check divisor remainder bit next divisorBound remainderBound bitBound
  rw [WordCode.divisionRound, WordCode.append_value, WordCode.resize_value _ _ _ ((WordCode.check_iff _ _).mp checked).2]
  exact (trustIrWidthLemma BitVec.toNat_zeroExtend BitVec.toNat_setWidth) _ _

theorem WordCode.divisionRound_flag {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) :
    run (WordCode.divisionRound divisor remainder bit next).gates env
        (Code.restoringFlag divisor remainder bit next).output =
      (Code.restoringFlag divisor remainder bit next).eval env := by
  have checked := WordCode.restoringStep_check divisor remainder bit next divisorBound remainderBound bitBound
  have flagCheck := Code.restoringFlag_check divisor remainder bit next divisorBound remainderBound bitBound
  have flagBound := ((Code.check_iff _ _).mp flagCheck).2
  rw [Code.restoringFlag_gates] at flagBound
  have narrow := WordCode.resize_check width _ _ ((WordCode.check_iff _ _).mp checked).2
  rw [WordCode.divisionRound, WordCode.append, run_append]
  rw [(((WordCode.check_iff _ _).mp narrow).1.run_correct _).1 _ flagBound]
  rw [← Code.restoringFlag_gates]
  rfl

def DivisionCode.step {width : Nat} (divisor : Fin width → Nat) (bit next : Nat)
    (prior : DivisionCode width) : DivisionCode width :=
  let frontier := next+prior.remainder.gates.length
  let round := WordCode.divisionRound divisor prior.remainder.bits bit frontier
  ⟨WordCode.append prior.remainder round,
    (Code.restoringFlag divisor prior.remainder.bits bit frontier).output :: prior.quotient⟩

theorem DivisionCode.step_check {width : Nat} (divisor : Fin width → Nat) (bit next : Nat)
    (prior : DivisionCode width) (checked : prior.check next = true)
    (divisorBound : ∀ i, divisor i < next) (bitBound : bit < next) :
    (DivisionCode.step divisor bit next prior).check next = true := by
  obtain ⟨wordCheck, quotientBound⟩ := (DivisionCode.check_iff _ _).mp checked
  have wordBounds := ((WordCode.check_iff _ _).mp wordCheck).2
  have later : ∀ i, divisor i < next+prior.remainder.gates.length := by
    intro i; have before := divisorBound i; omega
  have bitLater : bit < next+prior.remainder.gates.length := by omega
  have roundCheck := WordCode.divisionRound_check divisor prior.remainder.bits bit _ later wordBounds bitLater
  apply (DivisionCode.check_iff _ _).mpr
  refine ⟨WordCode.append_check _ _ _ wordCheck roundCheck, ?_⟩
  intro id member
  change id ∈ _ :: prior.quotient at member
  rcases List.mem_cons.mp member with same | old
  · subst id
    have flagCheck := Code.restoringFlag_check divisor prior.remainder.bits bit _ later wordBounds bitLater
    have flagBound := ((Code.check_iff _ _).mp flagCheck).2
    rw [Code.restoringFlag_gates, WordCode.restoringStep_length] at flagBound
    simp only [DivisionCode.step, WordCode.append, List.length_append, WordCode.divisionRound_length]
    omega
  · have before := quotientBound id old
    simp only [DivisionCode.step, WordCode.append, List.length_append]
    omega

/-- Consume source references in most-significant-first order. Every round
appends to the one program and retains the actual carry as a quotient bit. -/
def DivisionCode.rows {width : Nat} (divisor : Fin width → Nat) (source : List Nat) (next : Nat)
    (initial : DivisionCode width) : DivisionCode width :=
  source.foldl (fun prior bit => DivisionCode.step divisor bit next prior) initial

theorem DivisionCode.rows_check {width : Nat} (divisor : Fin width → Nat) (source : List Nat) (next : Nat)
    (initial : DivisionCode width) (checked : initial.check next = true)
    (divisorBound : ∀ i, divisor i < next) (sourceBound : ∀ bit ∈ source, bit < next) :
    (DivisionCode.rows divisor source next initial).check next = true := by
  induction source generalizing initial with
  | nil => exact checked
  | cons bit rest ih =>
    exact ih (DivisionCode.step divisor bit next initial)
      (DivisionCode.step_check _ _ _ _ checked divisorBound (sourceBound _ (List.Mem.head _)))
      (fun id member => sourceBound id (List.Mem.tail _ member))

def DivisionCode.value {width : Nat} (code : DivisionCode width) (env : Assignment) : Nat × Nat :=
  (wireNumber code.quotient (run code.remainder.gates env), (code.remainder.value env).toNat)

def divisionTransition (width divisor : Nat) (bit : Bool) (prior : Nat × Nat) : Nat × Nat :=
  let trial := 2*prior.2+bit.toNat
  let take := decide (divisor ≤ trial)
  (2*prior.1+take.toNat, (if divisor ≤ trial then trial-divisor else trial) % 2^width)

theorem wireNumber_congr (wires : List Nat) (left right : Assignment)
    (same : ∀ id ∈ wires, left id = right id) : wireNumber wires left = wireNumber wires right := by
  induction wires with
  | nil => rfl
  | cons bit rest ih =>
    change (left bit).toNat + 2*wireNumber rest left = (right bit).toNat + 2*wireNumber rest right
    rw [same bit (List.Mem.head _), ih (fun id member => same id (List.Mem.tail _ member))]

theorem WordCode.restoringStep_toNat {width : Nat} (divisor remainder : Fin width → Nat) (bit next : Nat)
    (divisorBound : ∀ i, divisor i < next) (remainderBound : ∀ i, remainder i < next) (bitBound : bit < next)
    (env : Assignment) :
    ((WordCode.restoringStep divisor remainder bit next).value env).toNat =
      let trial := 2*(wordValue remainder env).toNat+(env bit).toNat
      let d := (wordValue divisor env).toNat
      if d ≤ trial then trial-d else trial := by
  have numeric := WordCode.restoringStep_numeric divisor remainder bit next divisorBound remainderBound bitBound env
  rw [Code.restoringFlag_eval _ _ _ _ divisorBound remainderBound bitBound] at numeric
  dsimp
  split <;> rename_i enough
  · simp only [enough, trustIrWidthLemma decide_True decide_true, Bool.toNat_true, Nat.mul_one] at numeric
    omega
  · simp only [enough, trustIrWidthLemma decide_False decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at numeric
    exact numeric

theorem DivisionCode.step_value {width : Nat} (divisor : Fin width → Nat) (bit next : Nat)
    (prior : DivisionCode width) (checked : prior.check next = true)
    (divisorBound : ∀ i, divisor i < next) (bitBound : bit < next) (env : Assignment) :
    (DivisionCode.step divisor bit next prior).value env =
      divisionTransition width (wordValue divisor env).toNat (env bit) (prior.value env) := by
  obtain ⟨wordCheck, quotientBound⟩ := (DivisionCode.check_iff _ _).mp checked
  obtain ⟨valid, wordBounds⟩ := (WordCode.check_iff _ _).mp wordCheck
  let frontier := next+prior.remainder.gates.length
  let round := WordCode.divisionRound divisor prior.remainder.bits bit frontier
  let before := run prior.remainder.gates env
  have later : ∀ i, divisor i < frontier := by intro i; have bound := divisorBound i; dsimp [frontier]; omega
  have bitLater : bit < frontier := by dsimp [frontier]; omega
  have roundCheck := WordCode.divisionRound_check divisor prior.remainder.bits bit frontier later wordBounds bitLater
  have divisorSame : wordValue divisor before = wordValue divisor env := by
    apply wordValue_congr
    intro i; exact (valid.run_correct env).1 _ (divisorBound i)
  have bitSame : before bit = env bit := (valid.run_correct env).1 _ bitBound
  have quotientSame : wireNumber prior.quotient (run round.gates before) = wireNumber prior.quotient before := by
    apply wireNumber_congr
    intro id member
    exact ((((WordCode.check_iff _ _).mp roundCheck).1).run_correct before).1 _ (quotientBound id member)
  have flagValue := WordCode.divisionRound_flag divisor prior.remainder.bits bit frontier later wordBounds bitLater before
  rw [Code.restoringFlag_eval _ _ _ _ later wordBounds bitLater, divisorSame, bitSame] at flagValue
  have remValue := WordCode.divisionRound_numeric divisor prior.remainder.bits bit frontier later wordBounds bitLater before
  rw [WordCode.restoringStep_toNat _ _ _ _ later wordBounds bitLater, divisorSame, bitSame] at remValue
  apply Prod.ext
  · change wireNumber (_ :: prior.quotient) (run (prior.remainder.gates ++ round.gates) env) = _
    rw [run_append]
    change (run round.gates before _).toNat + 2*wireNumber prior.quotient (run round.gates before) = _
    rw [quotientSame, flagValue]
    change _ = 2*wireNumber prior.quotient before +
      (decide ((wordValue divisor env).toNat ≤ 2*(wordValue prior.remainder.bits before).toNat+(env bit).toNat)).toNat
    exact Nat.add_comm _ _
  · change (wordValue round.bits (run (prior.remainder.gates ++ round.gates) env)).toNat = _
    rw [run_append]
    exact remValue

theorem DivisionCode.rows_value {width : Nat} (divisor : Fin width → Nat) (source : List Nat) (next : Nat)
    (initial : DivisionCode width) (checked : initial.check next = true)
    (divisorBound : ∀ i, divisor i < next) (sourceBound : ∀ bit ∈ source, bit < next) (env : Assignment) :
    (DivisionCode.rows divisor source next initial).value env =
      source.foldl (fun prior bit => divisionTransition width (wordValue divisor env).toNat (env bit) prior)
        (initial.value env) := by
  induction source generalizing initial with
  | nil => rfl
  | cons bit rest ih =>
    change (DivisionCode.rows divisor rest next (DivisionCode.step divisor bit next initial)).value env = _
    rw [ih _ (DivisionCode.step_check _ _ _ _ checked divisorBound (sourceBound _ (List.Mem.head _)))
      (fun id member => sourceBound id (List.Mem.tail _ member)),
      DivisionCode.step_value _ _ _ _ checked divisorBound (sourceBound _ (List.Mem.head _))]
    rfl

theorem divisionTransition_div_mod (width d dividendPrefix : Nat) (bit : Bool)
    (positive : 0 < d) (fits : d < 2^width) :
    divisionTransition width d bit (dividendPrefix/d, dividendPrefix%d) =
      ((2*dividendPrefix+bit.toNat)/d, (2*dividendPrefix+bit.toNat)%d) := by
  let trial := 2*(dividendPrefix%d)+bit.toNat
  let take := (decide (d ≤ trial)).toNat
  let rem := if d ≤ trial then trial-d else trial
  have small := Nat.mod_lt dividendPrefix positive
  have bitSize : bit.toNat ≤ 1 := by cases bit <;> decide
  have conservation : rem+d*take=trial := by
    dsimp [rem, take]
    by_cases enough : d ≤ trial <;> simp [enough] <;> omega
  have bound : rem < d := by
    dsimp [rem]
    split <;> dsimp [trial] at * <;> omega
  have noTruncation : rem % 2^width = rem := Nat.mod_eq_of_lt (by omega)
  let q := 2*(dividendPrefix/d)+take
  let n := 2*dividendPrefix+bit.toNat
  have original := Nat.mod_add_div dividendPrefix d
  have conserved : n=d*q+rem := by
    dsimp [n, q]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm _ 2]
    dsimp [trial] at conservation
    omega
  have divValue : n/d=q := by
    apply Nat.div_eq_of_lt_le
    · rw [conserved, Nat.mul_comm q d]; omega
    · rw [conserved, Nat.succ_mul, Nat.mul_comm q d]; omega
  have modValue : n%d=rem := by
    have identity := Nat.mod_add_div n d
    rw [divValue] at identity
    omega
  change (q, rem % 2^width) = (n/d,n%d)
  rw [noTruncation, divValue, modValue]

theorem divisionRows_div_mod (width d : Nat) (source : List Nat) (env : Assignment) (dividendPrefix : Nat)
    (positive : 0 < d) (fits : d < 2^width) :
    source.foldl (fun prior bit => divisionTransition width d (env bit) prior)
        (dividendPrefix/d, dividendPrefix%d) =
      let consumed := source.foldl (fun n bit => 2*n+(env bit).toNat) dividendPrefix
      (consumed/d,consumed%d) := by
  induction source generalizing dividendPrefix with
  | nil => rfl
  | cons bit rest ih =>
    simp only [List.foldl]
    rw [divisionTransition_div_mod width d dividendPrefix (env bit) positive fits]
    exact ih _

private theorem division_mem_reverseAux (id : Nat) (a b : List Nat) :
    id ∈ a.reverseAux b ↔ id ∈ a ∨ id ∈ b := by
  induction a generalizing b with
  | nil => simp [List.reverseAux]
  | cons head tail ih => simp [List.reverseAux, ih, List.mem_cons, or_assoc, or_left_comm]

theorem division_source_bound {width : Nat} (source : Fin width → Nat) (next : Nat)
    (bound : ∀ i, source i < next) : ∀ id ∈ (tabulate source).reverse, id < next := by
  intro id member
  have original : id ∈ tabulate source := by
    simpa only [List.reverse, division_mem_reverseAux, List.not_mem_nil, or_false] using member
  obtain ⟨i, same⟩ := tabulate_cases source id original
  rw [← same]
  exact bound i

theorem division_consume_reverse (source : List Nat) (env : Assignment) :
    source.reverse.foldl (fun n bit => 2*n+(env bit).toNat) 0 = wireNumber source env := by
  rw [List.foldl_reverse]
  induction source with
  | nil => rfl
  | cons bit rest ih =>
    change 2*rest.foldr (fun bit n => 2*n+(env bit).toNat) 0+(env bit).toNat =
      (env bit).toNat+2*wireNumber rest env
    rw [ih]
    exact Nat.add_comm _ _

def DivisionCode.unsigned {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat) : DivisionCode width :=
  DivisionCode.rows divisor (tabulate dividend).reverse next
    ⟨WordCode.constant (BitVec.ofNat width 0) next, []⟩

theorem DivisionCode.unsigned_check {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next) :
    (DivisionCode.unsigned dividend divisor next).check next = true := by
  apply DivisionCode.rows_check
  · exact (DivisionCode.check_iff _ _).mpr ⟨WordCode.constant_check _ _, by simp⟩
  · exact divisorBound
  · exact division_source_bound _ _ dividendBound

theorem DivisionCode.unsigned_value_nonzero {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next)
    (env : Assignment) (positive : 0 < (wordValue divisor env).toNat) :
    (DivisionCode.unsigned dividend divisor next).value env =
      ((wordValue dividend env).toNat / (wordValue divisor env).toNat,
       (wordValue dividend env).toNat % (wordValue divisor env).toNat) := by
  have initialCheck : (⟨WordCode.constant (BitVec.ofNat width 0) next, []⟩ : DivisionCode width).check next = true :=
    (DivisionCode.check_iff _ _).mpr ⟨WordCode.constant_check _ _, by simp⟩
  have initialValue : (⟨WordCode.constant (BitVec.ofNat width 0) next, []⟩ : DivisionCode width).value env = (0,0) := by
    simp [DivisionCode.value, wireNumber, WordCode.constant_value]
  rw [DivisionCode.unsigned, DivisionCode.rows_value _ _ _ _ initialCheck divisorBound
    (division_source_bound _ _ dividendBound), initialValue]
  have zero : (0 / (wordValue divisor env).toNat, 0 % (wordValue divisor env).toNat) = (0,0) := by simp
  rw [← zero, divisionRows_div_mod _ _ _ _ _ positive (wordValue divisor env).isLt,
    division_consume_reverse, ← wordValue_toNat]

theorem division_consume_ge (source : List Nat) (env : Assignment) (initial : Nat) :
    initial ≤ source.foldl (fun n bit => 2*n+(env bit).toNat) initial := by
  induction source generalizing initial with
  | nil => exact Nat.le_refl _
  | cons bit rest ih =>
    have later := ih (2*initial+(env bit).toNat)
    exact Nat.le_trans (by omega) later

theorem divisionRows_zero (width : Nat) (source : List Nat) (env : Assignment) (q r : Nat)
    (fits : source.foldl (fun n bit => 2*n+(env bit).toNat) r < 2^width) :
    source.foldl (fun prior bit => divisionTransition width 0 (env bit) prior) (q,r) =
      ((q+1)*2^source.length-1, source.foldl (fun n bit => 2*n+(env bit).toNat) r) := by
  induction source generalizing q r with
  | nil => simp
  | cons bit rest ih =>
    have later := division_consume_ge rest env (2*r+(env bit).toNat)
    have trialFits : 2*r+(env bit).toNat < 2^width := by
      change rest.foldl _ (2*r+(env bit).toNat) < _ at fits
      omega
    have one : divisionTransition width 0 (env bit) (q,r) = (2*q+1,2*r+(env bit).toNat) := by
      simp [divisionTransition, Nat.mod_eq_of_lt trialFits]
    change rest.foldl (fun prior bit => divisionTransition width 0 (env bit) prior)
      (divisionTransition width 0 (env bit) (q,r)) = _
    rw [one, ih _ _ fits]
    apply Prod.ext
    · change (2*q+1+1)*2^rest.length-1 = (q+1)*2^(rest.length+1)-1
      rw [show 2*q+1+1 = (q+1)*2 by omega, Nat.pow_succ, Nat.mul_assoc,
        Nat.mul_comm 2 (2^rest.length)]
    · rfl

theorem DivisionCode.unsigned_value_zero {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next)
    (env : Assignment) (zero : (wordValue divisor env).toNat = 0) :
    (DivisionCode.unsigned dividend divisor next).value env =
      (2^width-1, (wordValue dividend env).toNat) := by
  have initialCheck : (⟨WordCode.constant (BitVec.ofNat width 0) next, []⟩ : DivisionCode width).check next = true :=
    (DivisionCode.check_iff _ _).mpr ⟨WordCode.constant_check _ _, by simp⟩
  have initialValue : (⟨WordCode.constant (BitVec.ofNat width 0) next, []⟩ : DivisionCode width).value env = (0,0) := by
    simp [DivisionCode.value, wireNumber, WordCode.constant_value]
  have fits : (tabulate dividend).reverse.foldl (fun n bit => 2*n+(env bit).toNat) 0 < 2^width := by
    rw [division_consume_reverse, ← wordValue_toNat]
    exact (wordValue dividend env).isLt
  rw [DivisionCode.unsigned, DivisionCode.rows_value _ _ _ _ initialCheck divisorBound
    (division_source_bound _ _ dividendBound), initialValue, zero, divisionRows_zero _ _ _ _ _ fits,
    division_consume_reverse, ← wordValue_toNat]
  simp [tabulate_length]

theorem DivisionCode.rows_quotient_length {width : Nat} (divisor : Fin width → Nat) (source : List Nat)
    (next : Nat) (initial : DivisionCode width) :
    (DivisionCode.rows divisor source next initial).quotient.length = initial.quotient.length+source.length := by
  induction source generalizing initial with
  | nil => simp [DivisionCode.rows]
  | cons bit rest ih =>
    change (DivisionCode.rows divisor rest next (DivisionCode.step divisor bit next initial)).quotient.length = _
    rw [ih]
    simp [DivisionCode.step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem DivisionCode.rows_gate_count {width : Nat} (divisor : Fin width → Nat) (source : List Nat)
    (next : Nat) (initial : DivisionCode width) :
    (DivisionCode.rows divisor source next initial).remainder.gates.length =
      initial.remainder.gates.length+source.length*(6*width+10) := by
  induction source generalizing initial with
  | nil => simp [DivisionCode.rows]
  | cons bit rest ih =>
    change (DivisionCode.rows divisor rest next (DivisionCode.step divisor bit next initial)).remainder.gates.length = _
    rw [ih]
    simp [DivisionCode.step, WordCode.append, List.length_append, WordCode.divisionRound_length,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem DivisionCode.unsigned_quotient_length {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat) :
    (DivisionCode.unsigned dividend divisor next).quotient.length = width := by
  simp [DivisionCode.unsigned, DivisionCode.rows_quotient_length, tabulate_length]

theorem DivisionCode.unsigned_gate_count {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat) :
    (DivisionCode.unsigned dividend divisor next).remainder.gates.length = width+width*(6*width+10) := by
  simp [DivisionCode.unsigned, DivisionCode.rows_gate_count, WordCode.constant, tabulate_length]

theorem DivisionCode.unsigned_value {width : Nat} (dividend divisor : Fin width → Nat) (next : Nat)
    (dividendBound : ∀ i, dividend i < next) (divisorBound : ∀ i, divisor i < next) (env : Assignment) :
    (DivisionCode.unsigned dividend divisor next).value env =
      if (wordValue divisor env).toNat = 0 then (2^width-1, (wordValue dividend env).toNat)
      else ((wordValue dividend env).toNat / (wordValue divisor env).toNat,
       (wordValue dividend env).toNat % (wordValue divisor env).toNat) := by
  split <;> rename_i h
  · exact DivisionCode.unsigned_value_zero _ _ _ dividendBound divisorBound env h
  · exact DivisionCode.unsigned_value_nonzero dividend divisor next dividendBound divisorBound env (Nat.pos_of_ne_zero h)

/-- Execute only a closed, admitted graph; both outputs use one buffered run. -/
def DivisionCode.checkedEval {width : Nat} (code : DivisionCode width) (next : Nat) (env : Assignment) :
    Option (Nat × Nat) :=
  if code.check next then
    let after := runBuffered next code.remainder.gates env
    some (wireNumber code.quotient after, (wordValue code.remainder.bits after).toNat)
  else none

theorem DivisionCode.checkedEval_eq_some {width : Nat} (code : DivisionCode width) (next : Nat)
    (env : Assignment) (result : Nat × Nat) :
    code.checkedEval next env = some result ↔ code.check next = true ∧ code.value env = result := by
  by_cases checked : code.check next = true
  · have wordCheck := ((DivisionCode.check_iff _ _).mp checked).1
    have program := (checkProgram_iff next code.remainder.gates).mpr ((WordCode.check_iff _ _).mp wordCheck).1
    simp [DivisionCode.checkedEval, checked, runBuffered_eq_run _ _ program,
      DivisionCode.value, WordCode.value]
  · simp [DivisionCode.checkedEval, checked]

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.check_iff == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.divisionRound_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.divisionRound_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.divisionRound_numeric == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.divisionRound_flag == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.step_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.rows_check == [propext, Classical.choice, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.wireNumber_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.wireNumber_congr

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.restoringStep_toNat == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.step_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.rows_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.divisionTransition_div_mod == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.divisionRows_div_mod == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.division_source_bound == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.division_consume_reverse == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.unsigned_check == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.unsigned_value_nonzero == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.division_consume_ge == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.divisionRows_zero == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.unsigned_value_zero == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.DivisionCode.rows_quotient_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.DivisionCode.rows_gate_count == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.DivisionCode.unsigned_quotient_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.DivisionCode.unsigned_gate_count == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.unsigned_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.DivisionCode.checkedEval_eq_some == [propext, Classical.choice, Quot.sound]
