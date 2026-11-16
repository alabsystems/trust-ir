-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordPermutation
import TrustIr.Proofs.AYTypedRequest

/-- Select the standard list concatenation operation on each compiler. -/
macro "trustIrPermutationFlatten" : term => do
  if Lean.versionString == "4.8.0" then `(List.join)
  else if Lean.versionString == "4.30.0-rc2" then `(List.flatten)
  else Lean.Macro.throwError "unsupported compiler for permutation bindings"

namespace TrustIr.TrustIrExpr

def SMTTerm.castWidth {a b : Nat} (same : a = b) (term : SMTTerm (.bv a)) : SMTTerm (.bv b) :=
  same ▸ term

theorem SMTTerm.castWidth_eval {a b : Nat} (same : a = b) (term : SMTTerm (.bv a)) (env : SMTEnv) :
    (term.castWidth same).eval env = (term.eval env).cast same := by cases same; rfl

theorem SMTTerm.castWidth_wellFormed {a b : Nat} (same : a = b) (term : SMTTerm (.bv a)) :
    (term.castWidth same).WellFormed = term.WellFormed := by cases same; rfl

theorem SMTTerm.castWidth_bindings {a b : Nat} (same : a = b) (term : SMTTerm (.bv a)) :
    (term.castWidth same).bindings = term.bindings := by cases same; rfl


theorem SMTTerm.castWidth_boolBindings {a b : Nat} (same : a = b) (term : SMTTerm (.bv a)) :
    (term.castWidth same).boolBindings = term.boolBindings := by cases same; rfl

/-- One legal extract of the ORIGINAL source. The chunk is not extracted from
a growing nest of prior extracts. -/
def SMTTerm.chunk {source : Nat} (word : SMTTerm (.bv source)) (size : Nat)
    (positive : 0 < size) (index : Nat) (bound : (index+1)*size ≤ source) : SMTTerm (.bv size) :=
  let hi := (index+1)*size-1
  let lo := index*size
  have step : (index+1)*size = index*size+size := Nat.succ_mul index size
  have endPositive : 0 < (index+1)*size := Nat.mul_pos (by omega) positive
  let part := SMTTerm.unary (.bvExtract source hi lo
    (by dsimp [hi, lo]; rw [Nat.succ_mul]; omega)
    (by dsimp [hi]; omega)) word
  part.castWidth (by dsimp [hi, lo]; rw [Nat.succ_mul]; omega)

theorem SMTTerm.chunk_toNat {source : Nat} (word : SMTTerm (.bv source)) (size : Nat)
    (positive : 0 < size) (index : Nat) (bound : (index+1)*size ≤ source) (env : SMTEnv) :
    ((word.chunk size positive index bound).eval env).toNat =
      (word.eval env).toNat / 2^(index*size) % 2^size := by
  unfold SMTTerm.chunk
  rw [SMTTerm.castWidth_eval, BitVec.toNat_cast]
  simp only [SMTTerm.eval, SMTUnary.eval, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  have step : (index+1)*size = index*size+size := Nat.succ_mul index size
  congr 2
  omega

/-- Build the same increasing-extract, left-associated-concat tree as the
Rust AY encoder. The zero case is uninhabited, with no fabricated bv0 term.
The source and output sizes bound every extract before it is constructed. -/
def SMTTerm.reverseChunks {source : Nat} (word : SMTTerm (.bv source)) (size : Nat)
    (chunkPositive : 0 < size) : (count : Nat) → 0 < count → count*size ≤ source → SMTTerm (.bv (count*size)) :=
  Nat.rec (motive := fun count => 0 < count → count*size ≤ source → SMTTerm (.bv (count*size)))
    (fun positive _ => False.elim (Nat.not_lt_zero _ positive))
    (fun count previous _ bound =>
      let lane := word.chunk size chunkPositive count bound
      if empty : count = 0 then
        lane.castWidth (by simp [empty])
      else
        let earlier := previous (by omega) (by rw [Nat.succ_mul] at bound; omega)
        (SMTTerm.concat earlier lane).castWidth (Nat.succ_mul count size).symm)

def reverseDigits (radix value count : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun n previous v => (v % radix) * radix^n + previous (v/radix)) count value

@[simp] theorem reverseDigits_zero (radix value : Nat) : reverseDigits radix value 0 = 0 := rfl
@[simp] theorem reverseDigits_succ (radix value count : Nat) :
    reverseDigits radix value (count+1) =
      (value % radix) * radix^count + reverseDigits radix (value/radix) count := rfl

theorem reverseDigits_append (radix value count : Nat) :
    reverseDigits radix value (count+1) =
      reverseDigits radix value count * radix + (value / radix^count) % radix := by
  induction count generalizing value with
  | zero => simp
  | succ count ih =>
    rw [reverseDigits_succ, ih (value/radix), reverseDigits_succ radix value count]
    simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm radix (radix^count)]
    omega

theorem SMTTerm.reverseChunks_step {source : Nat} (word : SMTTerm (.bv source))
    (size : Nat) (chunkPositive : 0 < size) (count : Nat) (positive : 0 < count+1)
    (bound : (count+1)*size ≤ source) :
    word.reverseChunks size chunkPositive (count+1) positive bound =
      if empty : count = 0 then
        (word.chunk size chunkPositive count bound).castWidth (by simp [empty])
      else
        (SMTTerm.concat
          (word.reverseChunks size chunkPositive count (by omega) (by rw [Nat.succ_mul] at bound; omega))
          (word.chunk size chunkPositive count bound)).castWidth (Nat.succ_mul count size).symm := rfl

private theorem permutation_concat_toNat {high low : Nat} (a : BitVec high) (b : BitVec low) :
    (a ++ b).toNat = a.toNat*2^low+b.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq]
  simpa only [Nat.mul_comm] using ((trustIrWidthLemma Nat.mul_add_lt_is_or Nat.two_pow_add_eq_or_of_lt) b.isLt a.toNat).symm

theorem SMTTerm.reverseChunks_toNat {source : Nat} (word : SMTTerm (.bv source))
    (size : Nat) (chunkPositive : 0 < size) (count : Nat) (positive : 0 < count)
    (bound : count*size ≤ source) (env : SMTEnv) :
    ((word.reverseChunks size chunkPositive count positive bound).eval env).toNat =
      reverseDigits (2^size) (word.eval env).toNat count := by
  induction count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ count ih =>
    rw [SMTTerm.reverseChunks_step]
    by_cases empty : count = 0
    · subst count
      rw [dif_pos rfl, SMTTerm.castWidth_eval, BitVec.toNat_cast, SMTTerm.chunk_toNat]
      simp [reverseDigits_succ]
    · rw [dif_neg empty, SMTTerm.castWidth_eval, BitVec.toNat_cast]
      change (((word.reverseChunks size chunkPositive count (by omega)
        (by rw [Nat.succ_mul] at bound; omega)).eval env ++
        (word.chunk size chunkPositive count bound).eval env).toNat) = _
      rw [permutation_concat_toNat, ih (by omega), SMTTerm.chunk_toNat, reverseDigits_append]
      have power : 2^(count*size) = (2^size)^count := by rw [Nat.mul_comm, Nat.pow_mul]
      rw [power]

theorem reverseDigits_two (value count : Nat) :
    reverseDigits 2 value count = bitReverseWidth value count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => rw [reverseDigits_succ, bitReverseWidth, ih]

theorem reverseDigits_bytes (value count : Nat) :
    reverseDigits 256 value count = bswapBytes value count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => rw [reverseDigits_succ, bswapBytes, ih]

theorem SMTTerm.chunk_wellFormed {source : Nat} (word : SMTTerm (.bv source)) (size : Nat)
    (positive : 0 < size) (index : Nat) (bound : (index+1)*size ≤ source)
    (wellFormed : word.WellFormed) : (word.chunk size positive index bound).WellFormed := by
  unfold SMTTerm.chunk
  rw [SMTTerm.castWidth_wellFormed]
  exact wellFormed

theorem SMTTerm.chunk_bindings {source : Nat} (word : SMTTerm (.bv source)) (size : Nat)
    (positive : 0 < size) (index : Nat) (bound : (index+1)*size ≤ source) :
    (word.chunk size positive index bound).bindings = word.bindings := by
  unfold SMTTerm.chunk
  rw [SMTTerm.castWidth_bindings]
  rfl


theorem SMTTerm.chunk_boolBindings {source : Nat} (word : SMTTerm (.bv source)) (size : Nat)
    (positive : 0 < size) (index : Nat) (bound : (index+1)*size ≤ source) :
    (word.chunk size positive index bound).boolBindings = word.boolBindings := by
  unfold SMTTerm.chunk
  rw [SMTTerm.castWidth_boolBindings]
  rfl

theorem SMTTerm.reverseChunks_wellFormed {source : Nat} (word : SMTTerm (.bv source))
    (size : Nat) (chunkPositive : 0 < size) (count : Nat) (positive : 0 < count)
    (bound : count*size ≤ source) (wellFormed : word.WellFormed) :
    (word.reverseChunks size chunkPositive count positive bound).WellFormed := by
  induction count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ count ih =>
    rw [SMTTerm.reverseChunks_step]
    split
    · rw [SMTTerm.castWidth_wellFormed]
      exact SMTTerm.chunk_wellFormed _ _ _ _ _ wellFormed
    · rw [SMTTerm.castWidth_wellFormed]
      exact ⟨ih _ _, SMTTerm.chunk_wellFormed _ _ _ _ _ wellFormed⟩

/-- Linear construction of the actual repeated inventory; do not repeatedly
copy the growing prefix as the left-associated SMT syntax is constructed. -/
def permutationBindings {α : Type} (count : Nat) (bindings : List α) : List α :=
  trustIrPermutationFlatten (List.replicate count bindings)

theorem permutationBindings_snoc {α : Type} (count : Nat) (bindings : List α) :
    permutationBindings (count+1) bindings = permutationBindings count bindings ++ bindings := by
  induction count with
  | zero => simp [permutationBindings]
  | succ count ih =>
    change bindings ++ permutationBindings (count+1) bindings =
      (bindings ++ permutationBindings count bindings) ++ bindings
    rw [ih, List.append_assoc]

theorem SMTTerm.reverseChunks_bindings {source : Nat} (word : SMTTerm (.bv source))
    (size : Nat) (chunkPositive : 0 < size) (count : Nat) (positive : 0 < count)
    (bound : count*size ≤ source) :
    (word.reverseChunks size chunkPositive count positive bound).bindings =
      permutationBindings count word.bindings := by
  induction count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ count ih =>
    rw [SMTTerm.reverseChunks_step]
    by_cases empty : count = 0
    · subst count
      rw [dif_pos rfl, SMTTerm.castWidth_bindings, SMTTerm.chunk_bindings]
      simp [permutationBindings]
    · rw [dif_neg empty, SMTTerm.castWidth_bindings]
      change (word.reverseChunks size chunkPositive count (by omega)
        (by rw [Nat.succ_mul] at bound; omega)).bindings ++
        (word.chunk size chunkPositive count bound).bindings = _
      rw [ih, SMTTerm.chunk_bindings, permutationBindings_snoc]


theorem SMTTerm.reverseChunks_boolBindings {source : Nat} (word : SMTTerm (.bv source))
    (size : Nat) (chunkPositive : 0 < size) (count : Nat) (positive : 0 < count)
    (bound : count*size ≤ source) :
    (word.reverseChunks size chunkPositive count positive bound).boolBindings =
      permutationBindings count word.boolBindings := by
  induction count with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ count ih =>
    rw [SMTTerm.reverseChunks_step]
    by_cases empty : count = 0
    · subst count
      rw [dif_pos rfl, SMTTerm.castWidth_boolBindings, SMTTerm.chunk_boolBindings]
      simp [permutationBindings]
    · rw [dif_neg empty, SMTTerm.castWidth_boolBindings]
      change (word.reverseChunks size chunkPositive count (by omega)
        (by rw [Nat.succ_mul] at bound; omega)).boolBindings ++
        (word.chunk size chunkPositive count bound).boolBindings = _
      rw [ih, SMTTerm.chunk_boolBindings, permutationBindings_snoc]

def SMTCheckedTerm.reverseChunks {source : Nat} (word : SMTCheckedTerm (.bv source))
    (size : Nat) (chunkPositive : 0 < size) (count : Nat) (positive : 0 < count)
    (bound : count*size ≤ source) : SMTCheckedTerm (.bv (count*size)) :=
  ⟨word.term.reverseChunks size chunkPositive count positive bound,
    permutationBindings count word.bindings,
    word.term.reverseChunks_wellFormed size chunkPositive count positive bound word.wellFormed,
    by rw [word.term.reverseChunks_bindings, word.inventory],
    permutationBindings count word.boolBindings,
    by rw [word.term.reverseChunks_boolBindings, word.boolInventory]⟩

def SMTCheckedTerm.castWidth {a b : Nat} (same : a = b) (term : SMTCheckedTerm (.bv a)) :
    SMTCheckedTerm (.bv b) := same ▸ term

theorem SMTCheckedTerm.castWidth_term {a b : Nat} (same : a = b) (term : SMTCheckedTerm (.bv a)) :
    (term.castWidth same).term = term.term.castWidth same := by cases same; rfl

def SMTCheckedTerm.bitReverse {width : Nat} (word : SMTCheckedTerm (.bv width)) :
    Except String (SMTCheckedTerm (.bv width)) :=
  if positive : 0 < width then
    .ok ((word.reverseChunks 1 (by decide) width positive (by simp)).castWidth (by simp))
  else .error "bitreverse at width 0"

def SMTCheckedTerm.byteSwap {width : Nat} (word : SMTCheckedTerm (.bv width)) :
    Except String (SMTCheckedTerm (.bv width)) :=
  if positive : 0 < width then
    if bytes : width % 8 = 0 then
      have size : (width/8)*8 = width := by omega
      .ok ((word.reverseChunks 8 (by decide) (width/8) (by omega) (by omega)).castWidth size)
    else .error "bswap requires a whole number of bytes"
  else .error "bswap at width 0"

theorem SMTCheckedTerm.bitReverse_toNat {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.bitReverse = .ok result) (env : SMTEnv) :
    (result.term.eval env).toNat = bitReverseWidth (word.term.eval env).toNat width := by
  unfold SMTCheckedTerm.bitReverse at built
  split at built
  · cases built
    rw [SMTCheckedTerm.castWidth_term, SMTTerm.castWidth_eval, BitVec.toNat_cast]
    change ((word.term.reverseChunks 1 (by decide) width _ _).eval env).toNat = _
    rw [SMTTerm.reverseChunks_toNat]
    exact reverseDigits_two _ _
  · contradiction

theorem SMTCheckedTerm.byteSwap_toNat {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.byteSwap = .ok result) (env : SMTEnv) :
    (result.term.eval env).toNat = bswapWidth (word.term.eval env).toNat width := by
  unfold SMTCheckedTerm.byteSwap at built
  split at built
  · split at built
    · cases built
      rw [SMTCheckedTerm.castWidth_term, SMTTerm.castWidth_eval, BitVec.toNat_cast]
      change ((word.term.reverseChunks 8 (by decide) (width/8) _ _).eval env).toNat = _
      rw [SMTTerm.reverseChunks_toNat]
      exact reverseDigits_bytes _ _
    · contradiction
  · contradiction

/-- Request construction preserves the exact actual target, including its
checked inventory and lexical source namespace. No solver result is assumed. -/
theorem SMTCheckedTerm.bitReverse_request {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.bitReverse = .ok result) (request : SMTTypedRequest (.bv width))
    (requested : result.toTypedRequest = .ok request) (env : SMTEnv) :
    request.target = result.term ∧ request.target.WellFormed ∧
    (request.target.eval env).toNat = bitReverseWidth (word.term.eval env).toNat width := by
  have actual := result.toTypedRequest_admitted request requested
  exact ⟨actual.1, actual.2.1, by rw [actual.1]; exact word.bitReverse_toNat result built env⟩

theorem SMTCheckedTerm.byteSwap_request {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.byteSwap = .ok result) (request : SMTTypedRequest (.bv width))
    (requested : result.toTypedRequest = .ok request) (env : SMTEnv) :
    request.target = result.term ∧ request.target.WellFormed ∧
    (request.target.eval env).toNat = bswapWidth (word.term.eval env).toNat width := by
  have actual := result.toTypedRequest_admitted request requested
  exact ⟨actual.1, actual.2.1, by rw [actual.1]; exact word.byteSwap_toNat result built env⟩

end TrustIr.TrustIrExpr

namespace TrustIr.AYGateCNF
open TrustIrExpr

theorem WordCode.bitReverse_target {width : Nat} (input : Fin width → Nat) (env : Assignment)
    (word result : SMTCheckedTerm (.bv width)) (built : word.bitReverse = .ok result)
    (target : SMTEnv) (source : wordValue input env = word.term.eval target) :
    (WordCode.bitReverse input).value env = result.term.eval target := by
  apply BitVec.eq_of_toNat_eq
  rw [WordCode.bitReverse_value, source, word.bitReverse_toNat result built target]

theorem WordCode.byteSwap_target (bytes : List (Fin 8 → Nat)) (env : Assignment)
    (word result : SMTCheckedTerm (.bv (bytes.length*8))) (built : word.byteSwap = .ok result)
    (target : SMTEnv)
    (source : ((WordCode.ofWireList (byteWireList bytes)).value env).toNat = (word.term.eval target).toNat) :
    (WordCode.byteSwap bytes).value env = result.term.eval target := by
  apply BitVec.eq_of_toNat_eq
  rw [WordCode.byteSwap_value, source, word.byteSwap_toNat result built target]

theorem WordCode.bitReverse_checkedTarget {width : Nat} (input : Fin width → Nat)
    (next : Nat) (env : Assignment) (value : BitVec width)
    (executed : (WordCode.bitReverse input).checkedEval next env = some value)
    (word result : SMTCheckedTerm (.bv width)) (built : word.bitReverse = .ok result)
    (target : SMTEnv) (source : wordValue input env = word.term.eval target) :
    value = result.term.eval target := by
  have actual := ((WordCode.bitReverse input).checkedEval_eq_some next env value).mp executed
  exact actual.2.symm.trans (WordCode.bitReverse_target input env word result built target source)

theorem WordCode.byteSwap_checkedTarget (bytes : List (Fin 8 → Nat))
    (next : Nat) (env : Assignment) (value : BitVec (bytes.length*8))
    (executed : (WordCode.byteSwap bytes).checkedEval next env = some value)
    (word result : SMTCheckedTerm (.bv (bytes.length*8))) (built : word.byteSwap = .ok result)
    (target : SMTEnv)
    (source : ((WordCode.ofWireList (byteWireList bytes)).value env).toNat = (word.term.eval target).toNat) :
    value = result.term.eval target := by
  have actual := ((WordCode.byteSwap bytes).checkedEval_eq_some next env value).mp executed
  exact actual.2.symm.trans (WordCode.byteSwap_target bytes env word result built target source)

/-- A child keeps its original gate prefix; reversal only rewires its output. -/
def WordCode.composeBitReverse {width : Nat} (child : WordCode width) : WordCode width :=
  WordCode.append child (WordCode.bitReverse child.bits)

theorem WordCode.composeBitReverse_check {width : Nat} (child : WordCode width) (next : Nat)
    (checked : child.check next = true) : (WordCode.composeBitReverse child).check next = true := by
  apply WordCode.append_check _ _ _ checked
  exact WordCode.bitReverse_check _ _ ((WordCode.check_iff _ _).mp checked).2

theorem WordCode.composeBitReverse_gates {width : Nat} (child : WordCode width) :
    (WordCode.composeBitReverse child).gates = child.gates := by
  simp [WordCode.composeBitReverse, WordCode.append, WordCode.bitReverse, WordCode.rewire]

theorem WordCode.composeBitReverse_target {width : Nat} (child : WordCode width) (env : Assignment)
    (word result : SMTCheckedTerm (.bv width)) (built : word.bitReverse = .ok result)
    (target : SMTEnv) (source : child.value env = word.term.eval target) :
    (WordCode.composeBitReverse child).value env = result.term.eval target := by
  rw [WordCode.composeBitReverse, WordCode.append_value]
  exact WordCode.bitReverse_target _ _ word result built target source

end TrustIr.AYGateCNF
