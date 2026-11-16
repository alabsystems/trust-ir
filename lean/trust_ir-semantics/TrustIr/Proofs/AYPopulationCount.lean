-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYPermutationTarget

namespace TrustIr.TrustIrExpr

/-- Exact subtotal width used by the Rust AY popcount interval encoder. -/
def populationBits (length : Nat) : Nat := length.log2+1

theorem populationBits_positive (length : Nat) : 0 < populationBits length := by
  unfold populationBits
  omega

theorem populationBits_capacity (length : Nat) : length < 2^(populationBits length) :=
  Nat.lt_log2_self

theorem populationBits_mono (small large : Nat) (positive : 0 < small) (bound : small ≤ large) :
    populationBits small ≤ populationBits large := by
  have low : 2^small.log2 ≤ large := Nat.le_trans (Nat.log2_self_le (by omega)) bound
  have logarithms := (Nat.le_log2 (show large ≠ 0 by omega)).mpr low
  unfold populationBits
  omega

private theorem population_lt_power (n : Nat) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have positive := Nat.two_pow_pos n
    omega

theorem populationBits_le (length : Nat) (positive : 0 < length) : populationBits length ≤ length := by
  have logarithm := (Nat.log2_lt (show length ≠ 0 by omega)).mpr (population_lt_power length)
  unfold populationBits
  omega

/-- A nonempty plan is intrinsically bisected. Its type prevents an empty
leaf, mismatched child extent, or a linear chain of singleton appends. -/
inductive PopulationPlan : Nat → Type where
  | bit : PopulationPlan 1
  | split {length : Nat} (large : 2 ≤ length)
      (left : PopulationPlan (length/2)) (right : PopulationPlan (length-length/2)) : PopulationPlan length

private theorem population_lower_positive (n : Nat) (large : 2 ≤ n) : 0 < n/2 := by omega
private theorem population_upper_positive (n : Nat) (large : 2 ≤ n) : 0 < n-n/2 := by omega
private theorem population_lower_lt (n : Nat) (large : 2 ≤ n) : n/2 < n := by omega
private theorem population_upper_lt (n : Nat) (large : 2 ≤ n) : n-n/2 < n := by omega

/-- No arbitrary fuel or width cap: recursion strictly decreases the actual
interval length, and has exactly the Rust encoder's lower/upper halves. -/
def PopulationPlan.balanced (length : Nat) (positive : 0 < length) : PopulationPlan length :=
  if single : length = 1 then single ▸ PopulationPlan.bit
  else
    have large : 2 ≤ length := by omega
    .split large
      (PopulationPlan.balanced (length/2) (population_lower_positive length large))
      (PopulationPlan.balanced (length-length/2) (population_upper_positive length large))
termination_by length
decreasing_by
  · exact population_lower_lt length large
  · exact population_upper_lt length large

/-- Independent ordered sum of the ORIGINAL source bits in a finite slice. -/
def populationSlice (value start length : Nat) : Nat :=
  Nat.rec 0 (fun i subtotal => subtotal+(value/2^(start+i))%2) length

@[simp] theorem populationSlice_zero (value start : Nat) : populationSlice value start 0 = 0 := rfl
@[simp] theorem populationSlice_succ (value start length : Nat) :
    populationSlice value start (length+1) =
      populationSlice value start length + (value/2^(start+length))%2 := rfl

theorem populationSlice_bound (value start length : Nat) : populationSlice value start length ≤ length := by
  induction length with
  | zero => exact Nat.le_refl 0
  | succ length ih =>
    rw [populationSlice_succ]
    have bit := Nat.mod_lt (value/2^(start+length)) (by decide : 0 < 2)
    omega

theorem populationSlice_append (value start left right : Nat) :
    populationSlice value start (left+right) =
      populationSlice value start left + populationSlice value (start+left) right := by
  induction right with
  | zero => simp
  | succ right ih =>
    rw [Nat.add_succ, populationSlice_succ, ih, populationSlice_succ]
    simp [Nat.add_assoc]

private theorem population_range_loop_append (n : Nat) (left right : List Nat) :
    List.range.loop n (left++right) = List.range.loop n left ++ right := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simpa only [List.range.loop, List.cons_append] using ih (n::left)

private theorem population_range_snoc (n : Nat) : List.range (n+1) = List.range n ++ [n] :=
  population_range_loop_append n [] [n]

/-- Connect the slice sum to the existing instruction semantics, rather than
substituting an unrelated abstract population-count function. -/
theorem populationSlice_semantics (value width : Nat) :
    populationSlice value 0 width = popCountWidth value width := by
  unfold popCountWidth
  induction width with
  | zero => rfl
  | succ width ih =>
    rw [populationSlice_succ, population_range_snoc, List.foldl_append, ← ih]
    simp [List.foldl]

/-- Match the encoder's conditional extension: equal-width children are
retained verbatim, not wrapped in redundant zero_extend 0 nodes. -/
def SMTTerm.populationExtend {bits : Nat} (target : Nat) (word : SMTTerm (.bv bits))
    (wide : bits ≤ target) : SMTTerm (.bv target) :=
  if same : bits = target then word.castWidth same
  else (SMTTerm.unary (.bvZeroExtend bits (target-bits)) word).castWidth (by omega)

theorem SMTTerm.populationExtend_toNat {bits : Nat} (target : Nat) (word : SMTTerm (.bv bits))
    (wide : bits ≤ target) (env : SMTEnv) :
    ((word.populationExtend target wide).eval env).toNat = (word.eval env).toNat := by
  unfold SMTTerm.populationExtend
  split
  · rw [SMTTerm.castWidth_eval, BitVec.toNat_cast]
  · rw [SMTTerm.castWidth_eval, BitVec.toNat_cast]
    change ((word.eval env).zeroExtend (bits+(target-bits))).toNat = _
    rw [trustIrWidthLemma BitVec.toNat_zeroExtend BitVec.toNat_setWidth]
    have size : bits+(target-bits) = target := by omega
    rw [size]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (word.eval env).isLt ((trustIrWidthLemma Nat.pow_le_pow_of_le_right Nat.pow_le_pow_right) (by decide) wide)

theorem SMTTerm.populationExtend_wellFormed {bits : Nat} (target : Nat) (word : SMTTerm (.bv bits))
    (wide : bits ≤ target) (wellFormed : word.WellFormed) :
    (word.populationExtend target wide).WellFormed := by
  unfold SMTTerm.populationExtend
  split <;> rw [SMTTerm.castWidth_wellFormed] <;> exact wellFormed

theorem SMTTerm.populationExtend_bindings {bits : Nat} (target : Nat) (word : SMTTerm (.bv bits))
    (wide : bits ≤ target) : (word.populationExtend target wide).bindings = word.bindings := by
  unfold SMTTerm.populationExtend
  split <;> rw [SMTTerm.castWidth_bindings] <;> rfl


theorem SMTTerm.populationExtend_boolBindings {bits : Nat} (target : Nat) (word : SMTTerm (.bv bits))
    (wide : bits ≤ target) : (word.populationExtend target wide).boolBindings = word.boolBindings := by
  unfold SMTTerm.populationExtend
  split <;> rw [SMTTerm.castWidth_boolBindings] <;> rfl

/-- Interpret the intrinsic plan through original-source extracts and narrow
native additions. Recursion is on the plan itself, with no independent fuel. -/
def PopulationPlan.target {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (word : SMTTerm (.bv source)) (start : Nat) (bound : start+length ≤ source) :
    SMTTerm (.bv (populationBits length)) :=
  match plan with
  | .bit => (word.chunk 1 (by decide) start (by simpa using bound)).castWidth (by decide)
  | .split (length := length) large leftPlan rightPlan =>
    let left := leftPlan.target word start (by have h := Nat.div_le_self length 2; omega)
    let right := rightPlan.target word (start+length/2) (by have h := Nat.div_le_self length 2; omega)
    SMTTerm.binary (.bvAdd (populationBits length))
      (left.populationExtend (populationBits length)
        (populationBits_mono _ _ (population_lower_positive length large) (Nat.div_le_self _ _)))
      (right.populationExtend (populationBits length)
        (populationBits_mono _ _ (population_upper_positive length large) (Nat.sub_le _ _)))

theorem PopulationPlan.target_bit {source : Nat} (word : SMTTerm (.bv source)) (start : Nat)
    (bound : start+1 ≤ source) :
    PopulationPlan.bit.target word start bound =
      (word.chunk 1 (by decide) start (by simpa using bound)).castWidth (by decide) := rfl

theorem PopulationPlan.target_split {length source : Nat} (large : 2 ≤ length)
    (left : PopulationPlan (length/2)) (right : PopulationPlan (length-length/2))
    (word : SMTTerm (.bv source)) (start : Nat) (bound : start+length ≤ source) :
    (PopulationPlan.split large left right).target word start bound =
      SMTTerm.binary (.bvAdd (populationBits length))
        ((left.target word start (by have h := Nat.div_le_self length 2; omega)).populationExtend _
          (populationBits_mono _ _ (population_lower_positive length large) (Nat.div_le_self _ _)))
        ((right.target word (start+length/2) (by have h := Nat.div_le_self length 2; omega)).populationExtend _
          (populationBits_mono _ _ (population_upper_positive length large) (Nat.sub_le _ _))) := rfl

/-- The result is the exact unbounded count, not merely its residue. Child
counts add without overflow at the encoder's actual minimal subtotal width. -/
theorem PopulationPlan.target_toNat {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (word : SMTTerm (.bv source)) (start : Nat) (bound : start+length ≤ source) (env : SMTEnv) :
    ((plan.target word start bound).eval env).toNat = populationSlice (word.eval env).toNat start length := by
  induction plan generalizing start with
  | bit =>
    rw [PopulationPlan.target_bit, SMTTerm.castWidth_eval, BitVec.toNat_cast, SMTTerm.chunk_toNat]
    simp [populationSlice_succ]
  | @split length large left right leftIH rightIH =>
    rw [PopulationPlan.target_split]
    change ((_ + _ : BitVec (populationBits length)).toNat) = _
    rw [BitVec.toNat_add, SMTTerm.populationExtend_toNat, SMTTerm.populationExtend_toNat,
      leftIH, rightIH]
    have halves : length/2+(length-length/2) = length := by have h := Nat.div_le_self length 2; omega
    have sum := populationSlice_append (word.eval env).toNat start (length/2) (length-length/2)
    rw [halves] at sum
    rw [← sum]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (populationSlice_bound _ _ _) (populationBits_capacity length)

theorem PopulationPlan.target_wellFormed {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (word : SMTTerm (.bv source)) (start : Nat) (bound : start+length ≤ source)
    (wellFormed : word.WellFormed) : (plan.target word start bound).WellFormed := by
  induction plan generalizing start with
  | bit =>
    rw [PopulationPlan.target_bit, SMTTerm.castWidth_wellFormed]
    exact SMTTerm.chunk_wellFormed _ _ _ _ _ wellFormed
  | @split length large left right leftIH rightIH =>
    rw [PopulationPlan.target_split]
    exact ⟨SMTTerm.populationExtend_wellFormed _ _ _ (leftIH _ _),
      SMTTerm.populationExtend_wellFormed _ _ _ (rightIH _ _)⟩

theorem populationBindings_add {α : Type} (left right : Nat) (bindings : List α) :
    permutationBindings (left+right) bindings =
      permutationBindings left bindings ++ permutationBindings right bindings := by
  induction right with
  | zero => simp [permutationBindings]
  | succ right ih =>
    rw [Nat.add_succ, permutationBindings_snoc, ih, permutationBindings_snoc, List.append_assoc]

private theorem population_binary_inventory {input output : SMTSort} (op : SMTBinary input output)
    (left right : SMTTerm input) : (SMTTerm.binary op left right).bindings = left.bindings ++ right.bindings := rfl


theorem population_binary_bool_inventory {input output : SMTSort} (op : SMTBinary input output)
    (left right : SMTTerm input) : (SMTTerm.binary op left right).boolBindings = left.boolBindings ++ right.boolBindings := rfl

theorem PopulationPlan.target_bindings {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (word : SMTTerm (.bv source)) (start : Nat) (bound : start+length ≤ source) :
    (plan.target word start bound).bindings = permutationBindings length word.bindings := by
  induction plan generalizing start with
  | bit =>
    rw [PopulationPlan.target_bit, SMTTerm.castWidth_bindings, SMTTerm.chunk_bindings]
    simp [permutationBindings]
  | @split length large left right leftIH rightIH =>
    rw [PopulationPlan.target_split, population_binary_inventory,
      SMTTerm.populationExtend_bindings, SMTTerm.populationExtend_bindings, leftIH, rightIH,
      ← populationBindings_add]
    congr 1
    have bound := Nat.div_le_self length 2
    omega


theorem PopulationPlan.target_boolBindings {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (word : SMTTerm (.bv source)) (start : Nat) (bound : start+length ≤ source) :
    (plan.target word start bound).boolBindings = permutationBindings length word.boolBindings := by
  induction plan generalizing start with
  | bit =>
    rw [PopulationPlan.target_bit, SMTTerm.castWidth_boolBindings, SMTTerm.chunk_boolBindings]
    simp [permutationBindings]
  | @split length large left right leftIH rightIH =>
    rw [PopulationPlan.target_split, population_binary_bool_inventory,
      SMTTerm.populationExtend_boolBindings, SMTTerm.populationExtend_boolBindings, leftIH, rightIH,
      ← populationBindings_add]
    congr 1
    have bound := Nat.div_le_self length 2
    omega

/-- The counter's inventory is computed in one replication pass, not by
copying inventories at every internal node of the balanced expression. -/
def PopulationPlan.checkedTarget {length : Nat} (plan : PopulationPlan length) {source : Nat}
    (word : SMTCheckedTerm (.bv source)) (start : Nat) (bound : start+length ≤ source) :
    SMTCheckedTerm (.bv (populationBits length)) :=
  ⟨plan.target word.term start bound, permutationBindings length word.bindings,
    plan.target_wellFormed word.term start bound word.wellFormed,
    by rw [plan.target_bindings, word.inventory],
    permutationBindings length word.boolBindings,
    by rw [plan.target_boolBindings, word.boolInventory]⟩

def SMTCheckedTerm.populationExtend {bits : Nat} (target : Nat) (word : SMTCheckedTerm (.bv bits))
    (wide : bits ≤ target) : SMTCheckedTerm (.bv target) :=
  ⟨word.term.populationExtend target wide, word.bindings,
    word.term.populationExtend_wellFormed target wide word.wellFormed,
    by rw [word.term.populationExtend_bindings, word.inventory],
    word.boolBindings, by rw [word.term.populationExtend_boolBindings, word.boolInventory]⟩

def SMTCheckedTerm.popCount {width : Nat} (word : SMTCheckedTerm (.bv width)) :
    Except String (SMTCheckedTerm (.bv width)) :=
  if positive : 0 < width then
    let plan := PopulationPlan.balanced width positive
    let counted := plan.checkedTarget word 0 (by omega)
    .ok (counted.populationExtend width (populationBits_le width positive))
  else .error "ctpop of a zero-width bit-vector"

theorem SMTCheckedTerm.popCount_toNat {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.popCount = .ok result) (env : SMTEnv) :
    (result.term.eval env).toNat = popCountWidth (word.term.eval env).toNat width := by
  unfold SMTCheckedTerm.popCount at built
  split at built
  · rename_i positive
    cases built
    change ((((PopulationPlan.balanced width positive).target word.term 0 (by omega)).populationExtend width
      (populationBits_le width positive)).eval env).toNat = _
    rw [SMTTerm.populationExtend_toNat, PopulationPlan.target_toNat, populationSlice_semantics]
  · contradiction

theorem SMTCheckedTerm.popCount_bound {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.popCount = .ok result) (env : SMTEnv) : (result.term.eval env).toNat ≤ width := by
  rw [word.popCount_toNat result built env, ← populationSlice_semantics]
  exact populationSlice_bound _ _ _

theorem SMTCheckedTerm.popCount_request {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.popCount = .ok result) (request : SMTTypedRequest (.bv width))
    (requested : result.toTypedRequest = .ok request) (env : SMTEnv) :
    request.target = result.term ∧ request.target.WellFormed ∧
      (request.target.eval env).toNat = popCountWidth (word.term.eval env).toNat width := by
  have actual := result.toTypedRequest_admitted request requested
  exact ⟨actual.1, actual.2.1, by rw [actual.1]; exact word.popCount_toNat result built env⟩

private theorem population_wrappedNat (width : Nat) (operand : Int) :
    (((operand % (2 : Int)^width) + (2 : Int)^width) % (2 : Int)^width).toNat =
      (BitVec.ofInt width operand).toNat := by
  rw [BitVec.toNat_ofInt, Int.natCast_pow]
  simp [Int.add_emod, Int.emod_emod]

/-- Connect actual emitted counts to the existing scalar opcode, including
negative or noncanonical integer carriers. Only the input mapping is a premise. -/
theorem SMTCheckedTerm.popCount_semIntUnOp {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (built : word.popCount = .ok result) (operand : Int) (env : SMTEnv)
    (source : word.term.eval env = BitVec.ofInt width operand) :
    semIntUnOp .CtPop width operand = .ok (Int.ofNat (result.term.eval env).toNat) := by
  rw [word.popCount_toNat result built env, source]
  simp only [semIntUnOp, population_wrappedNat]

end TrustIr.TrustIrExpr
