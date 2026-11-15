-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordWidths
import TrustIr.Semantics.Arith

/-- Read the actual finite array at its certified index under either API. -/
macro "trustIrPermArrayRead" : term => do
  if Lean.versionString == "4.8.0" then `(Array.get)
  else if Lean.versionString == "4.30.0-rc2" then
    `(fun (values : Array Nat) (index : Fin values.size) => values[index.val]'index.isLt)
  else Lean.Macro.throwError "unsupported compiler for permutation array access"

namespace TrustIr.AYGateCNF

/-- Reuse original wires directly. A permutation or projection needs no
fresh Boolean gate, including at width zero. -/
def WordCode.rewire {source target : Nat} (input : Fin source → Nat)
    (positions : Fin target → Fin source) : WordCode target :=
  ⟨[], fun i => input (positions i)⟩

theorem WordCode.rewire_check {source target : Nat} (input : Fin source → Nat)
    (positions : Fin target → Fin source) (next : Nat) (bound : ∀ i, input i < next) :
    (WordCode.rewire input positions).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  exact ⟨.nil next, fun i => bound (positions i)⟩

theorem WordCode.rewire_bit {source target : Nat} (input : Fin source → Nat)
    (positions : Fin target → Fin source) (env : Assignment) (i : Fin target) :
    (trustIrWordBit ((WordCode.rewire input positions).value env)) i.val = env (input (positions i)) :=
  wordValue_bit _ env i

def reversePosition {width : Nat} (i : Fin width) : Fin width :=
  ⟨width - 1 - i.val, by omega⟩

theorem reversePosition_involution {width : Nat} (i : Fin width) :
    reversePosition (reversePosition i) = i := by
  apply Fin.ext
  simp only [reversePosition]
  have bound := i.isLt
  omega

def WordCode.bitReverse {width : Nat} (input : Fin width → Nat) : WordCode width :=
  WordCode.rewire input reversePosition

theorem WordCode.bitReverse_check {width : Nat} (input : Fin width → Nat)
    (next : Nat) (bound : ∀ i, input i < next) :
    (WordCode.bitReverse input).check next = true := WordCode.rewire_check _ _ _ bound

theorem WordCode.bitReverse_bit {width : Nat} (input : Fin width → Nat)
    (env : Assignment) (i : Fin width) :
    (trustIrWordBit ((WordCode.bitReverse input).value env)) i.val =
      env (input (reversePosition i)) := WordCode.rewire_bit _ _ _ _

theorem wireNumber_append (left right : List Nat) (env : Assignment) :
    wireNumber (left ++ right) env = wireNumber left env + 2^left.length * wireNumber right env := by
  induction left with
  | nil => simp [wireNumber]
  | cons head tail ih =>
    change (env head).toNat + 2 * wireNumber (tail ++ right) env =
      (env head).toNat + 2 * wireNumber tail env + 2^(tail.length+1) * wireNumber right env
    rw [ih]
    simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc]
    rw [Nat.mul_left_comm (2^tail.length) 2 (wireNumber right env)]
    omega

theorem wireNumber_reverse (wires : List Nat) (env : Assignment) :
    wireNumber wires.reverse env = bitReverseWidth (wireNumber wires env) wires.length := by
  induction wires with
  | nil => rfl
  | cons head tail ih =>
    rw [List.reverse_cons, wireNumber_append, ih]
    simp only [List.length_cons, bitReverseWidth, wireNumber, List.foldr, List.length_reverse,
      Nat.mul_zero, Nat.add_zero]
    cases bit : env head <;> simp [bit, Nat.add_mul_div_left, Nat.mul_add_mod, Nat.add_comm]

theorem tabulate_reverse {width : Nat} (input : Fin width → Nat) :
    tabulate (fun i => input (reversePosition i)) = (tabulate input).reverse := by
  trustIrCompilerProof {
    apply List.ext_get (by simp)
    intro index leftBound rightBound
    have bound : index < width := by simpa using leftBound
    have reversed : width - 1 - index < width := by omega
    apply Option.some.inj
    rw [← List.get?_eq_get leftBound, ← List.get?_eq_get rightBound,
      List.get?_reverse _ (by simpa using bound)]
    simp only [tabulate_length]
    rw [List.get?_eq_get (by simpa using bound), List.get?_eq_get (by simpa using reversed)]
    rw [tabulate_get _ ⟨index, bound⟩, tabulate_get input ⟨width - 1 - index, reversed⟩]
    rfl
  } {
    apply List.ext_get (by simp)
    intro index leftBound rightBound
    have bound : index < width := by simpa using leftBound
    have reversed : width - 1 - index < width := by omega
    rw [tabulate_get _ ⟨index, bound⟩]
    simp only [List.get_eq_getElem, List.getElem_reverse, tabulate_length]
    change input (reversePosition ⟨index, bound⟩) =
      (tabulate input).get ⟨width - 1 - index, by simpa using reversed⟩
    rw [tabulate_get input ⟨width - 1 - index, reversed⟩]
    rfl
  }

/-- Exact equality to the integer semantics, without reducing the result
modulo its width or assuming any particular input bit pattern. -/
theorem WordCode.bitReverse_value {width : Nat} (input : Fin width → Nat)
    (env : Assignment) :
    ((WordCode.bitReverse input).value env).toNat =
      bitReverseWidth (wordValue input env).toNat width := by
  change (wordValue (fun i => input (reversePosition i)) env).toNat = _
  rw [wordValue_toNat, tabulate_reverse, wireNumber_reverse, tabulate_length, wordValue_toNat]

/-- A source word grouped into bytes. Each byte lists its wires from low bit
to high bit; the byte list itself is little-endian. -/
def byteWireList (bytes : List (Fin 8 → Nat)) : List Nat := trustIrListBind bytes tabulate

@[simp] theorem byteWireList_length (bytes : List (Fin 8 → Nat)) :
    (byteWireList bytes).length = bytes.length * 8 := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [byteWireList, trustIrWidthLemma List.cons_bind List.flatMap_cons, List.length_append, tabulate_length,
      List.length_cons] at *
    rw [ih]
    omega

/-- Turn a complete, fixed-width source wire list into a word, without
allocating constants or gates. -/
def WordCode.ofWireList (wires : List Nat) : WordCode wires.length :=
  let array := wires.toArray
  ⟨[], fun i => (trustIrPermArrayRead) array ⟨i.val, by
    change i.val < wires.toArray.size
    rw [trustIrWidthLemma Array.size_toArray List.size_toArray]
    exact i.isLt⟩⟩

private theorem permutation_array_get (wires : List Nat) (i : Fin wires.length) :
    (trustIrPermArrayRead) wires.toArray ⟨i.val, by rw [trustIrWidthLemma Array.size_toArray List.size_toArray]; exact i.isLt⟩ = wires.get i := by
  trustIrCompilerProof {
    have same := congrArg (fun xs : List Nat => xs.get? i.val) (Array.data_toArray wires)
    change wires.toArray.data.get? i.val = wires.get? i.val at same
    rw [List.get?_eq_get (by rw [Array.data_toArray]; exact i.isLt), List.get?_eq_get i.isLt] at same
    exact Option.some.inj same
  } {
    rfl
  }

theorem WordCode.ofWireList_bit (wires : List Nat) (i : Fin wires.length) :
    (WordCode.ofWireList wires).bits i = wires.get i := permutation_array_get wires i

theorem tabulate_get_list (wires : List Nat) : tabulate (fun i => wires.get i) = wires := by
  apply List.ext_get (by simp)
  intro index _leftBound rightBound
  exact tabulate_get _ ⟨index, rightBound⟩

theorem WordCode.ofWireList_value (wires : List Nat) (env : Assignment) :
    ((WordCode.ofWireList wires).value env).toNat = wireNumber wires env := by
  rw [WordCode.value, wordValue_toNat]
  change wireNumber (tabulate (WordCode.ofWireList wires).bits) env = _
  rw [show (WordCode.ofWireList wires).bits = (fun i => wires.get i) from
    funext (WordCode.ofWireList_bit wires)]
  rw [tabulate_get_list]

theorem WordCode.ofWireList_check (wires : List Nat) (next : Nat)
    (bound : ∀ id ∈ wires, id < next) : (WordCode.ofWireList wires).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  refine ⟨.nil next, ?_⟩
  intro i
  change (WordCode.ofWireList wires).bits i < next
  rw [WordCode.ofWireList_bit]
  trustIrCompilerProof { exact bound _ (List.get_mem _ _ _) } { exact bound _ (List.get_mem _ _) }

def WordCode.byteSwap (bytes : List (Fin 8 → Nat)) : WordCode (bytes.length * 8) :=
  let output := byteWireList bytes.reverse
  let array := output.toArray
  ⟨[], fun i => (trustIrPermArrayRead) array ⟨i.val, by
    change i.val < output.toArray.size
    rw [trustIrWidthLemma Array.size_toArray List.size_toArray, byteWireList_length, List.length_reverse]
    exact i.isLt⟩⟩

theorem WordCode.byteSwap_bit (bytes : List (Fin 8 → Nat)) (i : Fin (bytes.length*8)) :
    (WordCode.byteSwap bytes).bits i = (byteWireList bytes.reverse).get
      ⟨i.val, by rw [byteWireList_length, List.length_reverse]; exact i.isLt⟩ :=
  permutation_array_get (byteWireList bytes.reverse)
    ⟨i.val, by rw [byteWireList_length, List.length_reverse]; exact i.isLt⟩

private theorem permutation_mem_append {α : Type} (value : α) (left right : List α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons head tail ih => simp [List.mem_cons, ih, or_assoc]

theorem byteWireList_mem (bytes : List (Fin 8 → Nat)) (id : Nat) :
    id ∈ byteWireList bytes ↔ ∃ byte ∈ bytes, ∃ bit : Fin 8, byte bit = id := by
  induction bytes with
  | nil => simp [byteWireList]
  | cons byte rest ih =>
    simp only [byteWireList, trustIrWidthLemma List.cons_bind List.flatMap_cons, permutation_mem_append] at *
    constructor
    · intro member
      cases member with
      | inl current =>
        obtain ⟨bit, same⟩ := tabulate_cases _ _ current
        exact ⟨byte, by simp, bit, same⟩
      | inr later =>
        obtain ⟨other, member, bit, same⟩ := ih.mp later
        exact ⟨other, by simp [member], bit, same⟩
    · rintro ⟨other, member, bit, same⟩
      cases member with
      | head => exact Or.inl (same ▸ tabulate_mem byte bit)
      | tail _ member => exact Or.inr (ih.mpr ⟨other, member, bit, same⟩)

private theorem permutation_mem_reverse {α : Type} (value : α) (xs : List α) :
    value ∈ xs.reverse ↔ value ∈ xs := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp [List.reverse_cons, permutation_mem_append, ih, List.mem_cons, or_comm]

theorem WordCode.byteSwap_check (bytes : List (Fin 8 → Nat)) (next : Nat)
    (bound : ∀ byte ∈ bytes, ∀ bit, byte bit < next) :
    (WordCode.byteSwap bytes).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  refine ⟨.nil next, ?_⟩
  intro i
  have member : (WordCode.byteSwap bytes).bits i ∈ byteWireList bytes.reverse := by
    rw [WordCode.byteSwap_bit]
    trustIrCompilerProof { exact List.get_mem _ _ _ } { exact List.get_mem _ _ }
  obtain ⟨byte, member, bit, same⟩ := (byteWireList_mem _ _).mp member
  have original : byte ∈ bytes := (permutation_mem_reverse byte bytes).mp member
  simpa [same] using bound byte original bit

private theorem byteNumber_bound (byte : Fin 8 → Nat) (env : Assignment) :
    wireNumber (tabulate byte) env < 256 := by
  rw [← wordValue_toNat]
  exact (wordValue byte env).isLt

/-- The exact digit-reversal algebra of the actual flattened byte wires. -/
theorem wireNumber_byteSwap (bytes : List (Fin 8 → Nat)) (env : Assignment) :
    wireNumber (byteWireList bytes.reverse) env =
      bswapBytes (wireNumber (byteWireList bytes) env) bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have bounded := byteNumber_bound byte env
    have concat : byteWireList (rest.reverse ++ [byte]) =
        byteWireList rest.reverse ++ tabulate byte := by
      simp [byteWireList, trustIrWidthLemma List.append_bind List.flatMap_append]
    rw [List.reverse_cons, concat, wireNumber_append, ih, byteWireList_length]
    change _ = bswapBytes (wireNumber (tabulate byte ++ byteWireList rest) env) (rest.length+1)
    rw [wireNumber_append, tabulate_length, bswapBytes]
    have low : (wireNumber (tabulate byte) env + 2^8 * wireNumber (byteWireList rest) env) % 256 =
        wireNumber (tabulate byte) env := by omega
    have high : (wireNumber (tabulate byte) env + 2^8 * wireNumber (byteWireList rest) env) / 256 =
        wireNumber (byteWireList rest) env := by omega
    rw [low, high]
    have power : 2^(rest.length*8) = 256^rest.length := by
      rw [Nat.mul_comm, Nat.pow_mul]
    rw [List.length_reverse, power, Nat.mul_comm (wireNumber (tabulate byte) env)]
    omega

theorem WordCode.byteSwap_wireValue (bytes : List (Fin 8 → Nat)) (env : Assignment) :
    ((WordCode.byteSwap bytes).value env).toNat = wireNumber (byteWireList bytes.reverse) env := by
  rw [WordCode.value, wordValue_toNat]
  change wireNumber (tabulate (WordCode.byteSwap bytes).bits) env = _
  rw [show (WordCode.byteSwap bytes).bits = (fun i => (byteWireList bytes.reverse).get
    ⟨i.val, by rw [byteWireList_length, List.length_reverse]; exact i.isLt⟩) from
    funext (WordCode.byteSwap_bit bytes)]
  change wireNumber (tabulate (fun i : Fin (bytes.length*8) =>
    (byteWireList bytes.reverse).get ⟨i.val, by rw [byteWireList_length, List.length_reverse]; exact i.isLt⟩)) env = _
  congr 1
  apply List.ext_get (by simp)
  intro index leftBound rightBound
  have bound : index < bytes.length*8 := by simpa using leftBound
  exact tabulate_get _ ⟨index, bound⟩

theorem WordCode.byteSwap_value (bytes : List (Fin 8 → Nat)) (env : Assignment) :
    ((WordCode.byteSwap bytes).value env).toNat =
      bswapWidth ((WordCode.ofWireList (byteWireList bytes)).value env).toNat (bytes.length*8) := by
  rw [WordCode.byteSwap_wireValue, wireNumber_byteSwap, WordCode.ofWireList_value]
  simp [bswapWidth]

theorem WordCode.bitReverse_involution {width : Nat} (input : Fin width → Nat)
    (env : Assignment) :
    (WordCode.bitReverse (WordCode.bitReverse input).bits).value env = wordValue input env := by
  apply trustIrWordExt
  intro i
  rw [WordCode.bitReverse_bit, wordValue_bit]
  change env (input (reversePosition (reversePosition i))) = _
  rw [reversePosition_involution]

theorem WordCode.byteSwap_involution (bytes : List (Fin 8 → Nat)) (env : Assignment) :
    ((WordCode.byteSwap bytes.reverse).value env).toNat =
      ((WordCode.ofWireList (byteWireList bytes)).value env).toNat := by
  rw [WordCode.byteSwap_wireValue, List.reverse_reverse, WordCode.ofWireList_value]

theorem WordCode.bitReverse_no_gates {width : Nat} (input : Fin width → Nat) :
    (WordCode.bitReverse input).gates = [] := rfl

theorem WordCode.byteSwap_no_gates (bytes : List (Fin 8 → Nat)) :
    (WordCode.byteSwap bytes).gates = [] := rfl

private theorem permutation_wrappedNat (width : Nat) (operand : Int) :
    (((operand % (2 : Int)^width) + (2 : Int)^width) % (2 : Int)^width).toNat =
      (BitVec.ofInt width operand).toNat := by
  rw [BitVec.toNat_ofInt, Int.natCast_pow]
  simp [Int.add_emod, Int.emod_emod]

/-- The original scalar opcode on an arbitrary mathematical integer, including
negative and noncanonical carriers, returns the exact circuit result. -/
theorem WordCode.bitReverse_semIntUnOp {width : Nat} (input : Fin width → Nat)
    (env : Assignment) (operand : Int) (source : wordValue input env = BitVec.ofInt width operand) :
    semIntUnOp .BitReverse width operand =
      .ok (Int.ofNat ((WordCode.bitReverse input).value env).toNat) := by
  rw [WordCode.bitReverse_value, source]
  simp only [semIntUnOp, permutation_wrappedNat]

theorem WordCode.bitReverse_boundInput (width base : Nat) (operand : Int) (env : Assignment) :
    semIntUnOp .BitReverse width operand =
      .ok (Int.ofNat ((WordCode.bitReverse (fun i : Fin width => base+i.val)).value
        (bindWord base (BitVec.ofInt width operand) env)).toNat) :=
  WordCode.bitReverse_semIntUnOp _ _ operand (WordCode.input_value width base _ env)

/-- Byte swap's original scalar semantics, bound to the actual low-to-high
source wire image. Width is intrinsically a whole number of bytes. -/
theorem WordCode.byteSwap_semIntUnOp (bytes : List (Fin 8 → Nat))
    (env : Assignment) (operand : Int)
    (source : ((WordCode.ofWireList (byteWireList bytes)).value env).toNat =
      (BitVec.ofInt (bytes.length*8) operand).toNat) :
    semIntUnOp .BSwap (bytes.length*8) operand =
      .ok (Int.ofNat ((WordCode.byteSwap bytes).value env).toNat) := by
  rw [WordCode.byteSwap_value, source]
  simp only [semIntUnOp, permutation_wrappedNat]

def wireRange (count base : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ rest start => start :: rest (start+1)) count base

@[simp] theorem wireRange_zero (base : Nat) : wireRange 0 base = [] := rfl
@[simp] theorem wireRange_succ (count base : Nat) :
    wireRange (count+1) base = base :: wireRange count (base+1) := rfl

@[simp] theorem wireRange_length (count base : Nat) : (wireRange count base).length = count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simp [wireRange_succ, ih]

theorem wireRange_get? (count base index : Nat) (bound : index < count) :
    trustIrListGet? (wireRange count base) index = some (base+index) := by
  trustIrCompilerProof {
    induction count generalizing base index with
    | zero => omega
    | succ count ih =>
      cases index with
      | zero => simp [wireRange_zero, wireRange_succ]
      | succ index =>
        simp only [wireRange_succ, List.get?]
        change trustIrListGet? (wireRange count (base+1)) index = some (base+(index+1))
        rw [ih (base+1) index (by omega)]
        congr 1
        omega
  } {
    induction count generalizing base index with
    | zero => omega
    | succ count ih =>
      cases index with
      | zero => simp [wireRange_zero, wireRange_succ]
      | succ index =>
        simp only [wireRange_succ, trustIrListGetConsSucc]
        change trustIrListGet? (wireRange count (base+1)) index = some (base+(index+1))
        rw [ih (base+1) index (by omega)]
        congr 1
        omega
  }

theorem wireRange_tabulate (count base : Nat) :
    wireRange count base = tabulate (fun i : Fin count => base+i.val) := by
  trustIrCompilerProof {
    apply List.ext_get (by simp)
    intro index leftBound rightBound
    have bound : index < count := by simpa using leftBound
    apply Option.some.inj
    rw [← List.get?_eq_get leftBound, wireRange_get? count base index bound]
    rw [tabulate_get _ ⟨index, bound⟩]
  } {
    apply List.ext_get (by simp)
    intro index leftBound rightBound
    have bound : index < count := by simpa using leftBound
    rw [tabulate_get _ ⟨index, bound⟩]
    apply Option.some.inj
    change some ((wireRange count base)[index]) = some (base + index)
    have selected := CompilerCompat.listGet?_eq_get (values := wireRange count base) leftBound
    rw [wireRange_get? count base index bound] at selected
    simpa only [List.get_eq_getElem] using selected.symm
  }

theorem wireRange_append (left right base : Nat) :
    wireRange (left+right) base = wireRange left base ++ wireRange right (base+left) := by
  induction left generalizing base with
  | zero => simp [wireRange_zero, wireRange_succ]
  | succ left ih =>
    simp only [Nat.succ_add, wireRange_succ, List.cons_append]
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The concrete original input slice, grouped only for byte routing. -/
def byteInputs (count base : Nat) : List (Fin 8 → Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Fin 8 → Nat)) (fun _ => [])
    (fun _ rest start => (fun bit => start+bit.val) :: rest (start+8)) count base

@[simp] theorem byteInputs_zero (base : Nat) : byteInputs 0 base = [] := rfl
@[simp] theorem byteInputs_succ (count base : Nat) :
    byteInputs (count+1) base = (fun bit => base+bit.val) :: byteInputs count (base+8) := rfl

@[simp] theorem byteInputs_length (count base : Nat) : (byteInputs count base).length = count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simp [byteInputs_succ, ih]

theorem byteInputs_wires (count base : Nat) :
    byteWireList (byteInputs count base) = wireRange (count*8) base := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
    change tabulate (fun bit : Fin 8 => base+bit.val) ++
      byteWireList (byteInputs count (base+8)) = _
    rw [ih, ← wireRange_tabulate]
    have size : (count+1)*8 = 8+count*8 := by omega
    rw [size, wireRange_append]

/-- No endpoint receipt is assumed here: the byte image is the actual input
slice, populated by bindWord from the original arbitrary integer operand. -/
theorem WordCode.byteSwap_boundInput (count base : Nat) (operand : Int) (env : Assignment) :
    semIntUnOp .BSwap (count*8) operand =
      .ok (Int.ofNat ((WordCode.byteSwap (byteInputs count base)).value
        (bindWord base (BitVec.ofInt (count*8) operand) env)).toNat) := by
  have source : ((WordCode.ofWireList (byteWireList (byteInputs count base))).value
      (bindWord base (BitVec.ofInt (count*8) operand) env)).toNat =
        (BitVec.ofInt ((byteInputs count base).length*8) operand).toNat := by
    rw [WordCode.ofWireList_value, byteInputs_wires, wireRange_tabulate,
      ← wordValue_toNat, byteInputs_length]
    exact congrArg BitVec.toNat (WordCode.input_value (count*8) base _ env)
  simpa only [byteInputs_length] using
    WordCode.byteSwap_semIntUnOp (byteInputs count base) _ operand source

theorem WordCode.byteSwap_boundCheck (count base next : Nat) (bound : base+count*8 ≤ next) :
    (WordCode.byteSwap (byteInputs count base)).check next = true := by
  apply WordCode.byteSwap_check
  intro byte member bit
  have source : byte bit ∈ byteWireList (byteInputs count base) :=
    (byteWireList_mem _ _).mpr ⟨byte, member, bit, rfl⟩
  rw [byteInputs_wires, wireRange_tabulate] at source
  obtain ⟨i, same⟩ := tabulate_cases _ _ source
  omega

end TrustIr.AYGateCNF
