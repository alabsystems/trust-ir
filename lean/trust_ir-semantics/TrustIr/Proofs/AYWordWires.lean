-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBooleanCompile
import Init.Data.Array.Lemmas

/-- Select the actual Nat-indexed defaulting lookup, including out-of-range bits. -/
macro "trustIrWordBit" : term => do
  if Lean.versionString == "4.8.0" then `(BitVec.getLsb)
  else if Lean.versionString == "4.30.0-rc2" then `(BitVec.getLsbD)
  else Lean.Macro.throwError "unsupported compiler for word bit lookup"
/-- Expose the actual ordered list behind the array enumeration. -/
macro "trustIrWordArrayList" : term => do
  if Lean.versionString == "4.8.0" then `(Array.data)
  else if Lean.versionString == "4.30.0-rc2" then `(Array.toList)
  else Lean.Macro.throwError "unsupported compiler for word enumeration"
macro "trustIrWordExt" : term => do
  if Lean.versionString == "4.8.0" then `(BitVec.eq_of_getLsb_eq)
  else if Lean.versionString == "4.30.0-rc2" then pure (Lean.mkIdent `TrustIr.AYGateCNF.word_ext)
  else Lean.Macro.throwError "unsupported compiler for word extensionality"

namespace TrustIr.AYGateCNF
universe u
trustIrBitVec430 theorem word_ext {w : Nat} {x y : BitVec w}
    (h : ∀ i : Fin w, x.getLsbD i.val = y.getLsbD i.val) : x = y :=
  BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i, hi⟩)
trustIrBitVec430 #trustIrAxiomsExact word_ext == [propext, Quot.sound]

/-- Enumerate a width-indexed vector using core array construction. -/
def tabulate {width : Nat} {α : Type u} (f : Fin width → α) : List α := (trustIrWordArrayList (Array.ofFn f))

@[simp] theorem tabulate_length {width : Nat} {α : Type u} (f : Fin width → α) :
    (tabulate f).length = width := by
  trustIrCompilerProof {
    change (Array.ofFn f).size = width
    exact Array.size_ofFn f
  } {
    change (Array.ofFn f).size = width
    exact Array.size_ofFn
  }

theorem tabulate_get {width : Nat} {α : Type u} (f : Fin width → α) (i : Fin width) :
    (tabulate f).get ⟨i.val, by rw [tabulate_length]; exact i.isLt⟩ = f i := by
  trustIrCompilerProof {
    change (trustIrWordArrayList (Array.ofFn f)).get _ = f i
    rw [← Array.getElem_eq_data_get]
    exact Array.getElem_ofFn f i.val (by rw [Array.size_ofFn]; exact i.isLt)
  } {
    simp only [tabulate, List.get_eq_getElem, Array.getElem_toList, Array.getElem_ofFn]
  }

theorem tabulate_getD {width : Nat} {α : Type u} (f : Fin width → α) (i : Fin width) (fallback : α) :
    (tabulate f).getD i.val fallback = f i := by
  trustIrCompilerProof {
    rw [List.getD_eq_get?, List.get?_eq_get (by rw [tabulate_length]; exact i.isLt)]
    exact tabulate_get f i
  } {
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tabulate_length]; exact i.isLt)]
    exact tabulate_get f i
  }

theorem tabulate_mem {width : Nat} {α : Type u} (f : Fin width → α) (i : Fin width) :
    f i ∈ tabulate f := by
  trustIrCompilerProof {
    rw [← tabulate_get f i]
    exact List.get_mem _ _ _
  } {
    rw [← tabulate_get f i]
    exact List.get_mem _ _
  }

theorem tabulate_cases {width : Nat} {α : Type u} (f : Fin width → α) (value : α)
    (member : value ∈ tabulate f) : ∃ i : Fin width, f i = value := by
  obtain ⟨index, same⟩ := List.get_of_mem member
  let i : Fin width := ⟨index.val, by simpa using index.isLt⟩
  have getEq : (tabulate f).get index = f i := tabulate_get f i
  exact ⟨i, getEq.symm.trans same⟩

/-- Native little-endian word interpretation of width-indexed wires. -/
def wordValue {width : Nat} (wires : Fin width → Nat) (env : Assignment) : BitVec width :=
  (BitVec.ofBoolListLE (tabulate (fun i => env (wires i)))).cast (tabulate_length _)

@[simp] theorem wordValue_bit {width : Nat} (wires : Fin width → Nat) (env : Assignment) (i : Fin width) :
    (trustIrWordBit (wordValue wires env)) i.val = env (wires i) := by
  trustIrCompilerProof {
    simp only [wordValue, BitVec.getLsb_cast, BitVec.getLsb_ofBoolListLE]
    exact tabulate_getD _ i false
  } {
    simp only [wordValue, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
    exact tabulate_getD _ i false
  }

/-- Decode a little-endian list of Boolean wires as an unbounded natural. -/
def wireNumber (wires : List Nat) (env : Assignment) : Nat :=
  wires.foldr (fun bit rest => (env bit).toNat + 2 * rest) 0

private theorem tabulate_map {width : Nat} {α β : Type} (f : Fin width → α) (g : α → β) :
    (tabulate f).map g = tabulate (fun i => g (f i)) := by
  trustIrCompilerProof {
    apply List.ext_get (by simp)
    intro n h₁ h₂
    rw [List.get_map]
    have bound : n < width := by simpa using h₂
    rw [tabulate_get f ⟨n, bound⟩, tabulate_get (fun i => g (f i)) ⟨n, bound⟩]
  } {
    apply List.ext_get (by simp)
    intro n h₁ h₂
    simp only [List.get_eq_getElem, List.getElem_map]
    change g ((tabulate f).get ⟨n, by simpa using h₂⟩) = (tabulate (fun i => g (f i))).get ⟨n, h₂⟩
    have bound : n < width := by simpa using h₂
    rw [tabulate_get f ⟨n, bound⟩, tabulate_get (fun i => g (f i)) ⟨n, bound⟩]
  }

private theorem list_word_toNat (wires : List Nat) (env : Assignment) :
    (BitVec.ofBoolListLE (wires.map env)).toNat = wireNumber wires env := by
  induction wires with
  | nil => rfl
  | cons bit rest ih =>
    simp only [List.map, BitVec.ofBoolListLE, BitVec.toNat_concat, wireNumber, List.foldr]
    rw [ih]
    simp only [wireNumber]
    omega

theorem wordValue_toNat {width : Nat} (wires : Fin width → Nat) (env : Assignment) :
    (wordValue wires env).toNat = wireNumber (tabulate wires) env := by
  rw [wordValue, BitVec.toNat_cast, ← tabulate_map wires env]
  exact list_word_toNat _ _

theorem wordValue_congr {width : Nat} (wires : Fin width → Nat) (left right : Assignment)
    (agree : ∀ i, left (wires i) = right (wires i)) : wordValue wires left = wordValue wires right := by
  apply trustIrWordExt
  intro i
  simpa only [wordValue_bit] using agree i

private theorem valid_positions (gates : List Gate) (next : Nat)
    (outputs : ∀ i : Fin gates.length, (gates.get i).output = next + i.val)
    (inputs : ∀ i : Fin gates.length, ∀ id ∈ (gates.get i).inputs, id < next + i.val) :
    Valid next gates := by
  induction gates generalizing next with
  | nil => exact .nil next
  | cons gate tail ih =>
    apply Valid.cons (next := next) (gate := gate)
      (by simpa using outputs ⟨0, by simp⟩)
      (by simpa using inputs ⟨0, by simp⟩)
    apply ih (next + 1)
    · intro i
      have same := outputs ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      change (tail.get i).output = next + (i.val + 1) at same
      omega
    · intro i id member
      have before := inputs ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ id member
      change id < next + (i.val + 1) at before
      omega

/-- One fresh gate per vector position realizes a complete width-sized block. -/
theorem Valid.vector {width : Nat} (make : Fin width → Gate) (next : Nat)
    (outputs : ∀ i, (make i).output = next + i.val)
    (inputs : ∀ i, ∀ id ∈ (make i).inputs, id < next + i.val) : Valid next (tabulate make) := by
  apply valid_positions
  · intro index
    let i : Fin width := ⟨index.val, by simpa using index.isLt⟩
    have same : (tabulate make).get index = make i := tabulate_get make i
    rw [same]
    exact outputs i
  · intro index id member
    let i : Fin width := ⟨index.val, by simpa using index.isLt⟩
    have same : (tabulate make).get index = make i := tabulate_get make i
    rw [same] at member
    exact inputs i id member

/-- Word results carry a statically fixed number of result wires. -/
structure WordCode (width : Nat) where
  gates : List Gate
  bits : Fin width → Nat

instance {width : Nat} : Repr (WordCode width) where
  reprPrec code _ := repr (code.gates, tabulate code.bits)

def WordCode.value {width : Nat} (code : WordCode width) (env : Assignment) : BitVec width :=
  wordValue code.bits (run code.gates env)

def WordCode.check {width : Nat} (code : WordCode width) (next : Nat) : Bool :=
  checkProgram next code.gates &&
    (tabulate code.bits).all (fun id => decide (id < next + code.gates.length))

theorem WordCode.check_iff {width : Nat} (code : WordCode width) (next : Nat) :
    code.check next = true ↔ Valid next code.gates ∧ ∀ i, code.bits i < next + code.gates.length := by
  simp only [WordCode.check, Bool.and_eq_true, checkProgram_iff]
  constructor
  · rintro ⟨valid, bounds⟩
    refine ⟨valid, fun i => ?_⟩
    have all : ∀ id ∈ tabulate code.bits, id < next + code.gates.length := by simpa using bounds
    exact all _ (tabulate_mem code.bits i)
  · rintro ⟨valid, bounds⟩
    refine ⟨valid, ?_⟩
    have all : ∀ id ∈ tabulate code.bits, id < next + code.gates.length := by
      intro id member
      obtain ⟨i, same⟩ := tabulate_cases code.bits id member
      rw [← same]
      exact bounds i
    simpa using all

/-- Reference an already allocated input word without allocating gates. -/
def WordCode.input (width base : Nat) : WordCode width := ⟨[], fun i => base + i.val⟩

theorem WordCode.input_check (width base next : Nat) (bound : base + width ≤ next) :
    (WordCode.input width base).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  refine ⟨.nil next, ?_⟩
  intro i
  have before := i.isLt
  change base + i.val < next + 0
  omega

/-- Bind precisely this input slice to a native word; other variables survive. -/
def bindWord {width : Nat} (base : Nat) (word : BitVec width) (env : Assignment) : Assignment :=
  fun id => if base ≤ id ∧ id < base + width then (trustIrWordBit word) (id - base) else env id

theorem bindWord_bit {width : Nat} (base : Nat) (word : BitVec width) (env : Assignment) (i : Fin width) :
    bindWord base word env (base + i.val) = (trustIrWordBit word) i.val := by
  have before := i.isLt
  simp [bindWord, show base ≤ base + i.val by omega,
    show base + i.val < base + width by omega, show base + i.val - base = i.val by omega]

theorem bindWord_outside {width : Nat} (base : Nat) (word : BitVec width) (env : Assignment) (id : Nat)
    (outside : id < base ∨ base + width ≤ id) : bindWord base word env id = env id := by
  simp [bindWord, show ¬ (base ≤ id ∧ id < base + width) by omega]

theorem WordCode.input_value (width base : Nat) (word : BitVec width) (env : Assignment) :
    (WordCode.input width base).value (bindWord base word env) = word := by
  apply trustIrWordExt
  intro i
  change (trustIrWordBit (wordValue (fun i : Fin width => base + i.val) (bindWord base word env))) i.val = _
  rw [wordValue_bit, bindWord_bit]

inductive BitwiseOp where
  | band | bor | bxor
  deriving Repr

def BitwiseOp.evalBit : BitwiseOp → Bool → Bool → Bool
  | .band, a, b => a && b
  | .bor, a, b => a || b
  | .bxor, a, b => xor a b

def BitwiseOp.eval {width : Nat} : BitwiseOp → BitVec width → BitVec width → BitVec width
  | .band, a, b => a &&& b
  | .bor, a, b => a ||| b
  | .bxor, a, b => a ^^^ b

def BitwiseOp.gate : BitwiseOp → Nat → Nat → Nat → Gate
  | .band, out, a, b => .and2 out a b
  | .bor, out, a, b => .or2 out a b
  | .bxor, out, a, b => .xor2 out a b

theorem BitwiseOp.gate_output (op : BitwiseOp) (out a b : Nat) :
    (op.gate out a b).output = out := by cases op <;> rfl

theorem BitwiseOp.gate_eval (op : BitwiseOp) (out a b : Nat) (env : Assignment) :
    (op.gate out a b).eval env = op.evalBit (env a) (env b) := by cases op <;> rfl

theorem BitwiseOp.eval_bit {width : Nat} (op : BitwiseOp) (left right : BitVec width) (i : Fin width) :
    (trustIrWordBit (op.eval left right)) i.val = op.evalBit ((trustIrWordBit left) i.val) ((trustIrWordBit right) i.val) := by
  cases op <;> simp [BitwiseOp.eval, BitwiseOp.evalBit]

/-- Compile every result bit to one fresh Boolean gate. -/
def WordCode.bitwise {width : Nat} (op : BitwiseOp) (left right : Fin width → Nat) (next : Nat) :
    WordCode width :=
  ⟨tabulate (fun i => op.gate (next + i.val) (left i) (right i)), fun i => next + i.val⟩

def WordCode.bitNot {width : Nat} (input : Fin width → Nat) (next : Nat) : WordCode width :=
  ⟨tabulate (fun i => Gate.not (next + i.val) (input i)), fun i => next + i.val⟩

def WordCode.constant {width : Nat} (word : BitVec width) (next : Nat) : WordCode width :=
  ⟨tabulate (fun i : Fin width => if (trustIrWordBit word) i.val then .constTrue (next + i.val)
    else .constFalse (next + i.val)), fun i => next + i.val⟩

theorem WordCode.bitwise_check {width : Nat} (op : BitwiseOp) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) :
    (WordCode.bitwise op left right next).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  constructor
  · apply Valid.vector
    · intro i; exact op.gate_output _ _ _
    · intro i
      have a : left i < next + i.val := by have h := leftBound i; omega
      have b : right i < next + i.val := by have h := rightBound i; omega
      cases op <;> simpa [BitwiseOp.gate, Gate.inputs] using And.intro a b
  · intro i
    have h := i.isLt
    change next + i.val < next + (tabulate _).length
    rw [tabulate_length]
    omega

theorem WordCode.bitNot_check {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) : (WordCode.bitNot input next).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  constructor
  · apply Valid.vector
    · intro i; rfl
    · intro i
      have before : input i < next + i.val := by have h := bound i; omega
      simpa [Gate.inputs] using before
  · intro i
    have h := i.isLt
    change next + i.val < next + (tabulate _).length
    rw [tabulate_length]
    omega

theorem WordCode.constant_check {width : Nat} (word : BitVec width) (next : Nat) :
    (WordCode.constant word next).check next = true := by
  apply (WordCode.check_iff _ _).mpr
  constructor
  · apply Valid.vector
    · intro i
      cases h : (trustIrWordBit word) i.val <;> simp [Gate.output, h]
    · intro i
      cases h : (trustIrWordBit word) i.val <;> simp [Gate.inputs, h]
  · intro i
    have h := i.isLt
    change next + i.val < next + (tabulate _).length
    rw [tabulate_length]
    omega

/-- Native word bitwise semantics follows from actual generated fresh gates. -/
theorem WordCode.bitwise_value {width : Nat} (op : BitwiseOp) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment) :
    (WordCode.bitwise op left right next).value env = op.eval (wordValue left env) (wordValue right env) := by
  have valid := ((WordCode.check_iff _ _).mp (WordCode.bitwise_check op left right next leftBound rightBound)).1
  obtain ⟨preserved, equations⟩ := valid.run_correct env
  apply trustIrWordExt
  intro i
  have equation := equations (op.gate (next + i.val) (left i) (right i))
    (tabulate_mem (fun i : Fin width => op.gate (next + i.val) (left i) (right i)) i)
  rw [BitwiseOp.gate_output, BitwiseOp.gate_eval, preserved _ (leftBound i), preserved _ (rightBound i)] at equation
  change (trustIrWordBit (wordValue (fun i : Fin width => next + i.val) (run _ env))) i.val = _
  rw [wordValue_bit, BitwiseOp.eval_bit, wordValue_bit, wordValue_bit]
  exact equation

theorem WordCode.bitNot_value {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) :
    (WordCode.bitNot input next).value env = ~~~(wordValue input env) := by
  have valid := ((WordCode.check_iff _ _).mp (WordCode.bitNot_check input next bound)).1
  obtain ⟨preserved, equations⟩ := valid.run_correct env
  apply trustIrWordExt
  intro i
  have equation := equations (Gate.not (next + i.val) (input i))
    (tabulate_mem (fun i : Fin width => Gate.not (next + i.val) (input i)) i)
  change run _ env (next + i.val) = !(run _ env (input i)) at equation
  rw [preserved _ (bound i)] at equation
  change (trustIrWordBit (wordValue (fun i : Fin width => next + i.val) (run _ env))) i.val = _
  trustIrCompilerProof {
    rw [wordValue_bit, BitVec.getLsb_not, wordValue_bit]
  } {
    rw [wordValue_bit, BitVec.getLsbD_not, wordValue_bit]
  }
  simpa [i.isLt] using equation

theorem WordCode.constant_value {width : Nat} (word : BitVec width) (next : Nat) (env : Assignment) :
    (WordCode.constant word next).value env = word := by
  have valid := ((WordCode.check_iff _ _).mp (WordCode.constant_check word next)).1
  have equations := (valid.run_correct env).2
  apply trustIrWordExt
  intro i
  have equation := equations
    (if (trustIrWordBit word) i.val then Gate.constTrue (next + i.val) else Gate.constFalse (next + i.val))
    (tabulate_mem (fun i : Fin width => if (trustIrWordBit word) i.val then Gate.constTrue (next + i.val)
      else Gate.constFalse (next + i.val)) i)
  change (trustIrWordBit (wordValue (fun i : Fin width => next + i.val) (run _ env))) i.val = _
  rw [wordValue_bit]
  trustIrCompilerProof {
    cases h : (trustIrWordBit word) i.val <;> simpa [Gate.output, Gate.eval, h] using equation
  } {
    cases h : (trustIrWordBit word) i.val <;> simpa only [h, Bool.false_eq_true, ↓reduceIte, Gate.output, Gate.eval] using equation
  }

def BitwiseOp.target (op : BitwiseOp) (width : Nat) : TrustIrExpr.SMTBinary (.bv width) (.bv width) :=
  match op with
  | .band => .bvAnd width
  | .bor => .bvOr width
  | .bxor => .bvXor width

theorem BitwiseOp.target_eval {width : Nat} (op : BitwiseOp) (left right : BitVec width) :
    (op.target width).eval left right = op.eval left right := by cases op <;> rfl

/-- Input bit binding realizes the actual target variable, including arbitrary
signed/oversized integer assignments through the native word conversion. -/
theorem WordCode.input_target (width base : Nat) (symbol : String) (target : SMTEnv) (env : Assignment) :
    (WordCode.input width base).value (bindWord base (BitVec.ofInt width (target symbol)) env) =
      (TrustIrExpr.SMTTerm.var width symbol).eval target :=
  WordCode.input_value width base _ env

theorem WordCode.constant_target (width next : Nat) (value : Int) (target : SMTEnv) (env : Assignment) :
    (WordCode.constant (BitVec.ofInt width value) next).value env =
      (TrustIrExpr.SMTTerm.bvConst width value).eval target :=
  WordCode.constant_value _ next env

theorem WordCode.bitwise_target {width : Nat} (op : BitwiseOp) (left right : Fin width → Nat) (next : Nat)
    (leftBound : ∀ i, left i < next) (rightBound : ∀ i, right i < next) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : wordValue left env = leftTerm.eval target)
    (rightValue : wordValue right env = rightTerm.eval target) :
    (WordCode.bitwise op left right next).value env =
      (TrustIrExpr.SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [WordCode.bitwise_value op left right next leftBound rightBound env, leftValue, rightValue]
  exact (op.target_eval _ _).symm

theorem WordCode.bitNot_target {width : Nat} (input : Fin width → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment)
    (term : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (inputValue : wordValue input env = term.eval target) :
    (WordCode.bitNot input next).value env =
      (TrustIrExpr.SMTTerm.unary (.bvNot width) term).eval target := by
  rw [WordCode.bitNot_value input next bound env, inputValue]
  rfl

/-- Compose a prefix and a word result, retaining the suffix's typed wires. -/
def WordCode.append {a b : Nat} (first : WordCode a) (second : WordCode b) : WordCode b :=
  ⟨first.gates ++ second.gates, second.bits⟩

theorem WordCode.append_check {a b : Nat} (first : WordCode a) (second : WordCode b) (next : Nat)
    (firstCheck : first.check next = true)
    (secondCheck : second.check (next + first.gates.length) = true) :
    (WordCode.append first second).check next = true := by
  obtain ⟨firstValid, _firstBounds⟩ := (first.check_iff next).mp firstCheck
  obtain ⟨secondValid, secondBounds⟩ := (second.check_iff _).mp secondCheck
  apply (WordCode.check_iff _ _).mpr
  refine ⟨firstValid.append secondValid, ?_⟩
  intro i
  simpa [WordCode.append, Nat.add_assoc] using secondBounds i

theorem WordCode.append_value {a b : Nat} (first : WordCode a) (second : WordCode b) (env : Assignment) :
    (WordCode.append first second).value env = second.value (run first.gates env) := by
  simp only [WordCode.append, WordCode.value, run_append]

/-- Both child result vectors precede the frontier after appending their programs. -/
theorem WordCode.append_operand_bounds {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (∀ i, left.bits i < next + (WordCode.append left right).gates.length) ∧
      (∀ i, right.bits i < next + (WordCode.append left right).gates.length) := by
  have leftBounds := ((left.check_iff next).mp leftCheck).2
  have rightBounds := ((right.check_iff _).mp rightCheck).2
  simp only [WordCode.append, List.length_append]
  constructor
  · intro i; have bound := leftBounds i; omega
  · intro i; have bound := rightBounds i; omega

def WordCode.composeNot {width : Nat} (next : Nat) (child : WordCode width) : WordCode width :=
  WordCode.append child (WordCode.bitNot child.bits (next + child.gates.length))

theorem WordCode.composeNot_check {width : Nat} (next : Nat) (child : WordCode width)
    (checked : child.check next = true) : (WordCode.composeNot next child).check next = true := by
  apply WordCode.append_check child _ next checked
  exact WordCode.bitNot_check _ _ ((child.check_iff next).mp checked).2

theorem WordCode.composeNot_value {width : Nat} (next : Nat) (child : WordCode width)
    (checked : child.check next = true) (env : Assignment) :
    (WordCode.composeNot next child).value env = ~~~(child.value env) := by
  rw [WordCode.composeNot, WordCode.append_value,
    WordCode.bitNot_value _ _ ((child.check_iff next).mp checked).2]
  rfl

def WordCode.composeBitwise {width : Nat} (op : BitwiseOp) (next : Nat)
    (left right : WordCode width) : WordCode width :=
  let both := WordCode.append left right
  WordCode.append both (WordCode.bitwise op left.bits right.bits (next + both.gates.length))

private theorem word_binary_bounds {width : Nat} (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (∀ i, left.bits i < next + (WordCode.append left right).gates.length) ∧
      (∀ i, right.bits i < next + (WordCode.append left right).gates.length) := by
  have leftBounds := ((left.check_iff next).mp leftCheck).2
  have rightBounds := ((right.check_iff _).mp rightCheck).2
  simp only [WordCode.append, List.length_append]
  constructor
  · intro i; have h := leftBounds i; omega
  · intro i; have h := rightBounds i; omega

theorem WordCode.composeBitwise_check {width : Nat} (op : BitwiseOp) (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) :
    (WordCode.composeBitwise op next left right).check next = true := by
  obtain ⟨leftBounds, rightBounds⟩ := word_binary_bounds next left right leftCheck rightCheck
  apply WordCode.append_check _ _ next (WordCode.append_check left right next leftCheck rightCheck)
  exact WordCode.bitwise_check op _ _ _ leftBounds rightBounds

theorem WordCode.composeBitwise_value {width : Nat} (op : BitwiseOp) (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment) :
    (WordCode.composeBitwise op next left right).value env =
      op.eval (left.value env) (right.value (run left.gates env)) := by
  obtain ⟨leftBounds, rightBounds⟩ := word_binary_bounds next left right leftCheck rightCheck
  have rightValid := ((right.check_iff _).mp rightCheck).1
  have leftValue : wordValue left.bits (run (WordCode.append left right).gates env) = left.value env := by
    apply wordValue_congr
    intro i
    exact rightValid.append_preserves (next := next) (first := left.gates) env (left.bits i)
      (((left.check_iff next).mp leftCheck).2 i)
  have rightValue : wordValue right.bits (run (WordCode.append left right).gates env) =
      right.value (run left.gates env) := by rw [WordCode.append, run_append]; rfl
  rw [WordCode.composeBitwise, WordCode.append_value,
    WordCode.bitwise_value op _ _ _ leftBounds rightBounds, leftValue, rightValue]

theorem WordCode.composeBitwise_target {width : Nat} (op : BitwiseOp) (next : Nat) (left right : WordCode width)
    (leftCheck : left.check next = true)
    (rightCheck : right.check (next + left.gates.length) = true) (env : Assignment)
    (leftTerm rightTerm : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (leftValue : left.value env = leftTerm.eval target)
    (rightValue : right.value (run left.gates env) = rightTerm.eval target) :
    (WordCode.composeBitwise op next left right).value env =
      (TrustIrExpr.SMTTerm.binary (op.target width) leftTerm rightTerm).eval target := by
  rw [WordCode.composeBitwise_value op next left right leftCheck rightCheck env, leftValue, rightValue]
  exact (op.target_eval _ _).symm

theorem WordCode.composeNot_target {width : Nat} (next : Nat) (child : WordCode width)
    (checked : child.check next = true) (env : Assignment)
    (term : TrustIrExpr.SMTTerm (.bv width)) (target : SMTEnv)
    (childValue : child.value env = term.eval target) :
    (WordCode.composeNot next child).value env =
      (TrustIrExpr.SMTTerm.unary (.bvNot width) term).eval target := by
  rw [WordCode.composeNot_value next child checked env, childValue]
  rfl

/-- Append a Boolean result to a word-producing prefix without copying gates. -/
def WordCode.appendBool {width : Nat} (first : WordCode width) (second : Code) : Code :=
  ⟨first.gates ++ second.gates, second.output⟩

theorem WordCode.appendBool_check {width : Nat} (first : WordCode width) (second : Code) (next : Nat)
    (firstCheck : first.check next = true)
    (secondCheck : second.check (next + first.gates.length) = true) :
    (first.appendBool second).check next = true := by
  obtain ⟨firstValid, _⟩ := (first.check_iff next).mp firstCheck
  obtain ⟨secondValid, secondBound⟩ := (second.check_iff _).mp secondCheck
  apply (Code.check_iff _ _).mpr
  refine ⟨firstValid.append secondValid, ?_⟩
  simpa [WordCode.appendBool, Nat.add_assoc] using secondBound

theorem WordCode.appendBool_eval {width : Nat} (first : WordCode width) (second : Code) (env : Assignment) :
    (first.appendBool second).eval env = second.eval (run first.gates env) :=
  congrFun (run_append first.gates second.gates env) second.output

/-- Retain a Boolean-producing prefix and return a word from its fresh suffix. -/
def Code.appendWord {width : Nat} (first : Code) (second : WordCode width) : WordCode width :=
  ⟨first.gates ++ second.gates, second.bits⟩

theorem Code.appendWord_check {width : Nat} (first : Code) (second : WordCode width) (next : Nat)
    (firstCheck : first.check next = true)
    (secondCheck : second.check (next + first.gates.length) = true) :
    (first.appendWord second).check next = true := by
  obtain ⟨firstValid, _⟩ := (first.check_iff next).mp firstCheck
  obtain ⟨secondValid, secondBounds⟩ := (second.check_iff _).mp secondCheck
  apply (WordCode.check_iff _ _).mpr
  refine ⟨firstValid.append secondValid, ?_⟩
  intro i
  simpa [Code.appendWord, Nat.add_assoc] using secondBounds i

theorem Code.appendWord_value {width : Nat} (first : Code) (second : WordCode width) (env : Assignment) :
    (first.appendWord second).value env = second.value (run first.gates env) := by
  simp only [Code.appendWord, WordCode.value, run_append]

/-- Actual AND gates select a word using one shared input bit. -/
theorem WordCode.mask_value {width : Nat} (left : Fin width → Nat) (bit next : Nat)
    (leftBound : ∀ i, left i < next) (bitBound : bit < next) (env : Assignment) :
    (WordCode.bitwise .band left (fun _ => bit) next).value env =
      if env bit then wordValue left env else BitVec.ofNat width 0 := by
  trustIrCompilerProof {
    rw [WordCode.bitwise_value _ _ _ _ leftBound (fun _ => bitBound)]
    apply trustIrWordExt
    intro i
    simp only [BitwiseOp.eval, BitVec.getLsb_and, wordValue_bit]
    cases same : env bit <;> simp [same]
  } {
    rw [WordCode.bitwise_value _ _ _ _ leftBound (fun _ => bitBound)]
    apply trustIrWordExt
    intro i
    simp only [BitwiseOp.eval, BitVec.getLsbD_and, wordValue_bit]
    cases same : env bit <;> simp only [same, Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, wordValue_bit, BitVec.getLsbD_zero]
  }

/-- Checked executable evaluation uses a finite array; value remains the
reference semantics. Invalid programs or result wires are refused. -/
def WordCode.checkedEval {width : Nat} (code : WordCode width) (next : Nat) (env : Assignment) : Option (BitVec width) :=
  if code.check next then some (wordValue code.bits (runBuffered next code.gates env)) else none

theorem WordCode.checkedEval_eq_some {width : Nat} (code : WordCode width) (next : Nat)
    (env : Assignment) (result : BitVec width) :
    code.checkedEval next env = some result ↔ code.check next = true ∧ code.value env = result := by
  by_cases checked : code.check next = true
  · have program := (checkProgram_iff next code.gates).mpr ((code.check_iff next).mp checked).1
    have same : wordValue code.bits (runBuffered next code.gates env) = code.value env := by
      rw [runBuffered_eq_run next code.gates program]
      rfl
    simp [WordCode.checkedEval, checked, same]
  · simp [WordCode.checkedEval, checked]

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.tabulate_get == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.tabulate_getD == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.tabulate_mem == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.tabulate_cases == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.wordValue_congr == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.Valid.vector == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.check_iff == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.input_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsPinned TrustIr.AYGateCNF.bindWord_bit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.bindWord_outside == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.input_value == [propext, Classical.choice, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.BitwiseOp.gate_output' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.BitwiseOp.gate_output

/-- info: 'TrustIr.AYGateCNF.BitwiseOp.gate_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.BitwiseOp.gate_eval

#trustIrAxiomsExact TrustIr.AYGateCNF.BitwiseOp.eval_bit == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.bitwise_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.bitNot_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.constant_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.bitwise_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.bitNot_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.constant_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.BitwiseOp.target_eval == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.input_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.constant_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.bitwise_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.bitNot_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.append_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.append_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeNot_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeNot_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeBitwise_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeBitwise_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeBitwise_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.composeNot_target == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.append_operand_bounds == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.mask_value == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.checkedEval_eq_some == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.WordCode.appendBool_check == [propext, Quot.sound, Classical.choice]

/-- info: 'TrustIr.AYGateCNF.WordCode.appendBool_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.appendBool_eval

#trustIrAxiomsExact TrustIr.AYGateCNF.Code.appendWord_check == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Code.appendWord_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.wordValue_toNat == [propext, Classical.choice, Quot.sound]
