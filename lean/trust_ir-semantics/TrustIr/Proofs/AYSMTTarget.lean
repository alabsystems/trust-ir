-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBridge
import TrustIr.StringUnicode
import TrustIr.BitVecBounds
import Init.Data.BitVec.Basic

namespace TrustIr.TrustIrExpr

-- The local logical implementation has the same bytes as standard append,
-- while its UTF-8 validity witness preserves the grammar's zero-axiom budget.
local instance : Append String where
  append := TrustIr.StringCompat.append

inductive SMTSort where
  | bv : Nat → SMTSort
  | bool : SMTSort
  deriving DecidableEq, Repr

/-- The native core carrier of each actually admitted SMT sort. -/
abbrev SMTSort.CoreValue : SMTSort → Type
  | .bool => Bool
  | .bv bits => BitVec bits

/-- Decode the model's numeric carrier to its core value. -/
def SMTSort.toCore : (sort : SMTSort) → Int → sort.CoreValue
  | .bool, value => value != 0
  | .bv bits, value => BitVec.ofInt bits value

/-- Observe a core value in the model's exact numeric carrier. -/
def SMTSort.fromCore : (sort : SMTSort) → sort.CoreValue → Int
  | .bool, value => if value then 1 else 0
  | .bv _, value => Int.ofNat value.toNat

/-- Equality uses actual core Bool or BitVec equality at its common sort. -/
def SMTSort.coreEq : (sort : SMTSort) → sort.CoreValue → sort.CoreValue → Bool
  | .bool, left, right => left == right
  | .bv _, left, right => decide (left = right)

inductive SMTUnary : SMTSort → SMTSort → Type where
  | bvNeg (bits : Nat) : SMTUnary (.bv bits) (.bv bits)
  | bvNot (bits : Nat) : SMTUnary (.bv bits) (.bv bits)
  | boolNot : SMTUnary .bool .bool
  | bvZeroExtend (bits extra : Nat) : SMTUnary (.bv bits) (.bv (bits + extra))
  | bvSignExtend (bits extra : Nat) : SMTUnary (.bv bits) (.bv (bits + extra))
  | bvExtract (bits hi lo : Nat) (ordered : lo ≤ hi) (bounded : hi < bits) :
      SMTUnary (.bv bits) (.bv (hi - lo + 1))

def SMTUnary.name {input output : SMTSort} : SMTUnary input output → String
  | .bvNeg _ => "bvneg"
  | .bvNot _ => "bvnot"
  | .boolNot => "not"
  | .bvZeroExtend _ extra => "(_ zero_extend " ++ toString extra ++ ")"
  | .bvSignExtend _ extra => "(_ sign_extend " ++ toString extra ++ ")"
  | .bvExtract _ hi lo _ _ => "(_ extract " ++ toString hi ++ " " ++ toString lo ++ ")"

instance {input output : SMTSort} : Repr (SMTUnary input output) where
  reprPrec op _ := repr op.name

section
trustIrBitVec430 local instance {n : Nat} : Complement (BitVec n) := ⟨TrustIr.BitVecCompat.bitNot⟩

def SMTUnary.eval {input output : SMTSort} : SMTUnary input output → input.CoreValue → output.CoreValue
  | .bvNeg _, value => -value
  | .bvNot _, value => ~~~value
  | .boolNot, value => !value
  | .bvZeroExtend bits extra, value => value.zeroExtend (bits + extra)
  | .bvSignExtend bits extra, value => value.signExtend (bits + extra)
  | .bvExtract _ hi lo _ _, value => value.extractLsb hi lo

end

/-- Every unary constructor still computes the complete standard core operation. -/
theorem SMTUnary.eval_eq_standard : @SMTUnary.eval =
    fun {input output} (op : SMTUnary input output) value =>
      match op, value with
      | .bvNeg _, value => -value
      | .bvNot _, value => BitVec.not value
      | .boolNot, value => !value
      | .bvZeroExtend bits extra, value => value.zeroExtend (bits + extra)
      | .bvSignExtend bits extra, value => value.signExtend (bits + extra)
      | .bvExtract _ hi lo _ _, value => value.extractLsb hi lo := rfl
trustIrBitVec48 #trustIrAxiomsExact SMTUnary.eval_eq_standard == [propext]
trustIrBitVec430 #trustIrAxiomsExact SMTUnary.eval_eq_standard == [propext, Quot.sound]

inductive SMTBinary : SMTSort → SMTSort → Type where
  | bvAdd (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvSub (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvMul (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvUDiv (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvSDiv (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvURem (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvSRem (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvAnd (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvOr (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvXor (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvShl (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvLShr (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | bvAShr (bits : Nat) : SMTBinary (.bv bits) (.bv bits)
  | boolAnd : SMTBinary .bool .bool
  | boolOr : SMTBinary .bool .bool
  | boolImpl : SMTBinary .bool .bool
  | bvUlt (bits : Nat) : SMTBinary (.bv bits) .bool
  | bvUle (bits : Nat) : SMTBinary (.bv bits) .bool
  | bvSlt (bits : Nat) : SMTBinary (.bv bits) .bool
  | bvSle (bits : Nat) : SMTBinary (.bv bits) .bool
  | eq (sort : SMTSort) : SMTBinary sort .bool
  | distinct (sort : SMTSort) : SMTBinary sort .bool
  deriving Repr

def SMTBinary.name {input output : SMTSort} : SMTBinary input output → String
  | .bvAdd _ => "bvadd"
  | .bvSub _ => "bvsub"
  | .bvMul _ => "bvmul"
  | .bvUDiv _ => "bvudiv"
  | .bvSDiv _ => "bvsdiv"
  | .bvURem _ => "bvurem"
  | .bvSRem _ => "bvsrem"
  | .bvAnd _ => "bvand"
  | .bvOr _ => "bvor"
  | .bvXor _ => "bvxor"
  | .bvShl _ => "bvshl"
  | .bvLShr _ => "bvlshr"
  | .bvAShr _ => "bvashr"
  | .boolAnd => "and"
  | .boolOr => "or"
  | .boolImpl => "=>"
  | .bvUlt _ => "bvult"
  | .bvUle _ => "bvule"
  | .bvSlt _ => "bvslt"
  | .bvSle _ => "bvsle"
  | .eq _ => "="
  | .distinct _ => "distinct"

/-- Avoid constructing an enormous intermediate before word truncation. -/
def SMTBinary.shiftLeft {bits : Nat} (word amount : BitVec bits) : BitVec bits :=
  if amount.toNat < bits then word <<< amount else 0

def SMTBinary.eval {input output : SMTSort} : SMTBinary input output → input.CoreValue → input.CoreValue → output.CoreValue
  | .bvAdd _, left, right => left + right
  | .bvSub _, left, right => left - right
  | .bvMul _, left, right => left * right
  | .bvUDiv _, left, right => BitVec.smtUDiv left right
  | .bvSDiv _, left, right => BitVec.smtSDiv left right
  | .bvURem _, left, right => BitVec.umod left right
  | .bvSRem _, left, right => BitVec.srem left right
  | .bvAnd _, left, right => left &&& right
  | .bvOr _, left, right => left ||| right
  | .bvXor _, left, right => left ^^^ right
  | .bvShl _, left, right => SMTBinary.shiftLeft left right
  | .bvLShr _, left, right => left >>> right
  | .bvAShr _, left, right => BitVec.sshiftRight left right.toNat
  | .boolAnd, left, right => left && right
  | .boolOr, left, right => left || right
  | .boolImpl, left, right => !left || right
  | .bvUlt _, left, right => left.ult right
  | .bvUle _, left, right => left.ule right
  | .bvSlt _, left, right => left.slt right
  | .bvSle _, left, right => left.sle right
  | .eq sort, left, right => sort.coreEq left right
  | .distinct sort, left, right => !(sort.coreEq left right)

/-- Typed target syntax used by the actual request producer. -/
inductive SMTTerm : SMTSort → Type where
  | bvConst (bits : Nat) (value : Int) : SMTTerm (.bv bits)
  | boolConst (value : Bool) : SMTTerm .bool
  | var (bits : Nat) (symbol : String) : SMTTerm (.bv bits)
  | boolVar (symbol : String) : SMTTerm .bool
  | unary {input output : SMTSort} (op : SMTUnary input output) (arg : SMTTerm input) : SMTTerm output
  | binary {input output : SMTSort} (op : SMTBinary input output)
      (left right : SMTTerm input) : SMTTerm output
  | ite {sort : SMTSort} (cond : SMTTerm .bool) (yes no : SMTTerm sort) : SMTTerm sort
  | concat {highWidth lowWidth : Nat} (high : SMTTerm (.bv highWidth)) (low : SMTTerm (.bv lowWidth)) :
      SMTTerm (.bv (highWidth + lowWidth))

def SMTTerm.numeral (width : Nat) (value : Int) : String :=
  "(_ bv" ++ toString (value % (2 : Int) ^ width).toNat ++ " " ++ toString width ++ ")"

def SMTTerm.toText : {sort : SMTSort} → SMTTerm sort → String
  | _, .bvConst bits value => numeral bits value
  | _, .boolConst value => if value then "true" else "false"
  | _, .var _ symbol => symbol
  | _, .boolVar symbol => symbol
  | _, .unary op arg => "(" ++ op.name ++ " " ++ arg.toText ++ ")"
  | _, .binary op left right => "(" ++ op.name ++ " " ++ left.toText ++ " " ++ right.toText ++ ")"
  | _, .ite cond yes no => "(ite " ++ cond.toText ++ " " ++ yes.toText ++ " " ++ no.toText ++ ")"
  | _, .concat high low => "(concat " ++ high.toText ++ " " ++ low.toText ++ ")"

instance {sort : SMTSort} : Repr (SMTTerm sort) where
  reprPrec term _ := repr term.toText

/-- Semantics uses only native core Bool and BitVec operations. -/
def SMTTerm.eval (env : SMTEnv) : {sort : SMTSort} → SMTTerm sort → sort.CoreValue
  | _, .bvConst bits value => BitVec.ofInt bits value
  | _, .boolConst value => value
  | _, .var bits symbol => BitVec.ofInt bits (env symbol)
  | _, .boolVar symbol => SMTSort.toCore .bool (env symbol)
  | _, .unary op arg => op.eval (arg.eval env)
  | _, .binary op left right => op.eval (left.eval env) (right.eval env)
  | _, .ite cond yes no => if cond.eval env then yes.eval env else no.eval env
  | _, .concat high low => high.eval env ++ low.eval env

/-- The dynamic rotation expands to the actual QF_BV primitive vocabulary. -/
def SMTTerm.rotate (left : Bool) (bits : Nat) (word amount : SMTTerm (.bv bits)) : SMTTerm (.bv bits) :=
  let width := SMTTerm.bvConst bits (Int.ofNat bits)
  let shift := SMTTerm.binary (.bvURem bits) amount width
  let other := SMTTerm.binary (.bvSub bits) width shift
  let first := if left then SMTTerm.binary (.bvShl bits) word shift else SMTTerm.binary (.bvLShr bits) word shift
  let second := if left then SMTTerm.binary (.bvLShr bits) word other else SMTTerm.binary (.bvShl bits) word other
  SMTTerm.binary (.bvOr bits) first second

/-- An admitted word root asserts nonzero; a Bool root is already an assertion. -/
def SMTTerm.asFormula : {sort : SMTSort} → SMTTerm sort → SMTTerm .bool
  | .bool, term => term
  | .bv bits, term => .binary (.distinct (.bv bits)) term (.bvConst bits 0)

/-- Fixed SMT-LIB operator tokens, independent of the executable printer. -/
inductive SMTUnary.Spelling : {input output : SMTSort} → SMTUnary input output → String → Prop where
  | bvNeg (bits : Nat) : SMTUnary.Spelling (.bvNeg bits) "bvneg"
  | bvNot (bits : Nat) : SMTUnary.Spelling (.bvNot bits) "bvnot"
  | boolNot : SMTUnary.Spelling (.boolNot) "not"
  | bvZeroExtend (bits extra : Nat) : SMTUnary.Spelling (.bvZeroExtend bits extra)
      ("(_ zero_extend " ++ toString extra ++ ")")
  | bvSignExtend (bits extra : Nat) : SMTUnary.Spelling (.bvSignExtend bits extra)
      ("(_ sign_extend " ++ toString extra ++ ")")
  | bvExtract (bits hi lo : Nat) (ordered : lo ≤ hi) (bounded : hi < bits) :
      SMTUnary.Spelling (.bvExtract bits hi lo ordered bounded)
        ("(_ extract " ++ toString hi ++ " " ++ toString lo ++ ")")

theorem SMTUnary.name_spelling {input output : SMTSort} (op : SMTUnary input output) :
    SMTUnary.Spelling op op.name := by
  cases op <;> constructor

/-- Fixed SMT-LIB operator tokens, independent of the executable printer. -/
inductive SMTBinary.Spelling : {input output : SMTSort} → SMTBinary input output → String → Prop where
  | bvAdd (bits : Nat) : SMTBinary.Spelling (.bvAdd bits) "bvadd"
  | bvSub (bits : Nat) : SMTBinary.Spelling (.bvSub bits) "bvsub"
  | bvMul (bits : Nat) : SMTBinary.Spelling (.bvMul bits) "bvmul"
  | bvUDiv (bits : Nat) : SMTBinary.Spelling (.bvUDiv bits) "bvudiv"
  | bvSDiv (bits : Nat) : SMTBinary.Spelling (.bvSDiv bits) "bvsdiv"
  | bvURem (bits : Nat) : SMTBinary.Spelling (.bvURem bits) "bvurem"
  | bvSRem (bits : Nat) : SMTBinary.Spelling (.bvSRem bits) "bvsrem"
  | bvAnd (bits : Nat) : SMTBinary.Spelling (.bvAnd bits) "bvand"
  | bvOr (bits : Nat) : SMTBinary.Spelling (.bvOr bits) "bvor"
  | bvXor (bits : Nat) : SMTBinary.Spelling (.bvXor bits) "bvxor"
  | bvShl (bits : Nat) : SMTBinary.Spelling (.bvShl bits) "bvshl"
  | bvLShr (bits : Nat) : SMTBinary.Spelling (.bvLShr bits) "bvlshr"
  | bvAShr (bits : Nat) : SMTBinary.Spelling (.bvAShr bits) "bvashr"
  | boolAnd : SMTBinary.Spelling (.boolAnd) "and"
  | boolOr : SMTBinary.Spelling (.boolOr) "or"
  | boolImpl : SMTBinary.Spelling (.boolImpl) "=>"
  | bvUlt (bits : Nat) : SMTBinary.Spelling (.bvUlt bits) "bvult"
  | bvUle (bits : Nat) : SMTBinary.Spelling (.bvUle bits) "bvule"
  | bvSlt (bits : Nat) : SMTBinary.Spelling (.bvSlt bits) "bvslt"
  | bvSle (bits : Nat) : SMTBinary.Spelling (.bvSle bits) "bvsle"
  | eq (sort : SMTSort) : SMTBinary.Spelling (.eq sort) "="
  | distinct (sort : SMTSort) : SMTBinary.Spelling (.distinct sort) "distinct"

theorem SMTBinary.name_spelling {input output : SMTSort} (op : SMTBinary input output) :
    SMTBinary.Spelling op op.name := by
  cases op <;> constructor

/-- Mathematical value of a fixed list of literal digits, not an SMT parser. -/
def SMTTerm.literalValue (radix : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun value digit => value * radix + digit) 0

def SMTTerm.literalDigits (digits : List Nat) : String :=
  String.join (digits.map (fun digit => toString (Nat.digitChar digit)))

/-- A structural derivation in the emitted typed SMT-LIB term grammar.
It fixes literal syntax, keyword spelling, operand order and conditional arity. -/
inductive SMTTerm.Prints : {sort : SMTSort} → SMTTerm sort → String → Prop where
  | bvConst (bits : Nat) (value : Int) :
      Prints (.bvConst bits value)
        ("(_ bv" ++ toString (value % (2 : Int) ^ bits).toNat ++ " " ++ toString bits ++ ")")
  | bvHex (bits : Nat) (value : Int) (digits : List Nat)
      (positive : 0 < bits) (width : digits.length * 4 = bits)
      (range : ∀ digit ∈ digits, digit < 16)
      (residue : literalValue 16 digits = (value % (2 : Int) ^ bits).toNat) :
      Prints (.bvConst bits value) ("#x" ++ literalDigits digits)
  | bvBinary (bits : Nat) (value : Int) (digits : List Nat)
      (positive : 0 < bits) (width : digits.length = bits)
      (range : ∀ digit ∈ digits, digit < 2)
      (residue : literalValue 2 digits = (value % (2 : Int) ^ bits).toNat) :
      Prints (.bvConst bits value) ("#b" ++ literalDigits digits)
  | boolConst (value : Bool) : Prints (.boolConst value) (if value then "true" else "false")
  | var (bits : Nat) (symbol : String) : Prints (.var bits symbol) symbol
  | boolVar (symbol : String) : Prints (.boolVar symbol) symbol
  | unary {input output : SMTSort} {op : SMTUnary input output} {arg : SMTTerm input}
      {name text : String} (spelling : SMTUnary.Spelling op name) (argument : Prints arg text) :
      Prints (.unary op arg) ("(" ++ name ++ " " ++ text ++ ")")
  | binary {input output : SMTSort} {op : SMTBinary input output} {left right : SMTTerm input}
      {name lhs rhs : String} (spelling : SMTBinary.Spelling op name)
      (leftText : Prints left lhs) (rightText : Prints right rhs) :
      Prints (.binary op left right) ("(" ++ name ++ " " ++ lhs ++ " " ++ rhs ++ ")")
  | ite {sort : SMTSort} {cond : SMTTerm .bool} {yes no : SMTTerm sort} {c t e : String}
      (condition : Prints cond c) (thenText : Prints yes t) (elseText : Prints no e) :
      Prints (.ite cond yes no) ("(ite " ++ c ++ " " ++ t ++ " " ++ e ++ ")")
  | concat {highWidth lowWidth : Nat} {high : SMTTerm (.bv highWidth)} {low : SMTTerm (.bv lowWidth)}
      {highText lowText : String} (highPrinted : Prints high highText) (lowPrinted : Prints low lowText) :
      Prints (.concat high low) ("(concat " ++ highText ++ " " ++ lowText ++ ")")

theorem SMTTerm.toText_prints {sort : SMTSort} (term : SMTTerm sort) : term.Prints term.toText := by
  induction term with
  | bvConst bits value => exact .bvConst bits value
  | boolConst value => exact .boolConst value
  | var bits symbol => exact .var bits symbol
  | boolVar symbol => exact .boolVar symbol
  | unary op arg ih => exact .unary op.name_spelling ih
  | binary op left right leftIH rightIH => exact .binary op.name_spelling leftIH rightIH
  | ite cond yes no condIH yesIH noIH => exact .ite condIH yesIH noIH
  | concat high low highIH lowIH => exact .concat highIH lowIH

/-- Encoded variable tokens occupy the non-reserved v_ identifier alphabet. -/
def SMTTerm.Identifier (symbol : String) : Prop :=
  ∃ payload : List Char, StringCompat.toList symbol = ['v', '_'] ++ payload ∧
    ∀ c ∈ payload, c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57)

/-- The complete identifier predicate still uses the standard character sequence. -/
theorem SMTTerm.Identifier_function_eq_standard : SMTTerm.Identifier =
    fun symbol => ∃ payload : List Char, symbol.data = ['v', '_'] ++ payload ∧
      ∀ c ∈ payload, c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by
  trustIrCompilerProof { rfl } {
    funext symbol
    unfold SMTTerm.Identifier
    rw [StringCompat.toList_eq_standard]
    rfl
  }
#trustIrAxiomsExact SMTTerm.Identifier == []
trustIrString48 #trustIrAxiomsExact SMTTerm.Identifier_function_eq_standard == []
trustIrString430 #trustIrAxiomsExact SMTTerm.Identifier_function_eq_standard == [propext, Classical.choice, Quot.sound]

/-- A deliberately bounded raw simple-symbol vocabulary. These names are
printed unchanged, never alpha-renamed or treated as formula syntax. Reserved
lexical/theory tokens and every quoting/escape/control character refuse. -/
def SMTTerm.checkNativeIdentifier (symbol : String) : Bool :=
  let letter := fun c : Char => decide ((65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
    (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c = '_')
  let tail := fun c : Char => letter c || decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ c = '$')
  let reserved := ["BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING", "_",
    "as", "let", "exists", "forall", "match", "par", "true", "false", "Bool",
    "assert", "check-sat", "declare-fun", "not", "and", "or", "xor", "ite", "distinct",
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv", "bvurem", "bvsrem",
    "bvand", "bvor", "bvxor", "bvnot", "bvneg", "bvshl", "bvlshr", "bvashr",
    "bvult", "bvule", "bvslt", "bvsle", "concat"]
  match StringCompat.toList symbol with
  | [] => false
  | first :: rest => letter first && rest.all tail && !(reserved.contains symbol)

def SMTTerm.VariableIdentifier (symbol : String) : Prop :=
  SMTTerm.Identifier symbol ∨ SMTTerm.checkNativeIdentifier symbol = true

/-- Positive bitvector widths and lexically safe variable identifiers. -/
def SMTTerm.WellFormed {sort : SMTSort} (term : SMTTerm sort) : Prop :=
  SMTTerm.rec (motive := fun _ _ => Prop)
    (fun bits _ => 0 < bits)
    (fun _ => True)
    (fun bits symbol => 0 < bits ∧ VariableIdentifier symbol)
    (fun symbol => VariableIdentifier symbol)
    (fun _ _ arg => arg)
    (fun _ _ _ left right => left ∧ right)
    (fun _ _ _ cond yes no => cond ∧ yes ∧ no)
    (fun _ _ high low => high ∧ low) term

/-- Every original well-formedness clause is retained for every typed term. -/
theorem SMTTerm.WellFormed_eq_standard {sort : SMTSort} (term : SMTTerm sort) :
    term.WellFormed =
      SMTTerm.rec (motive := fun _ _ => Prop)
        (fun bits _ => 0 < bits)
        (fun _ => True)
        (fun bits symbol => 0 < bits ∧ ((∃ payload : List Char,
          symbol.data = ['v', '_'] ++ payload ∧
          ∀ c ∈ payload, c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57)) ∨
          SMTTerm.checkNativeIdentifier symbol = true))
        (fun symbol => (∃ payload : List Char,
          symbol.data = ['v', '_'] ++ payload ∧
          ∀ c ∈ payload, c = '_' ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57)) ∨
          SMTTerm.checkNativeIdentifier symbol = true)
        (fun _ _ arg => arg)
        (fun _ _ _ left right => left ∧ right)
        (fun _ _ _ cond yes no => cond ∧ yes ∧ no)
        (fun _ _ high low => high ∧ low) term := by
  unfold SMTTerm.WellFormed SMTTerm.VariableIdentifier
  rw [SMTTerm.Identifier_function_eq_standard]
trustIrString48 #trustIrAxiomsExact SMTTerm.WellFormed_eq_standard == []
trustIrString430 #trustIrAxiomsExact SMTTerm.WellFormed_eq_standard == [propext, Classical.choice, Quot.sound]

/-- info: 'TrustIr.TrustIrExpr.SMTUnary.name_spelling' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTUnary.name_spelling

/-- info: 'TrustIr.TrustIrExpr.SMTBinary.name_spelling' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTBinary.name_spelling

/-- info: 'TrustIr.TrustIrExpr.SMTTerm.toText_prints' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.toText_prints

#trustIrAxioms TrustIr.TrustIrExpr.SMTTerm.Prints <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTTerm.checkNativeIdentifier <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTTerm.literalValue <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.TrustIrExpr.SMTTerm.literalDigits <= [propext, Classical.choice, Quot.sound]
