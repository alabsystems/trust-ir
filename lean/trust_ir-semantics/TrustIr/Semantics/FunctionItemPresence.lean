-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Basic
import TrustIr.Semantics.NatIndexTree
import TrustIr.StringAppend

namespace TrustIr.FunctionItemPresence

/-- One original function row supplies both its static header and its local
    frame declarations. Header errors contain no executable state. Failed
    body decoding retains `none`, distinct from a real empty declaration list. -/
structure FunctionDecl where
  id : FuncId
  header : Except String FunctionItemHeader
  frames : Option (List BindingFrameDef)

/-- Actual finite value-type declarations. A failed decode retains its source
    position as `none`; it is not removed or replaced with a declaration.
    Function signatures and pointer pointees are not value-containment edges.
    This carrier grants neither header validity nor value/layout admission. -/
structure Source where
  types : List (Option Ty) := []
  structs : List StructDef := []
  enums : List EnumDef := []
  records : List (RecordId × Option RecordDef) := []
  closures : List ClosureTy := []
  /-- Every original function row, including failed bodies. Duplicate IDs and
      duplicate local frame IDs remain distinguishable and cannot authenticate. -/
  functions : List FunctionDecl := []

private def numbered {α : Type} (rows : List α) : List (α × Nat) :=
  rows.zip (List.range rows.length)

/-- Exactly `Module::{struct_def,enum_def,record_def}`: a matching row at
    the ID's own position takes precedence, otherwise the first matching ID.
    No dense allocation up to the largest sparse nominal ID is performed. -/
private def positions {α : Type} (rows : List α) (id : α → Nat) : NatIndexTree Nat :=
  let entries := numbered rows
  let first : NatIndexTree Nat :=
    entries.foldr (fun (row, position) out => out.insert (id row) position) .empty
  entries.foldl (fun out (row, position) =>
    if id row == position then out.insert position position else out) first

private structure Index where
  types : Array (Option Ty)
  structs : Array StructDef
  enums : Array EnumDef
  records : Array (RecordId × Option RecordDef)
  closures : Array ClosureTy
  structPositions : NatIndexTree Nat
  enumPositions : NatIndexTree Nat
  recordPositions : NatIndexTree Nat
  /-- An occupied `none` records ambiguity, including malformed duplicates. -/
  functions : NatIndexTree (Option FunctionDecl)

private def functionIndex (rows : List FunctionDecl) : NatIndexTree (Option FunctionDecl) :=
  rows.foldl (fun out row =>
    out.insert row.id.index (if (out.find row.id.index).isSome then none else some row)) .empty

private def Index.ofSource (source : Source) : Index :=
  { types := source.types.toArray
    structs := source.structs.toArray
    enums := source.enums.toArray
    records := source.records.toArray
    closures := source.closures.toArray
    structPositions := positions source.structs (·.id.index)
    enumPositions := positions source.enums (·.id.index)
    recordPositions := positions source.records (·.fst.index)
    functions := functionIndex source.functions }

private def Index.structBase (index : Index) : Nat := index.types.size
private def Index.enumBase (index : Index) : Nat := index.structBase + index.structs.size
private def Index.recordBase (index : Index) : Nat := index.enumBase + index.enums.size
private def Index.closureBase (index : Index) : Nat := index.recordBase + index.records.size
private def Index.count (index : Index) : Nat := index.closureBase + index.closures.size

private def Index.ty (index : Index) (id : TyId) : Option Ty :=
  (trustIrArrayGet? index.types id.index).join

private def Index.structDef (index : Index) (id : StructId) : Option StructDef :=
  (index.structPositions.find id.index).bind (fun position => trustIrArrayGet? index.structs position)

private def Index.enumDef (index : Index) (id : EnumId) : Option EnumDef :=
  (index.enumPositions.find id.index).bind (fun position => trustIrArrayGet? index.enums position)

private def Index.recordDef (index : Index) (id : RecordId) : Option RecordDef :=
  ((index.recordPositions.find id.index).bind (fun position => trustIrArrayGet? index.records position)).bind (·.snd)

private def Index.closureTy (index : Index) (id : ClosureTyId) : Option ClosureTy :=
  trustIrArrayGet? index.closures id.index

private def functionItemAmbiguityMessage (id : FuncId) : String :=
  StringCompat.append (StringCompat.append "FnItem: function " (toString id.index))
    " has ambiguous declarations"

private theorem functionItemAmbiguityMessage_eq_standard (id : FuncId) :
    functionItemAmbiguityMessage id = s!"FnItem: function {id.index} has ambiguous declarations" := by
  unfold functionItemAmbiguityMessage
  trustIrCompilerProof { rfl } {
    rw [StringCompat.append_eq_standard, StringCompat.append_eq_standard]
    rfl
  }

#trustIrAxiomsExact functionItemAmbiguityMessage == []
trustIrString48 #trustIrAxiomsExact functionItemAmbiguityMessage_eq_standard == []
trustIrString430 #trustIrAxiomsExact functionItemAmbiguityMessage_eq_standard == [propext]

private def Index.functionItem (index : Index) (id : FuncId) :
    Option (Except String FunctionItemHeader) :=
  match index.functions.find id.index with
  | none => none
  | some none => some (.error (functionItemAmbiguityMessage id))
  | some (some row) => some row.header

/-- The exact original lookup, including ambiguity and malformed-header
errors, is unchanged for every finite index and function identifier. -/
private theorem Index.functionItem_eq_standard (index : Index) (id : FuncId) :
    index.functionItem id =
      match index.functions.find id.index with
      | none => none
      | some none => some (.error s!"FnItem: function {id.index} has ambiguous declarations")
      | some (some row) => some row.header := by
  unfold Index.functionItem
  cases index.functions.find id.index with
  | none => rfl
  | some row =>
    cases row with
    | none =>
      exact congrArg (fun message => some (Except.error message))
        (functionItemAmbiguityMessage_eq_standard id)
    | some declaration => rfl

private def Index.bindingFrame (index : Index) (function : FuncId) (frame : BindingFrameId) :
    Option BindingFrameDef :=
  match index.functions.find function.index with
  | some (some row) => row.frames.bind (fun declarations =>
    match declarations.filter (fun declaration => declaration.id == frame) with
    | [declaration] => some declaration
    | _ => none)
  | _ => none

/-- Unique original function and function-local frame declaration. All raw
    rows count before inspecting header/body success; duplicates never grant
    authority. No declaration is recovered from the runtime payload. -/
def Source.bindingFrame (source : Source) (function : FuncId) (frame : BindingFrameId) :
    Option BindingFrameDef := (Index.ofSource source).bindingFrame function frame

def Source.functionItem (source : Source) (id : FuncId) :
    Option (Except String FunctionItemHeader) := (Index.ofSource source).functionItem id

/-- A positive presence rule: an immediate item or a reachable source node.
    Unlike uninhabitedness, every value-bearing field is an OR alternative. -/
structure Rule where
  direct : Bool := false
  children : List Nat := []

def Rule.holds (rule : Rule) (facts : NatIndexTree Unit) : Bool :=
  rule.direct || rule.children.any (fun key => (facts.find key).isSome)

private theorem any_mono (rows : List Nat) (p q : Nat → Bool)
    (implication : ∀ key, p key = true → q key = true)
    (present : rows.any p = true) : rows.any q = true := by
  induction rows with
  | nil => cases present
  | cons first rest ih =>
    simp only [List.any, Bool.or_eq_true] at present ⊢
    rcases present with firstTrue | restTrue
    · exact Or.inl (implication first firstTrue)
    · exact Or.inr (ih restTrue)

/-- Adding source facts can only enable a positive rule; there is no
    negative edge or cycle-as-proof condition in the closure. -/
theorem Rule.holds_mono (rule : Rule) (earlier later : NatIndexTree Unit)
    (grows : ∀ key, (earlier.find key).isSome = true → (later.find key).isSome = true)
    (present : rule.holds earlier = true) : rule.holds later = true := by
  simp only [Rule.holds, Bool.or_eq_true] at present ⊢
  rcases present with direct | reachable
  · exact Or.inl direct
  · exact Or.inr (any_mono rule.children _ _ grows reachable)

private def combine (rules : List Rule) : Rule :=
  { direct := rules.any (·.direct), children := trustIrListBind rules (·.children) }

private def reference (position : Option Nat) (base : Nat := 0) : Rule :=
  { children := position.toList.map (base + ·) }

private theorem syntax_size_step (left right : Nat) : right < 1 + left + right := by
  have first : right < 1 + right := (Nat.add_comm right 1) ▸ Nat.lt_succ_self right
  exact Nat.lt_of_lt_of_le first (Nat.add_le_add_right (Nat.le_add_right 1 left) right)

private theorem syntax_list_size (types : List Ty) : Ty._sizeOf_2 types = sizeOf types := by
  induction types with
  | nil => rfl
  | cons first rest ih =>
    change 1 + sizeOf first + Ty._sizeOf_2 rest = 1 + sizeOf first + sizeOf rest
    exact congrArg (fun count => 1 + sizeOf first + count) ih

trustIrDenseMatch
mutual
  private def typeRule (index : Index) : Ty → Rule
    | .FnItem _ => { direct := true }
    | .Tuple fields => combine (typeRules index fields)
    | .Vector count element => typeRule index element
    | .Array element _ | .Sequence element | .Set element _ | .Refine element _ =>
      -- Array count zero still follows its element, as Rust's predicate does.
      reference (if (index.ty element).isSome then some element.index else none)
    | .Struct id => reference (index.structPositions.find id.index) index.structBase
    | .Enum id => reference (index.enumPositions.find id.index) index.enumBase
    | .Record id => reference (index.recordPositions.find id.index) index.recordBase
    | .Closure id => reference
        (if (index.closureTy id).isSome then some id.index else none) index.closureBase
    -- In particular: Ref/RefMut/PtrConst/PtrMut/Rc, FatPtr, and Func do not
    -- follow pointees, metadata declarations or function signatures.
    | _ => {}
  termination_by ty => sizeOf ty
  decreasing_by
    · change sizeOf fields < 1 + Ty._sizeOf_2 fields
      rw [syntax_list_size fields]
      exact syntax_size_step 0 (sizeOf fields)
    · change sizeOf element < 1 + sizeOf count + sizeOf element
      exact syntax_size_step (sizeOf count) (sizeOf element)
  private def typeRules (index : Index) : List Ty → List Rule
    | [] => []
    | first :: rest => typeRule index first :: typeRules index rest
  termination_by types => sizeOf types
  decreasing_by
    · change sizeOf first < 1 + sizeOf first + sizeOf rest
      exact Nat.lt_add_right (sizeOf rest) (syntax_size_step 0 (sizeOf first))
    · change sizeOf rest < 1 + sizeOf first + sizeOf rest
      exact syntax_size_step (sizeOf first) (sizeOf rest)
end

private def equations (index : Index) : NatIndexTree Rule :=
  let out : NatIndexTree Rule := (numbered index.types.toList).foldl (fun out (ty, position) =>
    out.insert position (match ty with | some ty => typeRule index ty | none => {})) .empty
  let out := (numbered index.structs.toList).foldl (fun out (definition, position) =>
    out.insert (index.structBase + position)
      (combine (typeRules index (definition.fields.map (·.ty))))) out
  let out := (numbered index.enums.toList).foldl (fun out (definition, position) =>
    out.insert (index.enumBase + position)
      (combine (typeRules index (trustIrListBind definition.variants (·.fields))))) out
  let out := (numbered index.records.toList).foldl (fun out ((_, definition), position) =>
    out.insert (index.recordBase + position) (match definition with
      | some definition => combine (typeRules index (definition.fields.map (·.ty)))
      | none => {})) out
  (numbered index.closures.toList).foldl (fun out (definition, position) =>
    out.insert (index.closureBase + position)
      (combine (typeRules index definition.captures))) out

private theorem find_valid (test : Nat → Bool) (rows : List Nat) (key : Nat)
    (found : rows.find? test = some key) : key ∈ rows ∧ test key = true := by
  induction rows with
  | nil => cases found
  | cons first rest ih =>
    cases yes : test first with
    | false =>
      rw [List.find?,yes] at found
      obtain ⟨member, result⟩ := ih found
      exact ⟨List.Mem.tail first member, result⟩
    | true =>
      rw [List.find?,yes] at found
      cases found
      exact ⟨trustIrListMemConsSelf _ rest, yes⟩

private def choose (test : Nat → Bool) (rows : List Nat) :
    Option { key : Nat // key ∈ rows ∧ test key = true } :=
  match found : rows.find? test with
  | none => none
  | some key => some ⟨key, find_valid test rows key found⟩

private theorem natural_beq_refl : ∀ value : Nat, (value == value) = true
  | 0 => rfl
  | value + 1 => by
      trustIrCompilerProof {
        exact natural_beq_refl value
      } {
        change decide (value + 1 = value + 1) = true
        exact decide_eq_true rfl
      }

private theorem natural_beq_false (first second : Nat) (different : first ≠ second) :
    (first == second) = false := by
  cases comparison : first == second with
  | false => rfl
  | true =>
      have equal : first = second := by
        trustIrCompilerProof {
          exact Nat.eq_of_beq_eq_true comparison
        } {
          change decide (first = second) = true at comparison
          exact of_decide_eq_true comparison
        }
      exact False.elim (different equal)

private theorem erase_length_lt (rows : List Nat) (key : Nat) (present : key ∈ rows) :
    (rows.erase key).length < rows.length := by
  induction rows with
  | nil => cases present
  | cons head tail ih =>
    by_cases equal : head = key
    · subst head
      rw [List.erase,natural_beq_refl]
      exact Nat.lt_succ_self tail.length
    · have rest : key ∈ tail := by
        cases present with
        | head => exact False.elim (equal rfl)
        | tail _ member => exact member
      rw [List.erase,natural_beq_false head key equal]
      exact Nat.succ_lt_succ (ih rest)

/-- The actual finite source domain is consumed, not execution/value fuel.
    Rules only add positive facts. A cycle without an item proves nothing;
    a path from a cycle to a real item eventually derives every predecessor. -/
private def close (rules : NatIndexTree Rule) (remaining : List Nat)
    (facts : NatIndexTree Unit) : NatIndexTree Unit :=
  match choose (fun key => (rules.find key).any (·.holds facts)) remaining with
  | none => facts
  | some selected => close rules (remaining.erase selected.val) (facts.insert selected.val ())
termination_by remaining.length
decreasing_by exact erase_length_lt remaining selected.val selected.property.1

private structure Compiled where
  index : Index
  facts : NatIndexTree Unit

private def compile (source : Source) : Compiled :=
  let index := Index.ofSource source
  { index, facts := close (equations index) (List.range index.count) .empty }

/-- A prepared finite carrier. The cached data is definitionally tied to its
    actual source; even a manually constructed carrier must prove that tie.
    It cannot supply an unrelated favorable/always-false presence predicate. -/
structure Prepared where
  source : Source
  private compiled : Compiled
  private faithful : compiled = compile source

def prepare (source : Source) : Prepared :=
  { source, compiled := compile source, faithful := rfl }

def Source.ty (source : Source) (id : TyId) : Option Ty :=
  (Index.ofSource source).ty id

/-- Cached positional type lookup is the original finite raw-list lookup. -/
theorem Source.ty_eq_list (source : Source) (id : TyId) :
    source.ty id = (trustIrListGet? source.types id.index).join := by
  exact congrArg Option.join (CompilerCompat.getElem?_toArray source.types id.index)

def Source.structDef (source : Source) (id : StructId) : Option StructDef :=
  (Index.ofSource source).structDef id

def Source.enumDef (source : Source) (id : EnumId) : Option EnumDef :=
  (Index.ofSource source).enumDef id

def Source.recordDef (source : Source) (id : RecordId) : Option RecordDef :=
  (Index.ofSource source).recordDef id

def Source.closureTy (source : Source) (id : ClosureTyId) : Option ClosureTy :=
  (Index.ofSource source).closureTy id

def Prepared.bindingFrame (prepared : Prepared) (function : FuncId) (frame : BindingFrameId) :
    Option BindingFrameDef := prepared.compiled.index.bindingFrame function frame

def Prepared.functionItem (prepared : Prepared) (id : FuncId) :
    Option (Except String FunctionItemHeader) := prepared.compiled.index.functionItem id

#trustIrAxiomsExact Prepared.functionItem == []

theorem Prepared.bindingFrame_eq_source (prepared : Prepared) (function : FuncId) (frame : BindingFrameId) :
    prepared.bindingFrame function frame = prepared.source.bindingFrame function frame := by
  unfold Prepared.bindingFrame Source.bindingFrame
  rw [prepared.faithful]
  rfl

theorem Prepared.functionItem_eq_source (prepared : Prepared) (id : FuncId) :
    prepared.functionItem id = prepared.source.functionItem id := by
  unfold Prepared.functionItem Source.functionItem
  rw [prepared.faithful]
  rfl

def Prepared.ty (prepared : Prepared) (id : TyId) : Option Ty :=
  prepared.compiled.index.ty id

def Prepared.structDef (prepared : Prepared) (id : StructId) : Option StructDef :=
  prepared.compiled.index.structDef id

def Prepared.enumDef (prepared : Prepared) (id : EnumId) : Option EnumDef :=
  prepared.compiled.index.enumDef id

def Prepared.recordDef (prepared : Prepared) (id : RecordId) : Option RecordDef :=
  prepared.compiled.index.recordDef id

/-- Execution reads the first matching raw row. Canonical shape/presence
selection above remains separate; both selectors read this same finite source. -/
def Prepared.firstStructDef (prepared : Prepared) (id : StructId) : Option StructDef :=
  prepared.source.structs.find? (fun row => row.id == id)

def Prepared.firstEnumDef (prepared : Prepared) (id : EnumId) : Option EnumDef :=
  prepared.source.enums.find? (fun row => row.id == id)

/-- The first outer-key match remains authoritative even if its decode failed. -/
def Prepared.firstRecordDef (prepared : Prepared) (id : RecordId) : Option RecordDef :=
  ((prepared.source.records.find? (fun row => row.fst == id)).map (·.snd)).join

def Prepared.closureTy (prepared : Prepared) (id : ClosureTyId) : Option ClosureTy :=
  prepared.compiled.index.closureTy id

theorem Prepared.ty_eq_source (prepared : Prepared) (id : TyId) :
    prepared.ty id = prepared.source.ty id := by
  unfold Prepared.ty Source.ty
  rw [prepared.faithful]
  rfl

theorem Prepared.structDef_eq_source (prepared : Prepared) (id : StructId) :
    prepared.structDef id = prepared.source.structDef id := by
  unfold Prepared.structDef Source.structDef
  rw [prepared.faithful]
  rfl

theorem Prepared.enumDef_eq_source (prepared : Prepared) (id : EnumId) :
    prepared.enumDef id = prepared.source.enumDef id := by
  unfold Prepared.enumDef Source.enumDef
  rw [prepared.faithful]
  rfl

theorem Prepared.recordDef_eq_source (prepared : Prepared) (id : RecordId) :
    prepared.recordDef id = prepared.source.recordDef id := by
  unfold Prepared.recordDef Source.recordDef
  rw [prepared.faithful]
  rfl

theorem Prepared.closureTy_eq_source (prepared : Prepared) (id : ClosureTyId) :
    prepared.closureTy id = prepared.source.closureTy id := by
  unfold Prepared.closureTy Source.closureTy
  rw [prepared.faithful]
  rfl

/-- A complete value-containment query against one prepared module graph.
    Inline syntax recurses structurally; nominal cycles were already solved. -/
def Prepared.hasFnItem (prepared : Prepared) (ty : Ty) : Bool :=
  (typeRule prepared.compiled.index ty).holds prepared.compiled.facts

/-- Source-only specification of the prepared presence query. -/
def Source.hasFnItem (source : Source) (ty : Ty) : Bool :=
  let compiled := compile source
  (typeRule compiled.index ty).holds compiled.facts

theorem Prepared.hasFnItem_eq_source (prepared : Prepared) (ty : Ty) :
    prepared.hasFnItem ty = prepared.source.hasFnItem ty := by
  unfold Prepared.hasFnItem Source.hasFnItem
  rw [prepared.faithful]

theorem prepare_hasFnItem (source : Source) (ty : Ty) :
    (prepare source).hasFnItem ty = source.hasFnItem ty := rfl

/-- Presence of the item constructor never authenticates its ID. That is a
    separate actual-header/signature check at the value/layout boundary. -/
theorem Prepared.hasFnItem_item (prepared : Prepared) (id : FuncId) :
    prepared.hasFnItem (.FnItem id) = true := by
  unfold Prepared.hasFnItem
  trustIrCompilerProof {
    conv => lhs; delta typeRule typeRule._mutual; rw [WellFounded.fix_eq]
    rfl
  } {
    conv => lhs; delta typeRule typeRule._mutual WellFounded.Nat.fix
    simp only [WellFounded.Nat.eager_eq]
    rfl
  }

theorem Prepared.hasFnItem_pointer (prepared : Prepared) (pointee : Ty) :
    prepared.hasFnItem (.PtrConst pointee) = false := by
  unfold Prepared.hasFnItem
  trustIrCompilerProof {
    conv => lhs; delta typeRule typeRule._mutual; rw [WellFounded.fix_eq]
    rfl
  } {
    conv => lhs; delta typeRule typeRule._mutual WellFounded.Nat.fix
    simp only [WellFounded.Nat.eager_eq]
    rfl
  }

theorem Prepared.hasFnItem_signature (prepared : Prepared) (signature : FuncTyId) :
    prepared.hasFnItem (.Func signature) = false := by
  unfold Prepared.hasFnItem
  trustIrCompilerProof {
    conv => lhs; delta typeRule typeRule._mutual; rw [WellFounded.fix_eq]
    rfl
  } {
    conv => lhs; delta typeRule typeRule._mutual WellFounded.Nat.fix
    simp only [WellFounded.Nat.eager_eq]
    rfl
  }

-- Kernel controls exercise the actual source -> finite fixed point -> query.
-- Their counts are source positions, not an arbitrary recursion allowance.
/-- An unsigned scalar has no nominal function-item lanes, independently of
all other declarations in the original prepared module. -/
theorem Prepared.hasFnItem_u64 (prepared : Prepared) :
    prepared.hasFnItem .U64 = false := by
  unfold Prepared.hasFnItem
  trustIrCompilerProof {
    conv => lhs; delta typeRule typeRule._mutual; rw [WellFounded.fix_eq]
    rfl
  } {
    conv => lhs; delta typeRule typeRule._mutual WellFounded.Nat.fix
    simp only [WellFounded.Nat.eager_eq]
    rfl
  }

#trustIrAxiomsExact TrustIr.FunctionItemPresence.Prepared.hasFnItem_u64 == []

example : (prepare { types := [some (.FnItem ⟨7⟩)] }).hasFnItem (.Array ⟨0⟩ 0) = true := by
  trustIrReduce

example : (prepare { types := [some (.Array ⟨0⟩ 0)] }).hasFnItem (.Array ⟨0⟩ 9) = false := by
  trustIrReduce

example : (prepare { types := [some (.Tuple [.Array ⟨0⟩ 0, .FnItem ⟨7⟩])] }).hasFnItem
    (.Array ⟨0⟩ 0) = true := by
  trustIrReduce

example : (prepare { closures := [{ func := ⟨0⟩, captures := [.FnItem ⟨7⟩] }] }).hasFnItem
    (.Closure ⟨0⟩) = true := by
  trustIrReduce

example : (prepare { structs :=
    [{ id := ⟨1⟩, name := "first", fields :=
        [{ name := "held", ty := .FnItem ⟨7⟩, offset := none }], size := none, align := none },
     { id := ⟨1⟩, name := "matching-position", fields := [], size := none, align := none }] }).hasFnItem
    (.Struct ⟨1⟩) = false := by
  trustIrReduce

example : (prepare { records :=
    [(⟨0⟩, none), (⟨0⟩, some { id := ⟨0⟩, name := "later", fields :=
      [{ name := "held", ty := .FnItem ⟨7⟩, offset := none }] })] }).hasFnItem
    (.Record ⟨0⟩) = false := by
  trustIrReduce

end TrustIr.FunctionItemPresence
