-- Copyright 2026 Andrew Yates | Apache-2.0
import Lean
/-- Preserve native bindings across the two qualified Lean compiler APIs. -/
macro "trustIrExtern " arity:num pattern:str : attr => do
  let backend := Lean.mkIdent `c
  let binding ← `(attr| extern $backend:ident inline $pattern)
  if Lean.versionString == "4.8.0" then
    return ⟨binding.raw.setArg 1 (Lean.mkNullNode #[arity.raw])⟩
  else if Lean.versionString == "4.30.0-rc2" then return binding
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR native binding"

/-- Preserve T-rounding (toward zero), including negative operands. Both
    pinned definitions have identical four constructor equations. -/
macro "trustIrIntTDiv " left:term:max right:term:max : term => do
  if Lean.versionString == "4.8.0" then `(Int.div $left $right)
  else if Lean.versionString == "4.30.0-rc2" then `(Int.tdiv $left $right)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR truncating division"

macro "trustIrIntTMod " left:term:max right:term:max : term => do
  if Lean.versionString == "4.8.0" then `(Int.mod $left $right)
  else if Lean.versionString == "4.30.0-rc2" then `(Int.tmod $left $right)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR truncating remainder"

/-- Keep the original clauses while avoiding proof-bearing sparse matchers on
    the modern compiler. This changes matcher generation, not proof budgets. -/
macro "trustIrDenseMatch " declaration:command : command => do
  if Lean.versionString == "4.8.0" then pure declaration
  else if Lean.versionString == "4.30.0-rc2" then
    `(command| set_option backward.match.sparseCases false in $declaration)
  else Lean.Macro.throwError "unsupported Lean compiler for constructive matcher selection"

namespace TrustIr.CompilerCompat
universe u v w
trustIrDenseMatch
/-- The complete optional lookup equations, with constructive matcher generation.
    No bounds predicate, panic path, or element is added or omitted. -/
def listGetConstructive {α : Type u} : List α → Nat → Option α
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => listGetConstructive tail index
  | _, _ => none

@[simp] theorem listGetConstructive_nil {α : Type u} (index : Nat) :
    listGetConstructive ([] : List α) index = none := by
  cases index <;> rfl

@[simp] theorem listGetConstructive_cons_zero {α : Type u} (head : α) (tail : List α) :
    listGetConstructive (head :: tail) 0 = some head := rfl

@[simp] theorem listGetConstructive_cons_succ {α : Type u} (head : α) (tail : List α) (index : Nat) :
    listGetConstructive (head :: tail) (index + 1) = listGetConstructive tail index := rfl

/-- Successful lookup witnesses actual list membership. -/
theorem listGetConstructive_mem {α : Type u} {values : List α} {index : Nat} {value : α}
    (found : listGetConstructive values index = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => cases index <;> cases found
  | cons head tail ih =>
    cases index with
    | zero => cases found; exact .head _
    | succ index => exact .tail head (ih found)

/-- Equality at every optional position determines the complete finite list. -/
theorem listGetConstructive_ext {α : Type u} {left right : List α}
    (same : ∀ index, listGetConstructive left index = listGetConstructive right index) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail => have impossible := same 0; cases impossible
  | cons head tail ih =>
    cases right with
    | nil => have impossible := same 0; cases impossible
    | cons other rest =>
      have heads : head = other := Option.some.inj (same 0)
      cases heads
      exact congrArg (List.cons head) (ih (fun index => same (index + 1)))

/-- Mapping preserves every successful result and every out-of-bounds refusal. -/
theorem listGetConstructive_map {α : Type u} {β : Type v} (f : α → β)
    (values : List α) (index : Nat) :
    listGetConstructive (values.map f) index = (listGetConstructive values index).map f := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index

trustIrDenseMatch
/-- Zipping preserves exact positional optional lookup, including unequal lists. -/
theorem listGetConstructive_zipWith {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → γ) (left : List α) (right : List β) (index : Nat) :
    listGetConstructive (List.zipWith f left right) index =
      match listGetConstructive left index, listGetConstructive right index with
      | some a, some b => some (f a b)
      | _, _ => none := by
  induction left generalizing right index with
  | nil => cases right <;> cases index <;> rfl
  | cons head tail ih =>
    cases right with
    | nil =>
      cases index with
      | zero => rfl
      | succ index =>
        change (none : Option γ) = (match listGetConstructive tail index, (none : Option β) with
          | some a, some b => some (f a b)
          | _, _ => none)
        cases listGetConstructive tail index <;> rfl
    | cons other rest =>
      cases index with
      | zero => rfl
      | succ index => exact ih rest index

end TrustIr.CompilerCompat

/-- The original pinned optional lookup implementation, used only by its
    checked whole-function runtime replacement theorem. -/
macro "trustIrListGetRuntime" : term => do
  if Lean.versionString == "4.8.0" then `(@List.get?)
  else if Lean.versionString == "4.30.0-rc2" then `(@List.get?Internal)
  else Lean.Macro.throwError "unsupported Lean compiler for optional lookup runtime"

/-- Preserve canonical lookup; modern lookup uses the same constructive cases. -/
macro "trustIrListGet? " values:term:max index:term:max : term => do
  if Lean.versionString == "4.8.0" then `(List.get? $values $index)
  else if Lean.versionString == "4.30.0-rc2" then
    `(TrustIr.CompilerCompat.listGetConstructive $values ($index : Nat))
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR list access"

/-- Ordered map commutes with optional lookup under each pinned list API. -/
macro "trustIrListGetMap" : term => do
  if Lean.versionString == "4.8.0" then `(List.get?_map)
  else if Lean.versionString == "4.30.0-rc2" then `(TrustIr.CompilerCompat.listGetConstructive_map)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR mapped list lookup"

/-- Preserve optional array access under both pinned compiler APIs. -/
macro "trustIrArrayGet? " values:term:max index:term:max : term => do
  if Lean.versionString == "4.8.0" then `(Array.get? $values $index)
  else if Lean.versionString == "4.30.0-rc2" then `(($values)[($index : Nat)]?)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR array access"

/-- Preserve each compiler's actual append-membership theorem, including
    partial applications in source-admission proofs. -/
macro "trustIrListMemAppendLeft" : term => do
  if Lean.versionString == "4.8.0" then `(List.mem_append_of_mem_left)
  else if Lean.versionString == "4.30.0-rc2" then `(List.mem_append_left)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR list membership"

macro "trustIrListMemAppendRight" : term => do
  if Lean.versionString == "4.8.0" then `(List.mem_append_of_mem_right)
  else if Lean.versionString == "4.30.0-rc2" then `(List.mem_append_right)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR list membership"

/-- Select the actual head-membership theorem as a term, preserving the
    canonical elaborator's inference of the head from the expected list. -/
macro "trustIrListMemConsSelf" : term => do
  if Lean.versionString == "4.8.0" then `(List.mem_cons_self)
  else if Lean.versionString == "4.30.0-rc2" then `(fun value values => @List.Mem.head _ value values)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR head membership"

/-- The two pinned names for recursive list-lookup equations. -/
macro "trustIrListGetConsZero" : term => do
  if Lean.versionString == "4.8.0" then `(List.get?_cons_zero)
  else if Lean.versionString == "4.30.0-rc2" then `(TrustIr.CompilerCompat.listGetConstructive_cons_zero)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR lookup equation"

macro "trustIrListGetConsSucc" : term => do
  if Lean.versionString == "4.8.0" then `(List.get?_cons_succ)
  else if Lean.versionString == "4.30.0-rc2" then `(TrustIr.CompilerCompat.listGetConstructive_cons_succ)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR lookup equation"

/-- The pinned list flattening APIs denote the same ordered flat map. -/
macro "trustIrListBind " values:term:max callback:term : term => do
  if Lean.versionString == "4.8.0" then `(List.bind $values $callback)
  else if Lean.versionString == "4.30.0-rc2" then `(List.flatMap $callback $values)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR list flat map"

/-- The pinned compilers name the hash map differently: `Lean.HashMap` in 4.8,
    `Std.HashMap` in 4.30, which has no `Lean.HashMap`. -/
macro "trustIrHashMap " key:term:max value:term:max : term => do
  if Lean.versionString == "4.8.0" then `(Lean.HashMap $key $value)
  else if Lean.versionString == "4.30.0-rc2" then `(Std.HashMap $key $value)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR hash map"

/-- Optional lookup in that map, by each compiler's own name for it. -/
macro "trustIrHashMapFind? " map:term:max key:term:max : term => do
  if Lean.versionString == "4.8.0" then `(Lean.HashMap.find? $map $key)
  else if Lean.versionString == "4.30.0-rc2" then `(Std.HashMap.get? $map $key)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR hash map lookup"

/-- Preserve the JSON object's ascending-key accumulator fold. The canonical
    RBNode API calls it `fold`; the modern raw tree API calls it `foldl`. -/
macro "trustIrJsonObjectFold " object:term:max callback:term:max initial:term:max : term => do
  if Lean.versionString == "4.8.0" then `(($object).fold $callback $initial)
  else if Lean.versionString == "4.30.0-rc2" then `(($object).foldl $callback $initial)
  else Lean.Macro.throwError "unsupported Lean compiler for ordered JSON object fold"

/-- Both pinned recursors use `Nat.lt_wfRel.wf.fix`; only the public name
    changed. Select the compiler's actual eliminator, without a new axiom. -/
macro "trustIrNatStrongInduction" : term => do
  if Lean.versionString == "4.8.0" then `(Nat.strongInductionOn)
  else if Lean.versionString == "4.30.0-rc2" then `(Nat.strongRecOn)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR natural strong induction"

/-- Select a fully checked proof script before elaboration. This preserves the
    canonical proof's exact axiom footprint without recovering from failures or
    elaborating APIs that the other pinned compiler removed. -/
macro "trustIrCompilerProof " "{" legacy:tacticSeq "}" "{" modern:tacticSeq "}" : tactic => do
  if Lean.versionString == "4.8.0" then `(tactic| first | $legacy:tacticSeq)
  else if Lean.versionString == "4.30.0-rc2" then `(tactic| first | $modern:tacticSeq)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR proof selection"

/-- Kernel-checked reduction for closed executable fixtures. Lean 4.8 admits
    these by reflexivity; Lean 4.30's `cbv` constructs equation-theorem proofs
    for well-founded definitions. This does not invoke native evaluation. -/
macro "trustIrReduce" : tactic => do
  if Lean.versionString == "4.8.0" then `(tactic| rfl)
  else if Lean.versionString == "4.30.0-rc2" then
    -- This tactic's parser is absent in 4.8, so construct its no-location syntax.
    pure ⟨Lean.mkNode `Lean.Parser.Tactic.cbv #[Lean.mkAtom "cbv", Lean.mkNullNode #[]]⟩
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR fixture reduction"


namespace TrustIr.CompilerCompat
universe u

/-- The same optional result at every list and index on the pinned runtime. -/
theorem listGetConstructive_pointwise {α : Type u} (values : List α) (index : Nat) :
    listGetConstructive values index = (trustIrListGetRuntime) (α := α) values index := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index

/-- Whole-function equality preserves the pinned runtime implementation. -/
@[csimp]
theorem listGetConstructive_eq : @listGetConstructive = trustIrListGetRuntime := by
  funext α values index
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head tail ih =>
    cases index with
    | zero => rfl
    | succ index => exact ih index
end TrustIr.CompilerCompat

namespace TrustIr.CompilerCompat

/-- Optional access is preserved by finite list-to-array conversion. -/
theorem getElem?_toArray {α : Type} (values : List α) (index : Nat) :
    values.toArray[index]? = trustIrListGet? values index := by
  trustIrCompilerProof {
    first
    | exact List.getElem?_toArray
    | have representation : values.toArray = Array.mk values :=
        congrArg Array.mk (Array.data_toArray values)
      rw [representation]
      by_cases inside : index < values.length
      · simpa only [getElem?_def, Array.size_mk, inside, dite_true,
          Array.getElem_eq_data_get] using (List.get?_eq_get inside).symm
      · simp [getElem?_def, Array.size_mk, inside, List.get?_len_le (Nat.le_of_not_lt inside)]
  } {
    rw [listGetConstructive_pointwise]
    exact List.getElem?_toArray
  }

/-- The same successful optional lookup, retaining the Fin-indexed witness used
    by source-position proofs on the canonical compiler. -/
theorem listGet?_eq_some {α : Type} {values : List α} {index : Nat} {value : α} :
    trustIrListGet? values index = some value ↔
      ∃ inside : index < values.length, values.get ⟨index, inside⟩ = value := by
  trustIrCompilerProof {
    exact List.get?_eq_some
  } {
    rw [listGetConstructive_pointwise]
    exact List.getElem?_eq_some_iff
  }

theorem listGet?_outside {α : Type} (values : List α) (index : Nat)
    (outside : values.length ≤ index) : trustIrListGet? values index = none := by
  trustIrCompilerProof {
    exact List.get?_len_le outside
  } {
    induction values generalizing index with
    | nil => cases index <;> rfl
    | cons head tail ih =>
      cases index with
      | zero => cases outside
      | succ index => exact ih index (Nat.le_of_succ_le_succ outside)
  }

/-- Preserve the same Fin-indexed witness of a successful in-bounds lookup. -/
theorem listGet?_eq_get {α : Type} {values : List α} {index : Nat}
    (inside : index < values.length) :
    trustIrListGet? values index = some (values.get ⟨index, inside⟩) := by
  trustIrCompilerProof {
    exact List.get?_eq_get inside
  } {
    induction values generalizing index with
    | nil => exact False.elim (Nat.not_lt_zero index inside)
    | cons head tail ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih (Nat.lt_of_succ_lt_succ inside)
  }

end TrustIr.CompilerCompat

macro "trustIrCollectAxioms " name:term : term => do
  if Lean.versionString == "4.8.0" then
    `(do
      let env ← Lean.getEnv
      let (_, state) := ((Lean.Elab.Command.CollectAxioms.collect $name).run env).run {}
      pure state.axioms)
  else if Lean.versionString == "4.30.0-rc2" then `(Lean.collectAxioms $name)
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR axiom audit"

/-- Check actual transitive axiom dependencies, independent of printer ordering.
    Each allowed set is explicit; in particular, `sorryAx` is never implicit. -/
elab "#trustIrAxioms " subject:ident " <= " "[" allowed:ident,* "]" : command => do
  let names ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstWithInfos subject
  let permitted := allowed.getElems.map (·.getId)
  for name in names do
    let actual ← trustIrCollectAxioms name
    for axiomName in actual do
      unless permitted.contains axiomName do
        Lean.throwError m!"unexpected axiom {axiomName} in {name}"
    Lean.logInfo m!"TrustIR axiom audit: {name}: {actual.toList}"

/-- Require the exact transitive axiom set, independent of printer ordering.
    Unlike the subset audit, this also refuses a missing expected dependency. -/
elab "#trustIrAxiomsExact " subject:ident " == " "[" expected:ident,* "]" : command => do
  let names ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstWithInfos subject
  let required := expected.getElems.map (·.getId)
  for name in names do
    let actual ← trustIrCollectAxioms name
    for axiomName in actual do
      unless required.contains axiomName do
        Lean.throwError m!"unexpected axiom {axiomName} in {name}"
    for axiomName in required do
      unless actual.contains axiomName do
        Lean.throwError m!"missing expected axiom {axiomName} in {name}"
    Lean.logInfo m!"TrustIR exact axiom audit: {name}: {actual.toList}"

/-- Both compiler footprints are exact. The modern footprint must be a subset
    of the canonical one, so a compiler port cannot widen the axiom ceiling. -/
elab "#trustIrAxiomsPinned " subject:ident " == " "[" legacy:ident,* "]"
    " modern " "[" modern:ident,* "]" : command => do
  let canonical := legacy.getElems.map (·.getId)
  let newer := modern.getElems.map (·.getId)
  for axiomName in newer do
    unless canonical.contains axiomName do
      Lean.throwError m!"modern axiom ceiling widens canonical set: {axiomName}"
  let required ← if Lean.versionString == "4.8.0" then pure canonical
    else if Lean.versionString == "4.30.0-rc2" then pure newer
    else Lean.throwError "unsupported Lean compiler for pinned axiom audit"
  let names ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstWithInfos subject
  for name in names do
    let actual ← trustIrCollectAxioms name
    for axiomName in actual do
      unless required.contains axiomName do
        Lean.throwError m!"unexpected axiom {axiomName} in {name}"
    for axiomName in required do
      unless actual.contains axiomName do
        Lean.throwError m!"missing expected axiom {axiomName} in {name}"
    Lean.logInfo m!"TrustIR pinned exact axiom audit: {name}: {actual.toList}"

#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive == []
#trustIrAxioms TrustIr.CompilerCompat.listGetConstructive_eq <= [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_map == []

#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_zipWith == []
#trustIrAxiomsExact TrustIr.CompilerCompat.getElem?_toArray == [propext]
#trustIrAxiomsExact TrustIr.CompilerCompat.listGet?_eq_some == [propext]
#trustIrAxiomsExact TrustIr.CompilerCompat.listGet?_outside == []
#trustIrAxiomsExact TrustIr.CompilerCompat.listGet?_eq_get == []

#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_nil == []
#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_cons_zero == []
#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_cons_succ == []

#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_mem == []
#trustIrAxiomsExact TrustIr.CompilerCompat.listGetConstructive_ext == []
