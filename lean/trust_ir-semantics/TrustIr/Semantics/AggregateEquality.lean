-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.AggregatePlans

namespace TrustIr.AggregateMemory
open SourceLayout

private def discriminantIndex : List Int → Int → Option Nat
  | [], _ => none
  | first :: rest, value =>
    if first == value then some 0 else (discriminantIndex rest value).map Nat.succ

private def variantOf (info : Enumeration) : Value → Option Nat
  | .int width raw =>
    if width == tagBits info.tag then
      discriminantIndex info.discriminants
        (if tagSigned info.tag then toSigned raw width else truncateUnsigned raw width)
    else none
  | _ => none

private def equalFieldsWith (eq : Plan → Value → Value → Except SemError Bool)
    (fields : List (Nat × Plan)) (left right : List Value) : Except SemError Bool := do
  match fields, left, right with
  | [], [], [] => pure true
  | (_, plan) :: fields, left :: rest, right :: later =>
    if ← eq plan left right then equalFieldsWith eq fields rest later else pure false
  | _, _, _ => pure false

private def equalRepeatedWith (eq : Value → Value → Except SemError Bool)
    (left right : List Value) : Except SemError Bool := do
  match left, right with
  | [], [] => pure true
  | left :: rest, right :: later =>
    if ← eq left right then equalRepeatedWith eq rest later else pure false
  | _, _ => pure false

/-- Depth counts nested values, not logical array repetitions or storage edges.
    The public entry derives it from the actual operands, never a policy cap. -/
private def equalAt (fuel : Nat) (model : ByteModel) (plan : Plan)
    (left right : Value) : Except SemError Bool := do
  match fuel with
  | 0 => .error (.typeError "memory equality: value nesting exhausted")
  | fuel + 1 =>
    match left, right with
    | .int wa a, .int wb b => pure (wa == wb && truncateUnsigned a wa == truncateUnsigned b wb)
    | .bool a, .bool b => pure (a == b)
    | .float a, .float b =>
      if plan.ty.isFloat then
        let a ← floatToBitsAt plan.ty a
        let b ← floatToBitsAt plan.ty b
        pure (a == b)
      else pure false
    | .nullPtr, .nullPtr => pure true
    | .nullPtr, .ptr b provenance => pure (b == 0 && provenance.isNone)
    | .ptr a provenance, .nullPtr => pure (a == 0 && provenance.isNone)
    | .ptr a p, .ptr b q => pure (a == b && p == q)
    | .fnDef a f, .fnDef b g => pure (a == b && f == g)
    | .fnItem f, .fnItem g => pure (f == g && closureTyEq plan.ty (.FnItem f))
    | .fatPtr a p metadata, .fatPtr b q expected =>
      if a != b || p != q then pure false
      else
        let ty := match plan.ty with | .FatPtr kind => kind.metadataTyAtModel model | _ => Ty.Ptr
        equalAt fuel model (.leaf ty { size := model.pointerBytes, alignment := model.pointerBytes }) metadata expected
    | .uninit, .uninit => pure true
    | .partial a, .partial b => pure (a == b)
    | .array values, .array expected =>
      match plan with
      | .array _ _ count element =>
        if values.size != count || expected.size != count then pure false
        else if h : values.size = expected.size then
          values.tree.eqByM (equalAt fuel model element) (h.symm ▸ expected.tree)
        else pure false
      | _ => pure false
    | .aggregate values, .aggregate expected =>
      match plan with
      | .fields _ _ fields => equalFieldsWith (equalAt fuel model) fields values expected
      | .enumeration _ _ info variants =>
        match values, expected with
        | .int width raw :: values, .int expectedWidth expectedRaw :: expected =>
          if width != expectedWidth || truncateUnsigned raw width != truncateUnsigned expectedRaw expectedWidth then
            pure false
          else
            match variantOf info (.int width raw) with
            | none => pure false
            | some index =>
              match (trustIrListGet? variants index) with
              | some (some fields) => equalFieldsWith (equalAt fuel model) fields values expected
              | some none => .error (.typeError "memory image: uninhabited enum variant")
              | none => pure false
        | _, _ => pure false
      | .leaf .Unit _ => pure (values.isEmpty && expected.isEmpty)
      | _ => pure false
    | .vector values, .vector expected =>
      match plan.ty with
      | .Vector _ element =>
        let size := (vectorScalarByteSize element).getD 1
        equalRepeatedWith (equalAt fuel model (.leaf element { size, alignment := size })) values expected
      | _ => pure false
    | _, _ => pure false

/-- Typed equality preserves pointer provenance, function identity and actual
    float lane encoding. Compact arrays compare stored shapes without expanding
    uniform extents. The existing NaN payload refusal remains explicit. -/
def equal (model : ByteModel) (plan : Plan) (left right : Value) : Except SemError Bool :=
  equalAt (max left.depth right.depth + 1) model plan left right

private theorem ordered_errors (error : SemError → Prop) (check : Nat → Except SemError Bool)
    (safe : ∀ index, ByteImage.BlockResult (fun _ => True) error (check index)) (start count : Nat) :
    ByteImage.BlockResult (fun _ => True) error (CompactArray.OrderedComparison.run check start count) := by
  induction count generalizing start with
  | zero => exact True.intro
  | succ count ih =>
    rw [CompactArray.OrderedComparison.run_succ]
    have held := safe start
    cases checked : check start with
    | error failure => simpa [checked,CompactArray.OrderedComparison.andThen] using held
    | ok answer => cases answer <;> first | exact True.intro | exact ih _

private theorem array_equal_errors (error : SemError → Prop) (eq : Value → Value → Except SemError Bool)
    (safe : ∀ left right, ByteImage.BlockResult (fun _ => True) error (eq left right))
    {size : Nat} (left right : CompactArray.Tree Value size) :
    ByteImage.BlockResult (fun _ => True) error (left.eqByM eq right) := by
  rw [CompactArray.Tree.eqByM_eq_ordered]
  unfold CompactArray.Tree.eqByMOrderedSpec
  apply ordered_errors error
  intro index
  split
  · exact safe _ _
  · exact True.intro

private theorem fields_equal_errors (error : SemError → Prop) (eq : Plan → Value → Value → Except SemError Bool)
    (safe : ∀ plan left right, ByteImage.BlockResult (fun _ => True) error (eq plan left right))
    (fields : List (Nat × Plan)) (left right : List Value) :
    ByteImage.BlockResult (fun _ => True) error (equalFieldsWith eq fields left right) := by
  induction fields generalizing left right with
  | nil => cases left <;> cases right <;> rw [equalFieldsWith] <;> first | exact True.intro | simp
  | cons pair rest ih =>
    obtain ⟨offset,plan⟩ := pair
    cases left <;> cases right <;> rw [equalFieldsWith]
    all_goals repeat' first
      | (solve | exact True.intro)
      | (solve | simp)
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _ (safe _ _ _) ?_; intro answer _)
      | (solve | exact ih _ _)
      | split
      | (dsimp only; split)

private theorem repeated_equal_errors (error : SemError → Prop) (eq : Value → Value → Except SemError Bool)
    (safe : ∀ left right, ByteImage.BlockResult (fun _ => True) error (eq left right)) (left right : List Value) :
    ByteImage.BlockResult (fun _ => True) error (equalRepeatedWith eq left right) := by
  induction left generalizing right with
  | nil => cases right <;> rw [equalRepeatedWith] <;> first | exact True.intro | simp
  | cons first rest ih =>
    cases right <;> rw [equalRepeatedWith]
    all_goals repeat' first
      | (solve | exact True.intro)
      | (solve | simp)
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _ (safe _ _) ?_; intro answer _)
      | (solve | exact ih _)
      | split
      | (dsimp only; split)

private theorem equal_at_errors (error : SemError → Prop) (typeErrors : ∀ message, error (.typeError message))
    (floats : ∀ ty value, ByteImage.BlockResult (fun _ => True) error (floatToBitsAt ty value))
    (fuel : Nat) (model : ByteModel) (plan : Plan) (left right : Value) :
    ByteImage.BlockResult (fun _ => True) error (equalAt fuel model plan left right) := by
  induction fuel generalizing plan left right with
  | zero => exact typeErrors _
  | succ fuel ih =>
    trustIrCompilerProof { rw [equalAt] } { unfold equalAt }
    repeat' first
      | (solve | exact True.intro)
      | (solve | exact typeErrors _)
      | (solve | exact ih _ _ _)
      | (solve | exact fields_equal_errors error _ (fun _ _ _ => ih _ _ _) _ _ _)
      | (solve | exact repeated_equal_errors error _ (fun _ _ => ih _ _ _) _ _)
      | (solve | exact array_equal_errors error _ (fun _ _ => ih _ _ _) _ _)
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _ (floats _ _) ?_; intro bits _)
      | split
      | (dsimp only; split)

/-- Original typed equality propagates only actual float-codec errors and
its explicit nesting/variant refusals, for every value and compact shape. -/
theorem equal_errors (error : SemError → Prop) (typeErrors : ∀ message, error (.typeError message))
    (floats : ∀ ty value, ByteImage.BlockResult (fun _ => True) error (floatToBitsAt ty value))
    (model : ByteModel) (plan : Plan) (left right : Value) :
    ByteImage.BlockResult (fun _ => True) error (equal model plan left right) :=
  equal_at_errors error typeErrors floats _ model plan left right

end TrustIr.AggregateMemory
