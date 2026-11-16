-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.AggregateImages
import TrustIr.State.ByteImageTraversal

namespace TrustIr.AggregateMemory
open SourceLayout

private def imageError {α : Type} (message : String) : Except SemError α := .error (.typeError message)
private def imageUB {α : Type} (message : String) : Except SemError α := .error (.ub message)

private def initialized (image : ByteImage) : Except SemError (List UInt8) :=
  match image.toList.mapM id with
  | some bytes => .ok bytes
  | none => imageUB "Load: reading uninitialized covered memory"

def firstMissing (image : ByteImage) : Option Nat := image.firstWhere Option.isNone

/-- A reported initialization hole is inside the actual image and absent at
    that address. This uses the logical traversal law, without assuming a
    cached answer or inspecting bytes outside the visible image. -/
theorem firstMissing_sound (image : ByteImage) (hit : Nat)
    (found : firstMissing image = some hit) :
    hit < image.size ∧ image.get hit = none := by
  obtain ⟨inside, missing⟩ := image.firstWhere_sound Option.isNone hit found
  refine ⟨inside, ?_⟩
  cases value : image.get hit with
  | none => rfl
  | some byte => simp [value] at missing

#trustIrAxiomsExact firstMissing_sound == [Classical.choice, propext, Quot.sound]

/-- Absence of an initialization hole is exactly initialization of every
    visible byte. Unused bytes retained by views/templates are not premises. -/
theorem firstMissing_eq_none_iff (image : ByteImage) :
    firstMissing image = none ↔
      ∀ index, index < image.size → image.get index ≠ none := by
  unfold firstMissing
  rw [ByteImage.firstWhere_eq_none_iff]
  constructor
  · intro checked index inside missing
    have rejected := checked index inside
    simp [missing] at rejected
  · intro initialized index inside
    cases value : image.get index with
    | none => exact False.elim (initialized index inside value)
    | some byte => rfl

#trustIrAxiomsExact firstMissing_eq_none_iff == [propext, Quot.sound, Classical.choice]

/-- The reported hole is exactly the first absent visible byte. -/
theorem firstMissing_eq_some_iff (image : ByteImage) (hit : Nat) :
    firstMissing image = some hit ↔
      hit < image.size ∧ image.get hit = none ∧
        ∀ index, index < hit → image.get index ≠ none := by
  unfold firstMissing
  rw [ByteImage.firstWhere_eq_some_iff]
  constructor
  · rintro ⟨inside, missing, prior⟩
    refine ⟨inside, ?_, ?_⟩
    · cases value : image.get hit with
      | none => rfl
      | some byte => simp [value] at missing
    · intro index earlier absent
      have rejected := prior index earlier
      simp [absent] at rejected
  · rintro ⟨inside, missing, prior⟩
    refine ⟨inside, by simp [missing], ?_⟩
    intro index earlier
    cases value : image.get index with
    | none => exact False.elim (prior index earlier value)
    | some byte => rfl

#trustIrAxiomsExact firstMissing_eq_some_iff == [propext, Quot.sound, Classical.choice]

private def minimum (first second : Option Nat) : Option Nat :=
  match first, second with
  | none, second => second
  | first, none => first
  | some a, some b => some (min a b)

private def tagLane (info : Enumeration) : Option (Nat × Nat) :=
  match info.encoding with
  | .untagged | .singleInhabited _ => none
  | .direct offset | .directWithUninhabited offset _ => some (offset, tagBits info.tag / 8)
  | .niche _ _ _ _ offset repr => some (offset, tagBits repr / 8)

private def selectVariant (info : Enumeration) (image : ByteImage) : Except SemError Nat := do
  let index ← match info.encoding with
    | .untagged => pure 0
    | .singleInhabited selected => pure selected
    | .direct offset | .directWithUninhabited offset _ =>
      let bytes ← initialized (image.slice offset (tagBits info.tag / 8))
      let raw := Int.ofNat (decodeIntBytes bytes)
      let discriminant := if tagSigned info.tag then toSigned raw (tagBits info.tag) else raw
      match discriminantIndex info.discriminants discriminant with
      | some index => pure index
      | none => imageUB "Load: enum tag does not name a variant"
    | .niche untagged start stop first offset repr =>
      let bytes ← initialized (image.slice offset (tagBits repr / 8))
      let raw := decodeIntBytes bytes
      let modulus := 2 ^ tagBits repr
      let relative := (raw + modulus - first) % modulus
      if relative ≤ stop - start then
        let index := start + relative
        if index == untagged then imageUB "Load: niche names its untagged variant"
        else pure index
      else pure untagged
  if ((trustIrListGet? info.uninhabited index)).getD false then imageUB "Load: uninhabited enum variant"
  else if index ≥ info.discriminants.length then imageError "Load: enum variant is out of range"
  else pure index

private theorem initialized_errors (error : SemError → Prop)
    (undefined : ∀ message, error (.ub message)) (image : ByteImage) :
    ByteImage.BlockResult (fun _ => True) error (initialized image) := by
  unfold initialized
  cases image.toList.mapM id with
  | none => exact undefined _
  | some bytes => exact True.intro

private theorem selectVariant_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
    (info : Enumeration) (image : ByteImage) :
    ByteImage.BlockResult (fun _ => True) error (selectVariant info image) := by
  unfold selectVariant
  repeat' first
    | exact True.intro
    | exact typeErrors _
    | exact undefined _
    | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _ (initialized_errors error undefined _) ?_; intro bytes _)
    | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _ ?_ ?_ <;> dsimp only)
    | (intro value _)
    | split
    | (dsimp only; split)

mutual
  /-- Inspect exactly live covered bytes. Padding is never initialized or
      decoded speculatively. Enum selection reads its actual physical tag. -/
  def covered (plan : Plan) (image : ByteImage) : Except SemError (Option Nat) := do
    if image.size != plan.layout.size then
      return ← imageError "Load: image size does not match source layout"
    match plan with
    | .leaf _ _ => pure (firstMissing image)
    | .fnItem _ _ => pure (firstMissing image)
    | .fields _ _ fields => coveredFields fields image
    | .array _ _ count element =>
      if count == 0 || element.layout.size == 0 then pure none
      else
        -- Evaluate the full ordered map before choosing a missing byte: a
        -- later invalid enum tag still takes precedence over an earlier hole.
        image.checkBlocks (covered element) element.layout.size count
    | .enumeration _ _ info variants =>
      match tagLane info with
      | some (offset, size) =>
        if let some missing := firstMissing (image.slice offset size) then
          return some (offset + missing)
      | none => pure ()
      let index ← selectVariant info image
      coveredVariant variants index image
  termination_by sizeOf plan
  private def coveredFields (fields : List (Nat × Plan)) (image : ByteImage) :
      Except SemError (Option Nat) := do
    match fields with
    | [] => pure none
    | (offset, child) :: rest =>
      let first ← covered child (image.slice offset child.layout.size)
      let later ← coveredFields rest image
      pure (minimum (first.map (offset + ·)) later)
  termination_by sizeOf fields
  private def coveredVariant (variants : List (Option (List (Nat × Plan)))) (index : Nat)
      (image : ByteImage) : Except SemError (Option Nat) :=
    match variants, index with
    | [], _ => imageError "Load: missing enum variant layout"
    | none :: _, 0 => imageUB "Load: uninhabited enum variant"
    | some first :: _, 0 => coveredFields first image
    | _ :: rest, index + 1 => coveredVariant rest index image
  termination_by sizeOf variants
end

mutual
  /-- Covered-byte traversal can report its original type/initialization
  refusals, but introduces no other error, for arbitrary producer plans. -/
  theorem covered_errors (error : SemError → Prop)
      (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
      (plan : Plan) (image : ByteImage) :
      ByteImage.BlockResult (fun _ => True) error (covered plan image) := by
    cases plan with
    | leaf ty layout =>
      rw [covered]
      repeat' first | exact True.intro | exact typeErrors _ | split | (dsimp only; split)
    | fnItem target layout =>
      rw [covered]
      repeat' first | exact True.intro | exact typeErrors _ | split | (dsimp only; split)
    | fields ty layout fields =>
      rw [covered]
      repeat' first
        | exact typeErrors _
        | exact covered_fields_errors error typeErrors undefined fields image
        | (simp only [pure_bind])
        | split
        | (dsimp only; split)
    | array ty layout count element =>
      rw [covered]
      repeat' first
        | exact True.intro
        | exact typeErrors _
        | exact ByteImage.checkBlocks_errors error (covered element)
            (fun part => covered_errors error typeErrors undefined element part) image element.layout.size count
        | (simp only [pure_bind])
        | split
        | (dsimp only; split)
    | enumeration ty layout info variants =>
      rw [covered]
      repeat' first
        | exact True.intro
        | exact typeErrors _
        | exact covered_variant_errors error typeErrors undefined variants _ image
        | (simp only [pure_bind])
        | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
            (selectVariant_errors error typeErrors undefined info image) ?_; intro index _)
        | split
        | (dsimp only; split)
  termination_by sizeOf plan

  theorem covered_fields_errors (error : SemError → Prop)
      (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
      (fields : List (Nat × Plan)) (image : ByteImage) :
      ByteImage.BlockResult (fun _ => True) error (coveredFields fields image) := by
    cases fields with
    | nil => trustIrCompilerProof { exact True.intro } { rw [coveredFields]; exact True.intro }
    | cons pair rest =>
      obtain ⟨offset,child⟩ := pair
      rw [coveredFields]
      apply ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
        (covered_errors error typeErrors undefined child _)
      intro first _
      apply ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
        (covered_fields_errors error typeErrors undefined rest image)
      intro _ _
      exact True.intro
  termination_by sizeOf fields

  theorem covered_variant_errors (error : SemError → Prop)
      (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
      (variants : List (Option (List (Nat × Plan)))) (index : Nat) (image : ByteImage) :
      ByteImage.BlockResult (fun _ => True) error (coveredVariant variants index image) := by
    cases variants with
    | nil => trustIrCompilerProof { exact typeErrors _ } { rw [coveredVariant]; exact typeErrors _ }
    | cons first rest =>
      cases index with
      | zero =>
        cases first with
        | none => rw [coveredVariant]; exact undefined _
        | some fields => rw [coveredVariant]; exact covered_fields_errors error typeErrors undefined fields image
      | succ index => rw [coveredVariant]; exact covered_variant_errors error typeErrors undefined rest index image
  termination_by sizeOf variants
end

mutual
  private def decodeCore (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
      (plan : Plan) (image : ByteImage) (topChar allowUnwritten : Bool) :
      Except SemError Value := do
    if image.size != plan.layout.size then
      return ← imageError "Load: image size does not match source layout"
    match plan with
    | .fnItem target layout =>
      if layout.size != 0 || layout.alignment != 1 then
        imageError "Load: function item layout is not zero-sized/alignment-one"
      else pure (.fnItem target)
    | .leaf ty _ =>
      let bytes ← initialized image
      match ty with
      | .Char =>
        if topChar then decodeMemoryWithFunctions model order memory ty bytes
        else pure (.int 32 (Int.ofNat (decodeIntBytes bytes)))
      | _ => decodeMemoryWithFunctions model order memory ty bytes
    | .fields _ _ fields =>
      pure (.aggregate (← decodeFields model order memory fields image allowUnwritten))
    | .array _ _ count element =>
      if count == 0 then return .array (CompactArray.Packed.ofArray #[])
      if element.layout.size == 0 then
        let value ← decodeCore model order memory element ByteImage.empty false false
        return .array (CompactArray.Packed.uniform count value)
      let values ← image.mapBlocks
        (fun part => decodeCore model order memory element part false false)
        element.layout.size count
      pure (.array ⟨count, values⟩)
    | .enumeration _ _ info variants =>
      let index ← selectVariant info image
      let discriminant ← match (trustIrListGet? info.discriminants index) with
        | some value => pure value
        | none => imageError "Load: enum has no logical discriminant"
      let fields ← decodeVariant model order memory variants index image
      pure (.aggregate (Value.intAt (tagBits info.tag) discriminant :: fields))
  termination_by sizeOf plan
  private def decodeFields (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
      (fields : List (Nat × Plan)) (image : ByteImage) (allowUnwritten : Bool) :
      Except SemError (List Value) := do
    match fields with
    | [] => pure []
    | (offset, child) :: rest =>
      let part := image.slice offset child.layout.size
      let value ←
        if allowUnwritten && child.layout.size > 0 && (part.firstWhere Option.isSome).isNone then pure Value.uninit
        else if allowUnwritten then
          match ← covered child part with
          | none => decodeCore model order memory child part false false
          | some _ =>
            match child with
            | .fields ty layout children => decodeCore model order memory (.fields ty layout children) part false true
            | _ => imageUB "Load: partially written aggregate lane"
        else decodeCore model order memory child part false false
      let later ← decodeFields model order memory rest image allowUnwritten
      pure (value :: later)
  termination_by sizeOf fields
  private def decodeVariant (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
      (variants : List (Option (List (Nat × Plan)))) (index : Nat) (image : ByteImage) :
      Except SemError (List Value) :=
    match variants, index with
    | [], _ => imageError "Load: missing enum variant layout"
    | none :: _, 0 => imageUB "Load: uninhabited enum variant"
    | some first :: _, 0 => decodeFields model order memory first image false
    | _ :: rest, index + 1 => decodeVariant model order memory rest index image
  termination_by sizeOf variants
end

/-- Constructor closure and the actual scalar leaf contract required by
producer-plan decoding. Error assumptions retain the original refusals. -/
structure DecodeRules (valid : Value → Prop) (error : SemError → Prop) : Prop where
  typeErrors : ∀ message, error (.typeError message)
  undefined : ∀ message, error (.ub message)
  scalar : ∀ model order memory ty bytes,
    ByteImage.BlockResult valid error (decodeMemoryWithFunctions model order memory ty bytes)
  integer : ∀ (width : Nat) (value : Int), valid (.int width value)
  uninit : valid .uninit
  aggregate : ∀ values, (∀ value ∈ values, valid value) → valid (.aggregate values)
  array : ∀ values : CompactArray.Packed Value, ByteImage.BlockTreeValid valid values.tree → valid (.array values)
  fnItem : ∀ target, valid (.fnItem target)

private def DecodedLanes (valid : Value → Prop) (values : List Value) : Prop := ∀ value ∈ values, valid value

private theorem decoded_cons (valid : Value → Prop) (first : Value) (rest : List Value)
    (head : valid first) (tail : DecodedLanes valid rest) : DecodedLanes valid (first :: rest) := by
  intro child member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact head
  · exact tail child member

mutual
  private theorem decodeCore_valid (valid : Value → Prop) (error : SemError → Prop) (rules : DecodeRules valid error)
      (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (plan : Plan)
      (image : ByteImage) (topChar allowUnwritten : Bool) :
      ByteImage.BlockResult valid error (decodeCore model order memory plan image topChar allowUnwritten) := by
    cases plan with
    | leaf ty layout =>
      rw [decodeCore]
      repeat' first
        | exact rules.typeErrors _
        | exact rules.scalar _ _ _ _ _
        | exact rules.integer _ _
        | (simp only [pure_bind])
        | (refine ByteImage.BlockResult.bind (fun _ => True) valid error _ _
            (initialized_errors error rules.undefined image) ?_; intro bytes _)
        | split
        | (dsimp only; split)
    | fnItem target layout =>
      rw [decodeCore]
      repeat' first
        | exact rules.typeErrors _
        | exact rules.fnItem target
        | split
        | (dsimp only; split)
    | fields ty layout fields =>
      rw [decodeCore]
      repeat' first
        | exact rules.typeErrors _
        | (simp only [pure_bind])
        | (refine ByteImage.BlockResult.bind (DecodedLanes valid) valid error _ _
            (decodeFields_valid valid error rules model order memory fields image allowUnwritten) ?_
           intro values held
           exact rules.aggregate values held)
        | split
        | (dsimp only; split)
    | array ty layout count element =>
      rw [decodeCore]
      repeat' first
        | exact rules.typeErrors _
        | (simp only [pure_bind])
        | (solve | apply rules.array; exact ByteImage.BlockTreeValid.empty valid)
        | (solve |
            change valid (.array (CompactArray.Packed.ofArray #[]))
            apply rules.array
            simpa [CompactArray.Packed.ofArray,CompactArray.Tree.ofArray,
              CompactArray.Tree.ofArrayRange,CompactArray.Leaf.ofArray] using ByteImage.BlockTreeValid.empty valid)
        | (solve | apply rules.array; exact ByteImage.BlockTreeValid.uniform valid _ _ (by assumption))
        | (solve | apply rules.array; assumption)
        | (refine ByteImage.BlockResult.bind valid valid error _ _
            (decodeCore_valid valid error rules model order memory element _ false false) ?_; intro value held)
        | (refine ByteImage.BlockResult.bind (ByteImage.BlockTreeValid valid) valid error _ _
            (ByteImage.mapBlocks_valid valid error _
              (fun part => decodeCore_valid valid error rules model order memory element part false false) _ _ _) ?_; intro tree held)
        | split
        | (dsimp only; split)
    | enumeration ty layout info variants =>
      rw [decodeCore]
      repeat' first
        | exact rules.typeErrors _
        | (simp only [pure_bind])
        | (refine ByteImage.BlockResult.bind (fun _ => True) valid error _ _
            (selectVariant_errors error rules.typeErrors rules.undefined info image) ?_; intro index _)
        | (refine ByteImage.BlockResult.bind (DecodedLanes valid) valid error _ _
            (decodeVariant_valid valid error rules model order memory variants _ image) ?_
           intro fields held
           exact rules.aggregate _ (decoded_cons valid _ fields (rules.integer _ _) held))
        | split
        | (dsimp only; split)
  termination_by sizeOf plan

  private theorem decodeFields_valid (valid : Value → Prop) (error : SemError → Prop) (rules : DecodeRules valid error)
      (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
      (fields : List (Nat × Plan)) (image : ByteImage) (allowUnwritten : Bool) :
      ByteImage.BlockResult (DecodedLanes valid) error (decodeFields model order memory fields image allowUnwritten) := by
    cases fields with
    | nil => trustIrCompilerProof { exact (fun _ member => by cases member) } { rw [decodeFields]; exact (fun _ member => by cases member) }
    | cons pair rest =>
      obtain ⟨offset,child⟩ := pair
      cases child <;> rw [decodeFields]
      all_goals repeat' first
        | (solve | intro _ _ _ impossible; exact impossible)
        | (solve | intro _ _ _ impossible; cases impossible)
        | exact rules.undefined _
        | (simp only [pure_bind])
        | (solve | exact decoded_cons valid _ _ (by assumption) (by assumption))
        | (solve | exact decoded_cons valid .uninit _ rules.uninit (by assumption))
        | (with_reducible refine (ByteImage.BlockResult.bind valid (DecodedLanes valid) error _ _
            (decodeCore_valid valid error rules model order memory _ _ false false) ?_); intro value held)
        | (with_reducible refine (ByteImage.BlockResult.bind valid (DecodedLanes valid) error _ _
            (decodeCore_valid valid error rules model order memory _ _ false true) ?_); intro value held)
        | (refine ByteImage.BlockResult.bind (DecodedLanes valid) (DecodedLanes valid) error _ _
            (decodeFields_valid valid error rules model order memory rest image allowUnwritten) ?_; intro values held)
        | (refine ByteImage.BlockResult.bind (fun _ => True) (DecodedLanes valid) error _ _
            (covered_errors error rules.typeErrors rules.undefined _ _) ?_; intro missing _)
        | split
        | (dsimp only; split)
  termination_by sizeOf fields

  private theorem decodeVariant_valid (valid : Value → Prop) (error : SemError → Prop) (rules : DecodeRules valid error)
      (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
      (variants : List (Option (List (Nat × Plan)))) (index : Nat) (image : ByteImage) :
      ByteImage.BlockResult (DecodedLanes valid) error (decodeVariant model order memory variants index image) := by
    cases variants with
    | nil => trustIrCompilerProof { exact rules.typeErrors _ } { rw [decodeVariant]; exact rules.typeErrors _ }
    | cons first rest =>
      cases index with
      | zero =>
        cases first with
        | none => rw [decodeVariant]; exact rules.undefined _
        | some fields => rw [decodeVariant]; exact decodeFields_valid valid error rules model order memory fields image false
      | succ index => rw [decodeVariant]; exact decodeVariant_valid valid error rules model order memory rest index image
  termination_by sizeOf variants
end

/-- Ordinary decoding never recovers an Uninit lane from unexplained holes. -/
def decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : Plan) (image : ByteImage) : Except SemError Value :=
  decodeCore model order memory plan image true false

/-- Actual strict nested decoding. Char retains the decoder's nested raw-word
    rule rather than the distinct top-level Unicode validation rule. -/
def ChildDecoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : Plan) (image : ByteImage) (value : Value) : Prop :=
  decodeCore model order memory plan image false false = .ok value

/-- Every successful strict nested call checked its complete child extent. -/
theorem ChildDecoded.extent {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {plan : Plan} {image : ByteImage} {value : Value}
    (run : ChildDecoded model order memory plan image value) : image.size = plan.layout.size := by
  by_cases sized : image.size = plan.layout.size
  · exact sized
  unfold ChildDecoded at run
  cases plan <;> rw [decodeCore] at run
  all_goals simp only [Plan.layout] at sized
  all_goals simp [Plan.layout,sized,imageError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run

/-- Execution of the production field decoder in ordinary strict mode. -/
def FieldsDecoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (fields : List (Nat × Plan)) (image : ByteImage) (values : List Value) : Prop :=
  decodeFields model order memory fields image false = .ok values

theorem FieldsDecoded.nil_iff (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (image : ByteImage) (values : List Value) :
    FieldsDecoded model order memory [] image values ↔ values = [] := by
  simp [FieldsDecoded,decodeFields,Pure.pure,Except.pure] <;> exact eq_comm

private theorem decodeFields_strict_cons_eq (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (offset : Nat) (child : Plan) (fields : List (Nat × Plan)) (image : ByteImage) :
    decodeFields model order memory ((offset,child) :: fields) image false = (do
      let value ← decodeCore model order memory child (image.slice offset child.layout.size) false false
      let later ← decodeFields model order memory fields image false
      pure (value :: later)) := by
  cases child <;> rw [decodeFields]
  all_goals simp [Bool.false_and,Bool.false_eq_true,ite_false,pure_bind]

theorem FieldsDecoded.head {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {offset : Nat} {child : Plan} {fields : List (Nat × Plan)} {image : ByteImage} {values : List Value}
    (run : FieldsDecoded model order memory ((offset,child) :: fields) image values) :
    ∃ value later, values = value :: later ∧
      ChildDecoded model order memory child (image.slice offset child.layout.size) value ∧
      FieldsDecoded model order memory fields image later := by
  unfold FieldsDecoded at run
  rw [decodeFields_strict_cons_eq] at run
  cases first : decodeCore model order memory child (image.slice offset child.layout.size) false false with
  | error failure => simp [first,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  | ok value =>
    cases rest : decodeFields model order memory fields image false with
    | error failure => simp [first,rest,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    | ok later =>
      simp [first,rest,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases run
      exact ⟨value,later,rfl,first,rest⟩

/-- A successful ordinary tuple/struct decoder exposes the real strict field
    run, its logical values and the checked parent byte extent. -/
theorem decode_fields_steps (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
    (image : ByteImage) (result : Value)
    (run : decode model order memory (.fields ty layout fields) image = .ok result) :
    image.size = layout.size ∧ ∃ values, result = .aggregate values ∧
      FieldsDecoded model order memory fields image values := by
  unfold decode at run
  rw [decodeCore] at run
  have fieldsLayout : (Plan.fields ty layout fields).layout = layout := rfl
  by_cases same : image.size = layout.size
  · simp only [fieldsLayout,same,bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
      Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    cases fieldsRun : decodeFields model order memory fields image false with
    | error failure => simp [fieldsRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    | ok values =>
      simp [fieldsRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases run
      exact ⟨same,values,rfl,fieldsRun⟩
  · simp [fieldsLayout,same,imageError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run

/-- The production selected-variant decoder, whose present rows use strict
    ordinary field decoding and whose absent rows retain their refusals. -/
def VariantDecoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (variants : List (Option (List (Nat × Plan)))) (position : Nat) (image : ByteImage)
    (values : List Value) : Prop :=
  decodeVariant model order memory variants position image = .ok values

theorem VariantDecoded.fields {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {variants : List (Option (List (Nat × Plan)))} {position : Nat} {image : ByteImage} {values : List Value}
    (run : VariantDecoded model order memory variants position image values) :
    ∃ fields, (trustIrListGet? variants position) = some (some fields) ∧ FieldsDecoded model order memory fields image values := by
  unfold VariantDecoded at run
  induction variants generalizing position with
  | nil => simp [decodeVariant,imageError] at run
  | cons row rest ih =>
    cases position with
    | zero =>
      cases row with
      | none => simp [decodeVariant,imageUB] at run
      | some fields =>
        rw [decodeVariant] at run
        exact ⟨fields,rfl,run⟩
    | succ position =>
      rw [decodeVariant] at run
      obtain ⟨fields,found,decoded⟩ := ih run
      exact ⟨fields,found,decoded⟩

/-- Extract exact slot callbacks from a real successful array decoder run.
    The mapper premise is discharged in the higher proof layer. -/
theorem decode_array_slots_of_mapper
    (mapper : ∀ (callback : ByteImage → Except SemError Value) (image : ByteImage)
      (width count : Nat), image.size = width * count →
      ∀ tree, image.mapBlocks callback width count = .ok tree → ByteImage.DecodedSlots callback image width tree)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (layoutExtent : layout.size = element.layout.size * count) (image : ByteImage) (result : Value)
    (run : decode model order memory (.array ty layout count element) image = .ok result) :
    image.size = layout.size ∧ ∃ values : CompactArray.Packed Value, result = .array values ∧ values.size = count ∧
      ∀ slot value, slot < count → values.tree.get? slot = some value →
        ∃ part, part.size = element.layout.size ∧
          (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) ∧
          ChildDecoded model order memory element part value := by
  unfold decode at run
  rw [decodeCore] at run
  have arrayLayout : (Plan.array ty layout count element).layout = layout := rfl
  by_cases same : image.size = layout.size
  · simp only [arrayLayout,same,bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
      Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    refine ⟨same,?_⟩
    by_cases noSlots : count = 0
    · subst count
      simp [Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases run
      refine ⟨CompactArray.Packed.ofArray #[],rfl,rfl,?_⟩
      intro slot value inside
      omega
    by_cases zeroWidth : element.layout.size = 0
    · cases childRun : decodeCore model order memory element ByteImage.empty false false with
      | error failure =>
        simp [noSlots,zeroWidth,childRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      | ok child =>
        simp [noSlots,zeroWidth,childRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
        cases run
        refine ⟨CompactArray.Packed.uniform count child,rfl,rfl,?_⟩
        intro slot value inside found
        simp only [CompactArray.Packed.uniform,CompactArray.Tree.get?,if_pos inside,Option.some.injEq] at found
        subst value
        refine ⟨ByteImage.empty,by simp [zeroWidth,ByteImage.empty],?_,childRun⟩
        intro index inByte
        omega
    · cases mapped : image.mapBlocks (fun part => decodeCore model order memory element part false false)
          element.layout.size count with
      | error failure =>
        simp [noSlots,zeroWidth,mapped,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      | ok tree =>
        simp [noSlots,zeroWidth,mapped,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
        cases run
        refine ⟨⟨count,tree⟩,rfl,rfl,?_⟩
        exact mapper _ image element.layout.size count (same.trans layoutExtent) tree mapped
  · simp [arrayLayout,same,imageError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run

/-- The caller first checks that all missing covered bytes are explained by
    the allocation's actual unwritten record. Only tuple/struct roots admit
    this path. Other shapes keep their ordinary strict decoding discipline. -/
def decodeUnwritten (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : Plan) (image : ByteImage) : Except SemError Value :=
  match plan with
  | .fields _ _ _ => decodeCore model order memory plan image true true
  | _ => imageUB "Load: unwritten records require a tuple or struct root"

/-- Full original strict decoder result invariant for every producer plan. -/
theorem decode_valid (valid : Value → Prop) (error : SemError → Prop) (rules : DecodeRules valid error)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (plan : Plan) (image : ByteImage) :
    ByteImage.BlockResult valid error (decode model order memory plan image) :=
  decodeCore_valid valid error rules model order memory plan image true false

/-- The original explained-unwritten decoder retains the same value and
error invariant, including nested field reconstruction and original refusals. -/
theorem decodeUnwritten_valid (valid : Value → Prop) (error : SemError → Prop) (rules : DecodeRules valid error)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (plan : Plan) (image : ByteImage) :
    ByteImage.BlockResult valid error (decodeUnwritten model order memory plan image) := by
  cases plan <;> first
    | exact rules.undefined _
    | exact decodeCore_valid valid error rules model order memory _ image true true

/-- Initialization of the actual retained lane that the decoder reads. -/
def InitializedLane (image : ByteImage) (offset count : Nat) (bytes : List UInt8) : Prop :=
  initialized (image.slice offset count) = .ok bytes

/-- Variant selection by the actual decoder, including live/range guards. -/
def EnumDecodingSelects (info : Enumeration) (image : ByteImage) (position : Nat) : Prop :=
  selectVariant info image = .ok position

/-- Exact rejection by the actual selector, before any payload traversal. -/
def EnumDecodingRejects (info : Enumeration) (image : ByteImage) (error : SemError) : Prop :=
  selectVariant info image = .error error

theorem EnumDecodingSelects.functional {info : Enumeration} {image : ByteImage} {first second : Nat}
    (left : EnumDecodingSelects info image first) (right : EnumDecodingSelects info image second) : first = second := by
  unfold EnumDecodingSelects at left right
  exact Except.ok.inj (left.symm.trans right)

private theorem decode_enumeration_core_steps (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (image : ByteImage) (result : Value)
    (topChar allowUnwritten : Bool)
    (run : decodeCore model order memory (.enumeration ty layout info variants) image topChar allowUnwritten = .ok result) :
    image.size = layout.size ∧ ∃ position discriminant fields values,
      EnumDecodingSelects info image position ∧ (trustIrListGet? info.discriminants position) = some discriminant ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      result = .aggregate (Value.intAt (tagBits info.tag) discriminant :: values) ∧
      FieldsDecoded model order memory fields image values := by
  rw [decodeCore] at run
  have enumLayout : (Plan.enumeration ty layout info variants).layout = layout := rfl
  by_cases same : image.size = layout.size
  · simp only [enumLayout,same,bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
      Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    cases selected : selectVariant info image with
    | error failure => simp [selected] at run
    | ok position =>
      simp only [selected] at run
      cases discriminantRow : (trustIrListGet? info.discriminants position) with
      | none => simp [discriminantRow,imageError] at run
      | some discriminant =>
        simp only [discriminantRow] at run
        cases payloadRun : decodeVariant model order memory variants position image with
        | error failure => simp [payloadRun] at run
        | ok values =>
          simp only [payloadRun,Except.ok.injEq] at run
          cases run
          obtain ⟨fields,row,fieldsRun⟩ := VariantDecoded.fields payloadRun
          exact ⟨same,position,discriminant,fields,values,selected,discriminantRow,row,rfl,fieldsRun⟩
  · simp [enumLayout,same,imageError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run

/-- Successful ordinary enum decoding exposes the actual selector, logical
    discriminant row and strict payload field run, without guessing a variant. -/
theorem decode_enumeration_steps (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (image : ByteImage) (result : Value)
    (run : decode model order memory (.enumeration ty layout info variants) image = .ok result) :
    image.size = layout.size ∧ ∃ position discriminant fields values,
      EnumDecodingSelects info image position ∧ (trustIrListGet? info.discriminants position) = some discriminant ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      result = .aggregate (Value.intAt (tagBits info.tag) discriminant :: values) ∧
      FieldsDecoded model order memory fields image values :=
  decode_enumeration_core_steps model order memory ty layout info variants image result true false run

/-- Strict nested enum decoding retains the same payload custody while keeping
    the actual nested mode, rather than substituting a top-level leaf decoder. -/
theorem ChildDecoded.enumeration_steps {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {ty : Ty} {layout : MemoryTypeLayout} {info : Enumeration}
    {variants : List (Option (List (Nat × Plan)))} {image : ByteImage} {result : Value}
    (run : ChildDecoded model order memory (.enumeration ty layout info variants) image result) :
    image.size = layout.size ∧ ∃ position discriminant fields values,
      EnumDecodingSelects info image position ∧ (trustIrListGet? info.discriminants position) = some discriminant ∧
      (trustIrListGet? variants position) = some (some fields) ∧
      result = .aggregate (Value.intAt (tagBits info.tag) discriminant :: values) ∧
      FieldsDecoded model order memory fields image values :=
  decode_enumeration_core_steps model order memory ty layout info variants image result false false run

theorem EnumDecodingSelects.untagged (info : Enumeration) (image : ByteImage)
    (encoding : info.encoding = .untagged) (live : (trustIrListGet? info.uninhabited 0) = some false)
    (bound : 0 < info.discriminants.length) : EnumDecodingSelects info image 0 := by
  unfold EnumDecodingSelects selectVariant
  rw [encoding]
  simp [Bind.bind,Except.bind,Pure.pure,Except.pure,live,Nat.not_le_of_lt bound]

theorem EnumDecodingSelects.single (info : Enumeration) (image : ByteImage) (selected : Nat)
    (encoding : info.encoding = .singleInhabited selected) (live : (trustIrListGet? info.uninhabited selected) = some false)
    (bound : selected < info.discriminants.length) : EnumDecodingSelects info image selected := by
  unfold EnumDecodingSelects selectVariant
  rw [encoding]
  simp [Bind.bind,Except.bind,Pure.pure,Except.pure,live,Nat.not_le_of_lt bound]

theorem EnumDecodingSelects.direct_encoding (info : Enumeration) (image : ByteImage) (offset position : Nat)
    (bytes : List UInt8) (encoding : DirectEncodingAt info.encoding offset)
    (read : InitializedLane image offset (tagBits info.tag / 8) bytes)
    (found : discriminantIndex info.discriminants (if tagSigned info.tag then
      toSigned (Int.ofNat (decodeIntBytes bytes)) (tagBits info.tag) else Int.ofNat (decodeIntBytes bytes)) = some position)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  rcases encoding with encoding | ⟨profiles, encoding⟩
  all_goals
    unfold EnumDecodingSelects selectVariant
    rw [encoding]
    dsimp only
    change initialized (image.slice offset (tagBits info.tag / 8)) = .ok bytes at read
    rw [read]
    simp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
    rw [found]
    simp [live,Nat.not_le_of_lt bound]

theorem EnumDecodingSelects.direct (info : Enumeration) (image : ByteImage) (offset position : Nat)
    (bytes : List UInt8) (encoding : info.encoding = .direct offset)
    (read : InitializedLane image offset (tagBits info.tag / 8) bytes)
    (found : discriminantIndex info.discriminants (if tagSigned info.tag then
      toSigned (Int.ofNat (decodeIntBytes bytes)) (tagBits info.tag) else Int.ofNat (decodeIntBytes bytes)) = some position)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  exact EnumDecodingSelects.direct_encoding info image offset position bytes (Or.inl encoding) read found live bound

theorem EnumDecodingSelects.profiled_direct (info : Enumeration) (image : ByteImage) (offset position : Nat)
    (bytes : List UInt8) {profiles : List UninhabitedVariantLayout} (encoding : info.encoding = .directWithUninhabited offset profiles)
    (read : InitializedLane image offset (tagBits info.tag / 8) bytes)
    (found : discriminantIndex info.discriminants (if tagSigned info.tag then
      toSigned (Int.ofNat (decodeIntBytes bytes)) (tagBits info.tag) else Int.ofNat (decodeIntBytes bytes)) = some position)
    (live : (trustIrListGet? info.uninhabited position) = some false) (bound : position < info.discriminants.length) :
    EnumDecodingSelects info image position := by
  exact EnumDecodingSelects.direct_encoding info image offset position bytes (Or.inr ⟨profiles, encoding⟩) read found live bound


theorem EnumDecodingSelects.niche_tagged (info : Enumeration) (image : ByteImage)
    (untagged start stop first offset position : Nat) (repr : EnumTagRepr) (bytes : List UInt8)
    (encoding : info.encoding = .niche untagged start stop first offset repr)
    (read : InitializedLane image offset (tagBits repr / 8) bytes)
    (reserved : (decodeIntBytes bytes + 2 ^ tagBits repr - first) % (2 ^ tagBits repr) ≤ stop - start)
    (positionEq : position = start + (decodeIntBytes bytes + 2 ^ tagBits repr - first) % (2 ^ tagBits repr))
    (other : position ≠ untagged) (live : (trustIrListGet? info.uninhabited position) = some false)
    (bound : position < info.discriminants.length) : EnumDecodingSelects info image position := by
  unfold EnumDecodingSelects selectVariant
  rw [encoding]
  dsimp only
  change initialized (image.slice offset (tagBits repr / 8)) = .ok bytes at read
  rw [read]
  subst position
  have different : ((start + (decodeIntBytes bytes + 2 ^ tagBits repr - first) % (2 ^ tagBits repr)) == untagged) = false := by
    simp [other]
  simp [Bind.bind,Except.bind,Pure.pure,Except.pure,reserved,different,live,Nat.not_le_of_lt bound]

theorem EnumDecodingSelects.niche_untagged (info : Enumeration) (image : ByteImage)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr) (bytes : List UInt8)
    (encoding : info.encoding = .niche untagged start stop first offset repr)
    (read : InitializedLane image offset (tagBits repr / 8) bytes)
    (outside : stop - start < (decodeIntBytes bytes + 2 ^ tagBits repr - first) % (2 ^ tagBits repr))
    (live : (trustIrListGet? info.uninhabited untagged) = some false) (bound : untagged < info.discriminants.length) :
    EnumDecodingSelects info image untagged := by
  unfold EnumDecodingSelects selectVariant
  rw [encoding]
  dsimp only
  change initialized (image.slice offset (tagBits repr / 8)) = .ok bytes at read
  rw [read]
  simp [Bind.bind,Except.bind,Pure.pure,Except.pure,Nat.not_le_of_lt outside,live,Nat.not_le_of_lt bound]

private theorem initialized_map_some (bytes : List UInt8) : (bytes.map some).mapM id = some bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih => simp [List.mapM_cons,ih]

private theorem initialized_mapM_exact (data : List (Option UInt8)) (bytes : List UInt8)
    (run : data.mapM id = some bytes) : data = bytes.map some := by
  induction data generalizing bytes with
  | nil => cases run; rfl
  | cons first rest ih =>
    cases first with
    | none => simp [List.mapM_cons] at run
    | some byte =>
      cases following : rest.mapM id with
      | none => simp [List.mapM_cons,following] at run
      | some tail =>
        have emitted : (some byte :: rest).mapM id = some (byte :: tail) := by simp [List.mapM_cons,following]
        have same := Option.some.inj (emitted.symm.trans run)
        rw [← same,ih tail following]
        rfl

theorem InitializedLane.of_materialized (image : ByteImage) (offset count : Nat) (bytes : List UInt8)
    (materialized : (image.slice offset count).toList = bytes.map some) : InitializedLane image offset count bytes := by
  unfold InitializedLane initialized
  rw [materialized,initialized_map_some]

theorem InitializedLane.materialized {image : ByteImage} {offset count : Nat} {bytes : List UInt8}
    (read : InitializedLane image offset count bytes) : (image.slice offset count).toList = bytes.map some := by
  unfold InitializedLane initialized at read
  cases collected : (image.slice offset count).toList.mapM id with
  | none => rw [collected] at read; cases read
  | some actual =>
    rw [collected] at read
    cases read
    exact initialized_mapM_exact _ _ collected

theorem InitializedLane.defaulted {image : ByteImage} {offset count : Nat} {bytes : List UInt8}
    (read : InitializedLane image offset count bytes) :
    (image.slice offset count).toList.map (·.getD 0) = bytes := by
  rw [read.materialized]
  simpa only [List.map_map] using (List.map_id bytes)

/-- Direct selection depends only on the actual initialized tag read. -/
theorem EnumDecodingSelects.transfer_direct_encoding {info : Enumeration} {before after : ByteImage}
    {position offset : Nat} {bytes : List UInt8} (encoding : DirectEncodingAt info.encoding offset)
    (initial : InitializedLane before offset (tagBits info.tag / 8) bytes)
    (final : InitializedLane after offset (tagBits info.tag / 8) bytes)
    (selected : EnumDecodingSelects info before position) : EnumDecodingSelects info after position := by
  rcases encoding with encoding | ⟨profiles, encoding⟩
  all_goals
    unfold InitializedLane at initial final
    unfold EnumDecodingSelects selectVariant at selected ⊢
    simp only [encoding,initial,Bind.bind,Except.bind,Pure.pure,Except.pure] at selected
    simp only [encoding,final,Bind.bind,Except.bind,Pure.pure,Except.pure]
    exact selected

theorem EnumDecodingSelects.transfer_direct {info : Enumeration} {before after : ByteImage}
    {position offset : Nat} {bytes : List UInt8} (encoding : info.encoding = .direct offset)
    (initial : InitializedLane before offset (tagBits info.tag / 8) bytes)
    (final : InitializedLane after offset (tagBits info.tag / 8) bytes)
    (selected : EnumDecodingSelects info before position) : EnumDecodingSelects info after position := by
  exact EnumDecodingSelects.transfer_direct_encoding (Or.inl encoding) initial final selected

theorem EnumDecodingSelects.transfer_profiled_direct {info : Enumeration} {before after : ByteImage}
    {position offset : Nat} {bytes : List UInt8} {profiles : List UninhabitedVariantLayout} (encoding : info.encoding = .directWithUninhabited offset profiles)
    (initial : InitializedLane before offset (tagBits info.tag / 8) bytes)
    (final : InitializedLane after offset (tagBits info.tag / 8) bytes)
    (selected : EnumDecodingSelects info before position) : EnumDecodingSelects info after position := by
  exact EnumDecodingSelects.transfer_direct_encoding (Or.inr ⟨profiles, encoding⟩) initial final selected


/-- Niche selection depends only on the actual initialized carrier read. -/
theorem EnumDecodingSelects.transfer_niche {info : Enumeration} {before after : ByteImage}
    {position untagged start stop first offset : Nat} {repr : EnumTagRepr} {bytes : List UInt8}
    (encoding : info.encoding = .niche untagged start stop first offset repr)
    (initial : InitializedLane before offset (tagBits repr / 8) bytes)
    (final : InitializedLane after offset (tagBits repr / 8) bytes)
    (selected : EnumDecodingSelects info before position) : EnumDecodingSelects info after position := by
  unfold InitializedLane at initial final
  unfold EnumDecodingSelects selectVariant at selected ⊢
  simp only [encoding,initial,Bind.bind,Except.bind,Pure.pure,Except.pure] at selected
  simp only [encoding,final,Bind.bind,Except.bind,Pure.pure,Except.pure]
  exact selected

private theorem initialized_literal (bytes : List UInt8) :
    initialized (ByteImage.ofList (bytes.map some)) = .ok bytes := by
  have materialized : (ByteImage.ofList (bytes.map some)).toList = bytes.map some := by
    trustIrCompilerProof { apply List.ext } { apply CompilerCompat.listGetConstructive_ext }
    intro position
    rw [ByteImage.toList,trustIrListGetMap,SourceLayout.numbered_range_lookup,ByteImage.size_ofList,List.length_map]
    by_cases inside : position < bytes.length
    · rw [if_pos inside,trustIrListGetMap,CompilerCompat.listGet?_eq_get inside]
      apply congrArg some
      rw [ByteImage.get_ofList,trustIrListGetMap,CompilerCompat.listGet?_eq_get inside]
      rfl
    · rw [if_neg inside,CompilerCompat.listGet?_outside _ _ (by simp only [List.length_map]; omega)]
      rfl
  unfold initialized
  rw [materialized,initialized_map_some]

/-- A fully initialized leaf image reaches the real contextual decoder,
including top-level Char validity and function/data-pointer interpretation. -/
theorem decode_leaf_of_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (bytes : List UInt8) (size : bytes.length = layout.size) :
    decode model order memory (.leaf ty layout) (ByteImage.ofList (bytes.map some)) =
      decodeMemoryWithFunctions model order memory ty bytes := by
  unfold decode
  rw [decodeCore]
  simp only [ByteImage.size_ofList,List.length_map,size,Plan.layout,bne,beq_self_eq_true,
    Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
  rw [initialized_literal]
  cases ty <;> rfl


/-- A manually constructed scalar leaf cannot reconstruct a nominal item.
Only the source compiler's dedicated plan carries that operation. -/
theorem decode_fnItem_as_scalar_leaf_refuses (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (target : FuncId) (layout : MemoryTypeLayout)
    (image : ByteImage) (value : Value) :
    decode model order memory (.leaf (.FnItem target) layout) image ≠ .ok value := by
  intro success
  unfold decode at success
  rw [decodeCore] at success
  by_cases sized : image.size = layout.size
  · simp only [Plan.layout,sized,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
      Bind.bind,Except.bind,Pure.pure,Except.pure] at success
    cases initializedImage : initialized image with
    | error failure => simp [initializedImage,Bind.bind,Except.bind] at success
    | ok bytes => simp [initializedImage,decodeMemoryWithFunctions,Bind.bind,Except.bind] at success
  · simp [Plan.layout,sized,imageError,Bind.bind,Except.bind,Pure.pure,Except.pure] at success

/-- A literal initialized image reaches the actual nested scalar branch.
    Char retains its raw 32-bit rule; other types use contextual decoding. -/
theorem ChildDecoded.leaf_bytes_iff (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (bytes : List UInt8) (size : bytes.length = layout.size)
    (value : Value) :
    ChildDecoded model order memory (.leaf ty layout) (ByteImage.ofList (bytes.map some)) value ↔
      (match ty with
       | .Char => Except.ok (Value.int 32 (Int.ofNat (decodeIntBytes bytes)))
       | _ => decodeMemoryWithFunctions model order memory ty bytes) = .ok value := by
  unfold ChildDecoded
  rw [decodeCore]
  simp only [ByteImage.size_ofList,List.length_map,size,Plan.layout,bne,beq_self_eq_true,
    Bool.not_true,Bool.false_eq_true,ite_false]
  rw [initialized_literal]
  cases ty <;> rfl

/-- The production selector, including every refusal, depends only on complete
    byte observations and extent, never on compact image constructors. -/
theorem selectVariant_eq_of_observations (info : Enumeration) (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index) :
    selectVariant info left = selectVariant info right := by
  unfold selectVariant
  simp only [initialized,ByteImage.slice_toList_eq_of_observations left right extent bytes]

/-- Selection success transfers in either direction through equal observed
    images. Uninitialized, invalid and uninhabited tags keep their refusals. -/
theorem EnumDecodingSelects.iff_of_observations (info : Enumeration) (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index)
    (position : Nat) :
    EnumDecodingSelects info left position ↔ EnumDecodingSelects info right position := by
  unfold EnumDecodingSelects
  rw [selectVariant_eq_of_observations info left right extent bytes]

private theorem decode_leaf_core_eq_of_observations (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout) (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index)
    (topChar allowUnwritten : Bool) :
    decodeCore model order memory (.leaf ty layout) left topChar allowUnwritten =
      decodeCore model order memory (.leaf ty layout) right topChar allowUnwritten := by
  rw [decodeCore,decodeCore]
  simp only [extent,initialized,ByteImage.toList_eq_of_observations left right extent bytes]

/-- Actual scalar decoding preserves both results and failures under equal
    observed images, retaining top-level Unicode and extent checks. -/
theorem decode_leaf_eq_of_observations (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout) (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index) :
    decode model order memory (.leaf ty layout) left = decode model order memory (.leaf ty layout) right :=
  decode_leaf_core_eq_of_observations model order memory ty layout left right extent bytes true false

/-- Strict nested scalar calls transfer through equal observed bytes without
    substituting the distinct top-level Char decoder. -/
theorem ChildDecoded.leaf_iff_of_observations (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout) (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index) (value : Value) :
    ChildDecoded model order memory (.leaf ty layout) left value ↔
      ChildDecoded model order memory (.leaf ty layout) right value := by
  unfold ChildDecoded
  rw [decode_leaf_core_eq_of_observations model order memory ty layout left right extent bytes false false]


/-- Actual strict child successes compose into the production field run. -/
theorem FieldsDecoded.cons {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {offset : Nat} {child : Plan} {fields : List (Nat × Plan)} {image : ByteImage}
    {value : Value} {values : List Value}
    (first : ChildDecoded model order memory child (image.slice offset child.layout.size) value)
    (rest : FieldsDecoded model order memory fields image values) :
    FieldsDecoded model order memory ((offset,child) :: fields) image (value :: values) := by
  unfold FieldsDecoded
  rw [decodeFields_strict_cons_eq]
  unfold ChildDecoded at first
  unfold FieldsDecoded at rest
  simp only [first,rest,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Exact census and every actual indexed child call suffice for a complete
    strict field run. This constructs decoder success rather than assuming it. -/
theorem FieldsDecoded.of_get (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (fields : List (Nat × Plan)) (image : ByteImage) (values : List Value)
    (census : fields.length = values.length)
    (children : ∀ position offset child value, (trustIrListGet? fields position) = some (offset,child) →
      (trustIrListGet? values position) = some value → ChildDecoded model order memory child (image.slice offset child.layout.size) value) :
    FieldsDecoded model order memory fields image values := by
  induction fields generalizing values with
  | nil =>
    cases values with
    | nil => exact (FieldsDecoded.nil_iff model order memory image []).mpr rfl
    | cons value values => simp at census
  | cons field fields ih =>
    obtain ⟨offset,child⟩ := field
    cases values with
    | nil => simp at census
    | cons value values =>
      apply FieldsDecoded.cons (children 0 offset child value rfl rfl)
      apply ih values (Nat.succ.inj census)
      intro position laterOffset laterChild laterValue found selected
      exact children (position + 1) laterOffset laterChild laterValue found selected

private theorem decode_fields_core_of_children (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (image : ByteImage) (values : List Value)
    (extent : image.size = layout.size) (run : FieldsDecoded model order memory fields image values) (topChar : Bool) :
    decodeCore model order memory (.fields ty layout fields) image topChar false = .ok (.aggregate values) := by
  unfold FieldsDecoded at run
  rw [decodeCore]
  simp only [Plan.layout,extent,bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
    run,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- A checked parent extent and actual strict payload run construct ordinary
    tuple/struct decoding, including live empty products. -/
theorem decode_fields_of_children (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (image : ByteImage) (values : List Value)
    (extent : image.size = layout.size) (run : FieldsDecoded model order memory fields image values) :
    decode model order memory (.fields ty layout fields) image = .ok (.aggregate values) :=
  decode_fields_core_of_children model order memory ty layout fields image values extent run true

/-- The same strict field run constructs an actual nested aggregate call. -/
theorem ChildDecoded.fields_of_children (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (image : ByteImage) (values : List Value)
    (extent : image.size = layout.size) (run : FieldsDecoded model order memory fields image values) :
    ChildDecoded model order memory (.fields ty layout fields) image (.aggregate values) :=
  decode_fields_core_of_children model order memory ty layout fields image values extent run false

/-- Only a present payload row and its actual strict field run can construct
    selected-variant success. Absent and uninhabited rows remain refusals. -/
theorem VariantDecoded.of_fields (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (variants : List (Option (List (Nat × Plan)))) (position : Nat) (image : ByteImage) (values : List Value)
    (fields : List (Nat × Plan)) (row : (trustIrListGet? variants position) = some (some fields))
    (run : FieldsDecoded model order memory fields image values) :
    VariantDecoded model order memory variants position image values := by
  unfold VariantDecoded
  induction variants generalizing position with
  | nil => cases row
  | cons first rest ih =>
    cases position with
    | zero =>
      have same : first = some fields := Option.some.inj row
      subst first
      rw [decodeVariant]
      exact run
    | succ position =>
      rw [decodeVariant]
      exact ih position row

private theorem decode_enumeration_core_of_rejection (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (image : ByteImage) (error : SemError)
    (extent : image.size = layout.size) (rejected : EnumDecodingRejects info image error)
    (topChar allowUnwritten : Bool) :
    decodeCore model order memory (.enumeration ty layout info variants) image topChar allowUnwritten =
      .error error := by
  unfold EnumDecodingRejects at rejected
  rw [decodeCore]
  simp only [Plan.layout,extent,bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
    rejected,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- A correctly sized enum image propagates its exact selection error.
No payload row, field decoder or well-founded payload rank is evaluated. -/
theorem decode_enumeration_of_rejection (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (image : ByteImage) (error : SemError)
    (extent : image.size = layout.size) (rejected : EnumDecodingRejects info image error) :
    decode model order memory (.enumeration ty layout info variants) image = .error error :=
  decode_enumeration_core_of_rejection model order memory ty layout info variants image error
    extent rejected true false

private theorem decode_enumeration_core_of_payload (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (image : ByteImage) (position : Nat) (discriminant : Int) (fields : List (Nat × Plan)) (values : List Value)
    (extent : image.size = layout.size) (selected : EnumDecodingSelects info image position)
    (discriminantRow : (trustIrListGet? info.discriminants position) = some discriminant)
    (row : (trustIrListGet? variants position) = some (some fields)) (run : FieldsDecoded model order memory fields image values)
    (topChar : Bool) :
    decodeCore model order memory (.enumeration ty layout info variants) image topChar false =
      .ok (.aggregate (Value.intAt (tagBits info.tag) discriminant :: values)) := by
  have payload := VariantDecoded.of_fields model order memory variants position image values fields row run
  unfold VariantDecoded at payload
  unfold EnumDecodingSelects at selected
  rw [decodeCore]
  simp only [Plan.layout,extent,bne,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
    selected,discriminantRow,payload,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Actual selection, discriminant lookup and strict payload success compose
    into ordinary enum decoding. Carrier readiness is not inferred from layout. -/
theorem decode_enumeration_of_payload (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (image : ByteImage) (position : Nat) (discriminant : Int) (fields : List (Nat × Plan)) (values : List Value)
    (extent : image.size = layout.size) (selected : EnumDecodingSelects info image position)
    (discriminantRow : (trustIrListGet? info.discriminants position) = some discriminant)
    (row : (trustIrListGet? variants position) = some (some fields)) (run : FieldsDecoded model order memory fields image values) :
    decode model order memory (.enumeration ty layout info variants) image =
      .ok (.aggregate (Value.intAt (tagBits info.tag) discriminant :: values)) :=
  decode_enumeration_core_of_payload model order memory ty layout info variants image position discriminant fields values
    extent selected discriminantRow row run true

/-- Enum parent construction also retains the actual strict nested mode. -/
theorem ChildDecoded.enumeration_of_payload (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration) (variants : List (Option (List (Nat × Plan))))
    (image : ByteImage) (position : Nat) (discriminant : Int) (fields : List (Nat × Plan)) (values : List Value)
    (extent : image.size = layout.size) (selected : EnumDecodingSelects info image position)
    (discriminantRow : (trustIrListGet? info.discriminants position) = some discriminant)
    (row : (trustIrListGet? variants position) = some (some fields)) (run : FieldsDecoded model order memory fields image values) :
    ChildDecoded model order memory (.enumeration ty layout info variants) image
      (.aggregate (Value.intAt (tagBits info.tag) discriminant :: values)) :=
  decode_enumeration_core_of_payload model order memory ty layout info variants image position discriminant fields values
    extent selected discriminantRow row run false


/-- Successful production selection has passed its actual range guard. -/
theorem EnumDecodingSelects.bound {info : Enumeration} {image : ByteImage} {position : Nat}
    (selected : EnumDecodingSelects info image position) : position < info.discriminants.length := by
  unfold EnumDecodingSelects selectVariant at selected
  simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at selected
  repeat' split at selected
  all_goals simp_all [imageError,imageUB,Bind.bind,Except.bind,Pure.pure,Except.pure]
  all_goals trustIrCompilerProof { omega } {
    have nonempty : info.discriminants ≠ [] := by assumption
    have positive := List.length_pos_iff.mpr nonempty
    omega
  }

/-- Selection success authenticates a real logical discriminant row. -/
theorem EnumDecodingSelects.discriminant {info : Enumeration} {image : ByteImage} {position : Nat}
    (selected : EnumDecodingSelects info image position) :
    ∃ discriminant, (trustIrListGet? info.discriminants position) = some discriminant :=
  ⟨info.discriminants.get ⟨position,selected.bound⟩,CompilerCompat.listGet?_eq_get selected.bound⟩


theorem ChildDecoded.functional {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {plan : Plan} {image : ByteImage} {first second : Value}
    (left : ChildDecoded model order memory plan image first) (right : ChildDecoded model order memory plan image second) :
    first = second := Except.ok.inj (left.symm.trans right)

private theorem decode_array_core_exists_of_mapper
    (mapper : ∀ (callback : ByteImage → Except SemError Value) (image : ByteImage) (width count : Nat),
      image.size = width * count → ByteImage.BlockWindowsSucceed callback image width count →
      ∃ tree, image.mapBlocks callback width count = .ok tree)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (image : ByteImage)
    (layoutExtent : layout.size = element.layout.size * count) (imageExtent : image.size = layout.size)
    (children : ∀ slot, slot < count → ∀ part, part.size = element.layout.size →
      (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) →
      ∃ value, ChildDecoded model order memory element part value) (topChar : Bool) :
    ∃ values : CompactArray.Packed Value, values.size = count ∧
      decodeCore model order memory (.array ty layout count element) image topChar false = .ok (.array values) := by
  have arrayLayout : (Plan.array ty layout count element).layout = layout := rfl
  by_cases noSlots : count = 0
  · subst count
    refine ⟨CompactArray.Packed.ofArray #[],rfl,?_⟩
    rw [decodeCore]
    simp [arrayLayout,imageExtent,Bind.bind,Except.bind,Pure.pure,Except.pure]
  by_cases zeroWidth : element.layout.size = 0
  · obtain ⟨value,decoded⟩ := children 0 (by omega) ByteImage.empty (by change 0 = element.layout.size; omega)
      (by intro index inside; omega)
    refine ⟨CompactArray.Packed.uniform count value,rfl,?_⟩
    unfold ChildDecoded at decoded
    rw [decodeCore]
    simp [arrayLayout,imageExtent,noSlots,zeroWidth,decoded,Bind.bind,Except.bind,Pure.pure,Except.pure]
  · have windows : ByteImage.BlockWindowsSucceed
        (fun part => decodeCore model order memory element part false false) image element.layout.size count := by
      intro slot inside part partSize bytes
      exact children slot inside part partSize bytes
    obtain ⟨tree,mapped⟩ := mapper _ image element.layout.size count (imageExtent.trans layoutExtent) windows
    refine ⟨⟨count,tree⟩,rfl,?_⟩
    rw [decodeCore]
    simp [arrayLayout,imageExtent,noSlots,zeroWidth,mapped,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Complete actual slot-window read guarantees construct ordinary array
    decoding, including empty arrays and visible zero-byte elements. -/
theorem decode_array_exists_of_mapper
    (mapper : ∀ (callback : ByteImage → Except SemError Value) (image : ByteImage) (width count : Nat),
      image.size = width * count → ByteImage.BlockWindowsSucceed callback image width count →
      ∃ tree, image.mapBlocks callback width count = .ok tree)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (image : ByteImage)
    (layoutExtent : layout.size = element.layout.size * count) (imageExtent : image.size = layout.size)
    (children : ∀ slot, slot < count → ∀ part, part.size = element.layout.size →
      (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) →
      ∃ value, ChildDecoded model order memory element part value) :
    ∃ values : CompactArray.Packed Value, values.size = count ∧
      decode model order memory (.array ty layout count element) image = .ok (.array values) :=
  decode_array_core_exists_of_mapper mapper model order memory ty layout count element image layoutExtent imageExtent children true

/-- Array construction retains actual nested decoder mode as well. -/
theorem ChildDecoded.array_exists_of_mapper
    (mapper : ∀ (callback : ByteImage → Except SemError Value) (image : ByteImage) (width count : Nat),
      image.size = width * count → ByteImage.BlockWindowsSucceed callback image width count →
      ∃ tree, image.mapBlocks callback width count = .ok tree)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (image : ByteImage)
    (layoutExtent : layout.size = element.layout.size * count) (imageExtent : image.size = layout.size)
    (children : ∀ slot, slot < count → ∀ part, part.size = element.layout.size →
      (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) →
      ∃ value, ChildDecoded model order memory element part value) :
    ∃ values : CompactArray.Packed Value, values.size = count ∧
      ChildDecoded model order memory (.array ty layout count element) image (.array values) :=
  decode_array_core_exists_of_mapper mapper model order memory ty layout count element image layoutExtent imageExtent children false


/-- Ordinary and nested array roots both make strict nested element calls;
    the top-level Char flag does not change an array's result or refusal. -/
theorem ChildDecoded.array_iff_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (image : ByteImage) (result : Value) :
    ChildDecoded model order memory (.array ty layout count element) image result ↔
      decode model order memory (.array ty layout count element) image = .ok result := by
  unfold ChildDecoded decode
  conv => lhs; lhs; rw [decodeCore]
  conv => rhs; lhs; rw [decodeCore]


/-- Outside Char, ordinary and strict nested leaf decoding are identical.
    Char's distinct Unicode check remains excluded explicitly. -/
theorem ChildDecoded.leaf_iff_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (image : ByteImage) (result : Value) (notChar : ty ≠ .Char) :
    ChildDecoded model order memory (.leaf ty layout) image result ↔
      decode model order memory (.leaf ty layout) image = .ok result := by
  unfold ChildDecoded decode
  cases ty
  all_goals first
    | exact False.elim (notChar rfl)
    | (conv => lhs; lhs; rw [decodeCore]
       conv => rhs; lhs; rw [decodeCore])


/-- Non-Char roots retain identical ordinary and strict nested calls. This
    includes aggregate roots containing Char, whose children remain strict. -/
theorem ChildDecoded.ordinary_iff_decode (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : Plan) (image : ByteImage) (result : Value) (ordinary : ∀ layout, plan ≠ .leaf .Char layout) :
    ChildDecoded model order memory plan image result ↔ decode model order memory plan image = .ok result := by
  cases plan with
  | leaf ty layout =>
    exact ChildDecoded.leaf_iff_decode model order memory ty layout image result (by
      intro same
      subst ty
      exact ordinary layout rfl)
  | fnItem target layout =>
    unfold ChildDecoded decode
    conv => lhs; lhs; rw [decodeCore]
    conv => rhs; lhs; rw [decodeCore]
  | fields ty layout fields =>
    unfold ChildDecoded decode
    conv => lhs; lhs; rw [decodeCore]
    conv => rhs; lhs; rw [decodeCore]
  | array ty layout count element => exact ChildDecoded.array_iff_decode model order memory ty layout count element image result
  | enumeration ty layout info variants =>
    unfold ChildDecoded decode
    conv => lhs; lhs; rw [decodeCore]
    conv => rhs; lhs; rw [decodeCore]

/-- Exact item leaf for either internal decode mode; neither mode changes
    nominal identity or relaxes the checked byte extent and alignment. -/
theorem decodeCore_fnItem (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (target : FuncId) (layout : MemoryTypeLayout) (image : ByteImage)
    (topChar allowUnwritten : Bool) :
    decodeCore model order memory (.fnItem target layout) image topChar allowUnwritten = (do
      if image.size != layout.size then
        return ← imageError "Load: image size does not match source layout"
      if layout.size != 0 || layout.alignment != 1 then
        imageError "Load: function item layout is not zero-sized/alignment-one"
      else pure (.fnItem target)) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta decodeCore decodeCore._mutual
      rw [WellFounded.fix_eq]
    rfl
  } {
    rw [decodeCore.eq_def] <;> rfl
  }

/-- A prepared item-typed plan, not bytes or a code-address table, supplies
    the singleton identity. Invalid layout geometry remains a refusal. -/
theorem decode_fnItem (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (target : FuncId) (layout : MemoryTypeLayout) (image : ByteImage) :
    decode model order memory (.fnItem target layout) image = (do
      if image.size != layout.size then
        return ← imageError "Load: image size does not match source layout"
      if layout.size != 0 || layout.alignment != 1 then
        imageError "Load: function item layout is not zero-sized/alignment-one"
      else pure (.fnItem target)) := by
  trustIrCompilerProof {
    unfold decode
    conv =>
      lhs
      delta decodeCore decodeCore._mutual
      rw [WellFounded.fix_eq]
    rfl
  } {
    unfold decode
    rw [decodeCore.eq_def] <;> rfl
  }

/-- Zero-sized positive arrays decode their actual child once and retain the
    full logical count as a compact uniform value. Empty arrays decode none. -/
theorem decode_array (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (layout : MemoryTypeLayout) (count : Nat)
    (element : Plan) (image : ByteImage) :
    decode model order memory (.array ty layout count element) image = (do
      if image.size != layout.size then
        return ← imageError "Load: image size does not match source layout"
      if count == 0 then return .array (CompactArray.Packed.ofArray #[])
      if element.layout.size == 0 then
        let value ← decodeCore model order memory element ByteImage.empty false false
        return .array (CompactArray.Packed.uniform count value)
      let values ← image.mapBlocks
        (fun part => decodeCore model order memory element part false false)
        element.layout.size count
      pure (.array ⟨count, values⟩)) := by
  trustIrCompilerProof {
    unfold decode
    conv =>
      lhs
      delta decodeCore decodeCore._mutual
      rw [WellFounded.fix_eq]
    rfl
  } {
    unfold decode
    rw [decodeCore.eq_def] <;> rfl
  }

/-- Every logical array length uses the actual typed singleton once; the
    zero-length case retains the decoder's genuine empty representation. -/
theorem decode_fnItem_array (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (element : TyId) (target : FuncId) (count : Nat) :
    decode model order memory
      (.array (.Array element count) ⟨0, 1⟩ count (.fnItem target ⟨0, 1⟩))
      ByteImage.empty =
      (if count == 0 then .ok (.array (CompactArray.Packed.ofArray #[]))
       else .ok (.array (CompactArray.Packed.uniform count (.fnItem target)))) := by
  cases count with
  | zero => rw [decode_array]; rfl
  | succ count =>
    rw [decode_array]
    change (do
      let value ← decodeCore model order memory (.fnItem target ⟨0, 1⟩)
        ByteImage.empty false false
      pure (Value.array (CompactArray.Packed.uniform (count + 1) value))) = _
    rw [decodeCore_fnItem]
    rfl

end TrustIr.AggregateMemory
