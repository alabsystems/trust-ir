-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.AggregatePlans
import TrustIr.State.ArrayEncodingStats

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Padding is absent bytes. Unwritten ranges are separate source-lane facts;
    copying the byte image does not copy these records. -/
structure Image where
  bytes : ByteImage
  unwritten : List (Nat × Nat) := []

def Image.zeroUninit (image : Image) : ByteImage :=
  image.bytes.map (fun byte => some (byte.getD 0))

private def typeError {α : Type} (message : String) : Except SemError α :=
  .error (.typeError message)

private def ub {α : Type} (message : String) : Except SemError α := .error (.ub message)

private def overwrite (image : ByteImage) (offset : Nat)
    (bytes : ByteImage) : Except SemError ByteImage :=
  if offset + bytes.size ≤ image.size then
    .ok ((image.slice 0 offset).append (bytes.append
      (image.slice (offset + bytes.size) (image.size - (offset + bytes.size)))))
  else typeError "memory image: field exceeds source layout"

private def rejectUninit {α : Type} : Except SemError α := ub "memory image: inspecting an unwritten lane"

mutual
  def carriesUnwritten : Value → Bool
    | .uninit => true
    | .aggregate fields | .vector fields | .sequence fields | .set fields => carriesUnwrittenList fields
    | .record fields => carriesUnwrittenRecords fields
    | .closure _ captures => carriesUnwrittenList captures
    | _ => false
  private def carriesUnwrittenList : List Value → Bool
    | [] => false
    | first :: rest => carriesUnwritten first || carriesUnwrittenList rest
  private def carriesUnwrittenRecords : List (String × Value) → Bool
    | [] => false
    | (_, value) :: rest => carriesUnwritten value || carriesUnwrittenRecords rest
end

/-- Top-level Char validity belongs to a load/bind boundary. An aggregate
    transports the raw 32-bit carrier; this checks no recursive Unicode rule. -/
private def encodeLeaf (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (value : Value) : Except SemError (List UInt8) := do
  if value.isPoison then return ← ub "memory image: inspecting poison"
  if value.isUninit then return ← rejectUninit
  if !(fatPtrStoreValueValidFor model ty value) then
    return ← typeError "memory image: noncanonical fat-pointer lanes"
  if ty.isInteger || (match ty with | .Char => true | _ => false) then
    match value with
    | .int width _ =>
      if some width != ty.bitWidthFor model then
        return ← typeError "memory image: integer lane width does not match its source type"
    | _ => return ← typeError "memory image: expected an integer lane"
  encodeMemoryWithFunctions model order ty value

/-- Actual first-match lookup shared by enum encoding and decoding. -/
def discriminantIndex : List Int → Int → Option Nat
  | [], _ => none
  | first :: rest, value =>
    if first == value then some 0 else (discriminantIndex rest value).map Nat.succ

/-- The actual integer normalization consumed by enum encoding. -/
def enumTagValue (tag : EnumTagRepr) (raw : Int) : Int :=
  if tagSigned tag then toSigned raw (tagBits tag) else truncateUnsigned raw (tagBits tag)

theorem enumTagValue_inline (tag : EnumTagRepr) (raw : Int) :
    enumTagValue tag raw =
      (if tagSigned tag then toSigned raw (tagBits tag) else truncateUnsigned raw (tagBits tag)) := rfl

private def enumIndex (info : Enumeration) (value : Value) : Except SemError Nat := do
  let raw ← match value with
    | .int width raw =>
      if width == tagBits info.tag then pure raw
      else typeError "memory image: enum tag width does not match source type"
    | _ =>
      if value.isPoison || value.isUninit then ub "memory image: inspecting enum tag poison"
      else typeError "memory image: enum has no integer tag"
  let discriminant := enumTagValue info.tag raw
  match discriminantIndex info.discriminants discriminant with
  | some index =>
    if ((trustIrListGet? info.uninhabited index)).getD false then typeError "memory image: uninhabited enum variant"
    else pure index
  | none => typeError "memory image: enum tag does not name a variant"

private def tagPrefix (size : Nat) (info : Enumeration) (index : Nat) (tag : Value) :
    Except SemError ByteImage := do
  let empty := ByteImage.fill size none
  match info.encoding with
  | .untagged =>
    if index == 0 then pure empty else typeError "memory image: untagged enum names another variant"
  | .singleInhabited selected =>
    if index == selected then pure empty else typeError "memory image: single-inhabited enum names another variant"
  | .direct offset | .directWithUninhabited offset _ =>
    let raw ← match tag with | .int _ raw => pure raw | _ => typeError "memory image: missing tag"
    overwrite empty offset (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some))
  | .niche untagged start _stop first offset repr =>
    if index == untagged then pure empty
    else
      let value := truncateUnsigned (Int.ofNat first + Int.ofNat index - Int.ofNat start) (tagBits repr)
      overwrite empty offset (ByteImage.ofList ((encodeIntBytes value (tagBits repr / 8)).map some))

private def checkNichePayload (info : Enumeration) (index : Nat)
    (image : ByteImage) : Except SemError Unit := do
  match info.encoding with
  | .niche untagged start stop first offset repr =>
    if index == untagged then
      let modulus := 2 ^ tagBits repr
      let raw := decodeIntBytes ((image.slice offset (tagBits repr / 8)).toList.map (·.getD 0))
      let relative := (raw + modulus - first) % modulus
      if relative ≤ stop - start then
        typeError "memory image: untagged payload occupies a reserved niche"
      else pure ()
    else pure ()
  | _ => pure ()


/-- Encode only visible values, in their logical order. Complete cycles are
    encoded once and repeated only after their actual callbacks succeed. -/
private def encodeArrayLeafRange (encode : Value → Except SemError ByteImage) {size : Nat}
    (leaf : CompactArray.Leaf Value size) (offset count : Nat) : Except SemError ByteImage := do
  if count == 0 then return ByteImage.empty
  match leaf with
  | .nil => pure ByteImage.empty
  | .cons head tail =>
    if offset > 0 then encodeArrayLeafRange encode tail (offset - 1) count else do
      let first ← encode head
      let later ← encodeArrayLeafRange encode tail 0 (count - 1)
      pure (first.append later)

private def encodeArrayRange (encode : Value → Except SemError ByteImage) {size : Nat}
    (tree : CompactArray.Tree Value size) (offset count : Nat) : Except SemError ByteImage := do
  let count := min count (size - offset)
  if count == 0 then return ByteImage.empty
  match tree with
  | .uniform _ value => pure ((← encode value).tile count)
  | .dense _ values => encodeArrayLeafRange encode values offset count
  | .split (size := size) _ left right => do
    let before := min count (size / 2 - offset)
    let first ← encodeArrayRange encode left offset before
    let later ← encodeArrayRange encode right (offset + before - size / 2) (count - before)
    pure (first.append later)
  | .periodic (period := period) unit _ phase _ => do
    let start := (phase + offset) % period
    let before := min count (period - start)
    let remaining := count - before
    let copies := remaining / period
    let first ← encodeArrayRange encode unit start before
    let middle ← if copies == 0 then pure ByteImage.empty else encodeArrayRange encode unit 0 period
    let last ← encodeArrayRange encode unit 0 (remaining % period)
    pure (first.append ((middle.tile copies).append last))

@[nospecialize, trustIrExtern 3 "l___private_TrustIr_Semantics_AggregateImages_0__TrustIr_AggregateMemory_encodeArrayImage(#1, #2, #3)"]
private def encodeArrayImage (encode : Value → Except SemError ByteImage) {size : Nat}
    (tree : CompactArray.Tree Value size) : Except SemError ByteImage :=
  encodeArrayRange encode tree 0 size

mutual
  /-- The flag admits exactly the special tuple/struct Uninit store path.
      Arrays/enums use their regular encoder, as in the reference runtime. -/
  def encode (model : ByteModel) (order : FunctionAddressOrder) (plan : Plan)
      (value : Value) (allowUnwritten : Bool := false) : Except SemError Image := do
    if value.isUninit then
      if allowUnwritten then
        return { bytes := ByteImage.fill plan.layout.size none, unwritten := [(0, plan.layout.size)] }
      else return ← rejectUninit
    match plan with
    | .fnItem target layout =>
      if layout.size != 0 || layout.alignment != 1 then
        return ← typeError "memory image: function item layout is not zero-sized/alignment-one"
      if value.isPoison then return ← ub "memory image: inspecting poison"
      match value with
      | .fnItem actual =>
        if actual == target then pure { bytes := ByteImage.empty }
        else typeError "memory image: function item identity does not match its source type"
      | _ => typeError "memory image: expected a nominal function item"
    | .leaf ty layout =>
      let bytes ← encodeLeaf model order ty value
      if bytes.length != layout.size then return ← typeError "memory image: leaf byte count mismatch"
      pure { bytes := ByteImage.ofList (bytes.map some) }
    | .fields _ layout fields =>
      let values ← match value with
        | .aggregate values => pure values
        | _ => typeError "memory image: expected tuple/struct fields"
      encodeFields model order fields values allowUnwritten { bytes := ByteImage.fill layout.size none }
    | .array _ layout count element =>
      let values ← match value with
        | .array values => pure values
        | _ => typeError "memory image: expected array elements"
      if values.size != count then return ← typeError "memory image: array census mismatch"
      let bytes ← encodeArrayImage (fun value => do
        pure (← encode model order element value false).bytes) values.tree
      if bytes.size != layout.size then return ← typeError "memory image: array byte count mismatch"
      pure { bytes }
    | .enumeration _ layout info variants =>
      let (tag, values) ← match value with
        | .aggregate (tag :: values) => pure (tag, values)
        | _ => typeError "memory image: enum has no tag and fields"
      let index ← enumIndex info tag
      let bytes ← tagPrefix layout.size info index tag
      let image ← encodeVariant model order variants index values { bytes }
      checkNichePayload info index image.bytes
      pure image
  termination_by sizeOf plan
  private def encodeFields (model : ByteModel) (order : FunctionAddressOrder)
      (fields : List (Nat × Plan)) (values : List Value) (allowUnwritten : Bool)
      (image : Image) : Except SemError Image := do
    match fields, values with
    | [], [] => pure image
    | (offset, plan) :: rest, value :: later =>
      let child ← encode model order plan value allowUnwritten
      let bytes ← overwrite image.bytes offset child.bytes
      let unwritten := image.unwritten ++ child.unwritten.map (fun (start, count) => (offset + start, count))
      encodeFields model order rest later allowUnwritten { bytes, unwritten }
    | _, _ => typeError "memory image: field census mismatch"
  termination_by sizeOf fields
  private def encodeVariant (model : ByteModel) (order : FunctionAddressOrder)
      (variants : List (Option (List (Nat × Plan)))) (index : Nat) (values : List Value)
      (image : Image) : Except SemError Image := do
    match variants, index with
    | [], _ => typeError "memory image: variant index out of range"
    | none :: _, 0 => typeError "memory image: uninhabited enum variant"
    | some fields :: _, 0 => encodeFields model order fields values false image
    | _ :: rest, index + 1 => encodeVariant model order rest index values image
  termination_by sizeOf variants
end

private theorem overwrite_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (image bytes : ByteImage) (offset : Nat) :
    ByteImage.BlockResult (fun _ => True) error (overwrite image offset bytes) := by
  unfold overwrite
  split
  · exact True.intro
  · exact typeErrors _

private theorem encode_array_leaf_result (valid : ByteImage → Prop) (error : SemError → Prop)
    (empty : valid ByteImage.empty)
    (append : ∀ left right, valid left → valid right → valid (left.append right))
    (encode : Value → Except SemError ByteImage)
    (safe : ∀ value, ByteImage.BlockResult valid error (encode value))
    {size : Nat} (leaf : CompactArray.Leaf Value size) (offset count : Nat) :
    ByteImage.BlockResult valid error (encodeArrayLeafRange encode leaf offset count) := by
  induction leaf generalizing offset count with
  | nil =>
    rw [encodeArrayLeafRange]
    dsimp only
    split <;> exact empty
  | cons head tail ih =>
    rw [encodeArrayLeafRange]
    dsimp only
    split
    · exact empty
    · simp only [pure_bind]
      split
      · exact ih _ _
      · try simp only [pure_bind]
        apply ByteImage.BlockResult.bind valid valid error _ _ (safe head)
        intro first firstValid
        apply ByteImage.BlockResult.bind valid valid error _ _ (ih _ _)
        intro later laterValid
        exact append first later firstValid laterValid

/-- The actual compact-array fold preserves any byte property closed under
empty images, concatenation and repetition, and propagates callback errors. -/
private theorem encode_array_result (valid : ByteImage → Prop) (error : SemError → Prop)
    (empty : valid ByteImage.empty)
    (append : ∀ left right, valid left → valid right → valid (left.append right))
    (tile : ∀ unit count, valid unit → valid (unit.tile count))
    (encode : Value → Except SemError ByteImage)
    (safe : ∀ value, ByteImage.BlockResult valid error (encode value))
    {size : Nat} (tree : CompactArray.Tree Value size) (offset count : Nat) :
    ByteImage.BlockResult valid error (encodeArrayRange encode tree offset count) := by
  induction tree generalizing offset count with
  | uniform size value =>
    rw [encodeArrayRange]
    dsimp only
    split
    · exact empty
    · simp only [pure_bind]
      apply ByteImage.BlockResult.bind valid valid error _ _ (safe value)
      intro unit unitValid
      exact tile unit _ unitValid
  | dense size values =>
    rw [encodeArrayRange]
    dsimp only
    split
    · exact empty
    · simp only [pure_bind]
      exact encode_array_leaf_result valid error empty append encode safe values _ _
  | split positive left right leftIH rightIH =>
    rw [encodeArrayRange]
    dsimp only
    split
    · exact empty
    · simp only [pure_bind]
      apply ByteImage.BlockResult.bind valid valid error _ _ (leftIH _ _)
      intro first firstValid
      apply ByteImage.BlockResult.bind valid valid error _ _ (rightIH _ _)
      intro later laterValid
      exact append first later firstValid laterValid
  | periodic unit positive phase count ih =>
    rw [encodeArrayRange]
    dsimp only
    split
    · exact empty
    · simp only [pure_bind]
      apply ByteImage.BlockResult.bind valid valid error _ _ (ih _ _)
      intro first firstValid
      dsimp only
      split
      · try simp only [pure_bind]
        apply ByteImage.BlockResult.bind valid valid error _ _ (ih _ _)
        intro last lastValid
        exact append first _ firstValid (append _ last (tile _ _ empty) lastValid)
      · try simp only [pure_bind]
        apply ByteImage.BlockResult.bind valid valid error _ _ (ih _ _)
        intro middle middleValid
        apply ByteImage.BlockResult.bind valid valid error _ _ (ih _ _)
        intro last lastValid
        exact append first _ firstValid (append _ last (tile _ _ middleValid) lastValid)

/-- Successful execution of the actual compact-array encoder. -/
def ArrayImageEncoded (encode : Value → Except SemError ByteImage) {size : Nat}
    (tree : CompactArray.Tree Value size) (image : ByteImage) : Prop :=
  encodeArrayImage encode tree = .ok image

/-- Any property closed under the encoder's byte operations is retained by
all compact representations. Only successful actual callbacks need satisfy it. -/
theorem ArrayImageEncoded.preserves (valid : ByteImage → Prop)
    (empty : valid ByteImage.empty)
    (append : ∀ left right, valid left → valid right → valid (left.append right))
    (tile : ∀ unit count, valid unit → valid (unit.tile count))
    (encode : Value → Except SemError ByteImage)
    (safe : ∀ value bytes, encode value = .ok bytes → valid bytes)
    {size : Nat} (tree : CompactArray.Tree Value size) (image : ByteImage)
    (run : ArrayImageEncoded encode tree image) : valid image := by
  have callbacks : ∀ value, ByteImage.BlockResult valid (fun _ => True) (encode value) := by
    intro value
    cases result : encode value with
    | error _ => exact True.intro
    | ok bytes => exact safe value bytes result
  have result := encode_array_result valid (fun _ => True) empty append tile encode callbacks tree 0 size
  change encodeArrayRange encode tree 0 size = .ok image at run
  rw [run] at result
  exact result

private theorem encode_leaf_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
    (scalar : ∀ model order ty value, ByteImage.BlockResult (fun _ => True) error (encodeMemoryWithFunctions model order ty value))
    (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (value : Value) :
    ByteImage.BlockResult (fun _ => True) error (encodeLeaf model order ty value) := by
  unfold encodeLeaf
  repeat' first
    | (solve | exact scalar _ _ _ _)
    | (solve | exact True.intro)
    | (solve | exact typeErrors _)
    | (solve | exact undefined _)
    | (simp only [typeError,ub,rejectUninit,Except.bind,pure_bind])
    | split
    | (dsimp only; split)

private theorem enum_index_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
    (info : Enumeration) (value : Value) :
    ByteImage.BlockResult (fun _ => True) error (enumIndex info value) := by
  unfold enumIndex
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact typeErrors _)
    | (solve | exact undefined _)
    | (simp only [typeError,ub,Except.bind,pure_bind])
    | split
    | (dsimp only; split)

private theorem tag_prefix_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (size : Nat)
    (info : Enumeration) (index : Nat) (tag : Value) :
    ByteImage.BlockResult (fun _ => True) error (tagPrefix size info index tag) := by
  unfold tagPrefix
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact typeErrors _)
    | (solve | exact overwrite_errors error typeErrors _ _ _)
    | (simp only [typeError,Except.bind,pure_bind])
    | split
    | (dsimp only; split)

private theorem niche_payload_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message)) (info : Enumeration) (index : Nat) (image : ByteImage) :
    ByteImage.BlockResult (fun _ => True) error (checkNichePayload info index image) := by
  unfold checkNichePayload
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact typeErrors _)
    | split
    | (dsimp only; split)

mutual
  /-- Original aggregate encoding permits only callback errors and the actual
  type/UB refusals, including every logical compact-array representation. -/
  theorem encode_errors (error : SemError → Prop)
      (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
      (scalar : ∀ model order ty value, ByteImage.BlockResult (fun _ => True) error (encodeMemoryWithFunctions model order ty value))
      (model : ByteModel) (order : FunctionAddressOrder) (plan : Plan) (value : Value) (allowUnwritten : Bool) :
      ByteImage.BlockResult (fun _ => True) error (encode model order plan value allowUnwritten) := by
    cases plan <;> trustIrCompilerProof { rw [encode] } { rw [encode.eq_def] }
    all_goals repeat' first
      | (solve | exact True.intro)
      | (solve | exact typeErrors _)
      | (solve | exact undefined _)
      | (simp only [typeError,ub,rejectUninit,Except.bind,pure_bind])
      | (dsimp only [encodeArrayImage])
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
          (encode_leaf_errors error typeErrors undefined scalar _ _ _ _) ?_; intro bytes _)
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
          (enum_index_errors error typeErrors undefined _ _) ?_; intro index _)
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
          (tag_prefix_errors error typeErrors _ _ _ _) ?_; intro bytes _)
      | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
          (niche_payload_errors error typeErrors _ _ _) ?_; intro unit _)
      | (with_reducible refine (encode_fields_errors error typeErrors undefined scalar _ _ _ _ _ _))
      | (with_reducible refine (ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
          (encode_variant_errors error typeErrors undefined scalar _ _ _ _ _ _) ?_); intro image _)
      | split
      | (dsimp only; split)
    all_goals
      refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
        (encode_array_result (fun _ => True) error True.intro
          (fun _ _ _ _ => True.intro) (fun _ _ _ => True.intro) _ ?_ _ _ _) ?_
      · intro child
        with_reducible refine (ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
          (encode_errors error typeErrors undefined scalar _ _ _ child false) ?_)
        intro image _
        exact True.intro
      · intro bytes _
        split
        · exact typeErrors _
        · exact True.intro
  termination_by sizeOf plan

  private theorem encode_fields_errors (error : SemError → Prop)
      (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
      (scalar : ∀ model order ty value, ByteImage.BlockResult (fun _ => True) error (encodeMemoryWithFunctions model order ty value))
      (model : ByteModel) (order : FunctionAddressOrder) (fields : List (Nat × Plan))
      (values : List Value) (allowUnwritten : Bool) (image : Image) :
      ByteImage.BlockResult (fun _ => True) error (encodeFields model order fields values allowUnwritten image) := by
    cases fields with
    | nil =>
      cases values <;> rw [encodeFields]
      all_goals first | exact True.intro | exact typeErrors _ | simp
    | cons pair rest =>
      obtain ⟨offset,child⟩ := pair
      cases values <;> rw [encodeFields]
      all_goals repeat' first
        | (solve | simp)
        | (solve | exact True.intro)
        | (solve | exact typeErrors _)
        | (simp only [typeError,Except.bind,pure_bind])
        | (with_reducible refine (ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
            (encode_errors error typeErrors undefined scalar _ _ _ _ _) ?_); intro child _)
        | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
            (overwrite_errors error typeErrors _ _ _) ?_; intro bytes _)
        | (with_reducible exact encode_fields_errors error typeErrors undefined scalar _ _ _ _ _ _)
        | split
        | (dsimp only; split)
  termination_by sizeOf fields

  private theorem encode_variant_errors (error : SemError → Prop)
      (typeErrors : ∀ message, error (.typeError message)) (undefined : ∀ message, error (.ub message))
      (scalar : ∀ model order ty value, ByteImage.BlockResult (fun _ => True) error (encodeMemoryWithFunctions model order ty value))
      (model : ByteModel) (order : FunctionAddressOrder) (variants : List (Option (List (Nat × Plan))))
      (index : Nat) (values : List Value) (image : Image) :
      ByteImage.BlockResult (fun _ => True) error (encodeVariant model order variants index values image) := by
    cases variants with
    | nil =>
      trustIrCompilerProof { exact typeErrors _ } { rw [encodeVariant]; exact typeErrors _ }
    | cons head tail =>
      cases head <;> cases index <;> rw [encodeVariant]
      all_goals first
        | exact typeErrors _
        | with_reducible exact encode_fields_errors error typeErrors undefined scalar _ _ _ _ _ _
        | with_reducible exact encode_variant_errors error typeErrors undefined scalar _ _ _ _ _ _
  termination_by sizeOf variants
end

/-- Selection by the actual encoder, including its width and live-flag guards. -/
def EnumEncodingSelects (info : Enumeration) (tag : Value) (position : Nat) : Prop :=
  enumIndex info tag = .ok position

/-- Exact rejection by the actual typed-value encoder selector. -/
def EnumEncodingRejects (info : Enumeration) (tag : Value) (error : SemError) : Prop :=
  enumIndex info tag = .error error

theorem EnumEncodingSelects.of_lookup (info : Enumeration) (width : Nat) (raw : Int) (position : Nat)
    (sized : width = tagBits info.tag)
    (selected : discriminantIndex info.discriminants (enumTagValue info.tag raw) = some position)
    (live : (trustIrListGet? info.uninhabited position) = some false) :
    EnumEncodingSelects info (.int width raw) position := by
  unfold EnumEncodingSelects enumIndex
  simp [sized,selected,live,Pure.pure,Except.pure,Bind.bind,Except.bind]

/-- An exact retained byte window, including its extent. -/
def ByteLane (image : ByteImage) (offset : Nat) (bytes : ByteImage) : Prop :=
  offset + bytes.size ≤ image.size ∧ ∀ index, index < bytes.size → image.get (offset + index) = bytes.get index

/-- Concatenation retains a lane in its left image without changing its offset. -/
theorem ByteLane.append_left {left right bytes : ByteImage} {offset : Nat}
    (lane : ByteLane left offset bytes) : ByteLane (left.append right) offset bytes := by
  refine ⟨by rw [ByteImage.size_append]; have bound := lane.1; omega,?_⟩
  intro index inside
  rw [ByteImage.get_append,if_pos (by have bound := lane.1; omega)]
  exact lane.2 index inside

/-- Concatenation shifts a right-image lane by the complete left extent. -/
theorem ByteLane.append_right {left right bytes : ByteImage} {offset : Nat}
    (lane : ByteLane right offset bytes) :
    ByteLane (left.append right) (left.size + offset) bytes := by
  refine ⟨by rw [ByteImage.size_append]; have bound := lane.1; omega,?_⟩
  intro index inside
  rw [ByteImage.get_append,if_neg (by omega)]
  have shifted : left.size + offset + index - left.size = offset + index := by omega
  rw [shifted]
  exact lane.2 index inside

private theorem encode_array_leaf_slots (callback : Value → Except SemError ByteImage)
    (stride : Nat) (safe : ∀ value bytes, callback value = .ok bytes → bytes.size = stride)
    {size : Nat} (leaf : CompactArray.Leaf Value size) (offset count : Nat)
    (bounded : count ≤ size - offset) (image : ByteImage)
    (run : encodeArrayLeafRange callback leaf offset count = .ok image) :
    image.size = count * stride ∧ ∀ slot value, slot < count →
      leaf.get? (offset + slot) = some value →
      ∃ child, callback value = .ok child ∧ child.size = stride ∧
        ByteLane image (slot * stride) child := by
  induction leaf generalizing offset count image with
  | nil =>
    have zero : count = 0 := by omega
    subst count
    simp [encodeArrayLeafRange,Pure.pure,Except.pure] at run
    cases run
    refine ⟨by simp [ByteImage.empty],?_⟩
    intro slot value inside
    omega
  | @cons size head tail ih =>
    by_cases zero : count = 0
    · subst count
      simp [encodeArrayLeafRange,Pure.pure,Except.pure] at run
      cases run
      refine ⟨by simp [ByteImage.empty],?_⟩
      intro slot value inside
      omega
    by_cases skipped : 0 < offset
    · have reduced : encodeArrayLeafRange callback tail (offset - 1) count = .ok image := by
        simpa [encodeArrayLeafRange,zero,skipped] using run
      obtain ⟨extent,slots⟩ := ih (offset - 1) count (by omega) image reduced
      refine ⟨extent,?_⟩
      intro slot value inside found
      apply slots slot value inside
      have position : offset + slot = (offset - 1 + slot) + 1 := by omega
      rw [position] at found
      exact found
    · have atStart : offset = 0 := by omega
      subst offset
      cases firstRun : callback head with
      | error failure =>
        simp [encodeArrayLeafRange,zero,firstRun,Bind.bind,Except.bind] at run
        cases run
      | ok first =>
        cases laterRun : encodeArrayLeafRange callback tail 0 (count - 1) with
        | error failure =>
          simp [encodeArrayLeafRange,zero,firstRun,laterRun,Bind.bind,Except.bind] at run
          cases run
        | ok later =>
          simp [encodeArrayLeafRange,zero,firstRun,laterRun,Bind.bind,Except.bind,
            Pure.pure,Except.pure] at run
          cases run
          have firstSize := safe head first firstRun
          obtain ⟨laterSize,laterSlots⟩ := ih 0 (count - 1) (by omega) later laterRun
          refine ⟨?_,?_⟩
          · rw [ByteImage.size_append,firstSize,laterSize]
            have counts : count = (count - 1) + 1 := by omega
            have equation := Nat.add_mul (count - 1) 1 stride
            rw [← counts,Nat.one_mul] at equation
            omega
          · intro slot value inside found
            cases slot with
            | zero =>
              simp only [Nat.zero_add,CompactArray.Leaf.get?,Option.some.injEq] at found
              subst value
              refine ⟨first,firstRun,firstSize,?_⟩
              have lane : ByteLane first 0 first := ⟨by omega,by intro index _; simp⟩
              simpa using (lane.append_left (right := later))
            | succ slot =>
              obtain ⟨child,encoded,childSize,lane⟩ := laterSlots slot value (by omega) found
              refine ⟨child,encoded,childSize,?_⟩
              have placed := lane.append_right (left := first)
              simpa only [firstSize,Nat.succ_mul,Nat.add_comm] using placed

private theorem encode_array_range_slots
    (repeatLane : ∀ (unit bytes : ByteImage) (offset copies copy : Nat),
      ByteLane unit offset bytes → copy < copies →
        ByteLane (unit.tile copies) (copy * unit.size + offset) bytes)
    (callback : Value → Except SemError ByteImage) (stride : Nat)
    (safe : ∀ value bytes, callback value = .ok bytes → bytes.size = stride)
    {size : Nat} (tree : CompactArray.Tree Value size) (offset count : Nat)
    (bounded : count ≤ size - offset) (image : ByteImage)
    (run : encodeArrayRange callback tree offset count = .ok image) :
    image.size = count * stride ∧ ∀ slot value, slot < count →
      tree.get? (offset + slot) = some value →
      ∃ child, callback value = .ok child ∧ child.size = stride ∧
        ByteLane image (slot * stride) child := by
  induction tree generalizing offset count image with
  | uniform size value =>
    by_cases zero : count = 0
    · subst count
      simp [encodeArrayRange,Pure.pure,Except.pure] at run
      cases run
      exact ⟨by simp [ByteImage.empty],by intro slot value inside; omega⟩
    cases encoded : callback value with
    | error failure =>
      simp [encodeArrayRange,Nat.min_eq_left bounded,zero,encoded,
        Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    | ok child =>
      simp [encodeArrayRange,Nat.min_eq_left bounded,zero,encoded,
        Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases run
      have childSize := safe value child encoded
      refine ⟨by rw [ByteImage.size_tile,childSize,Nat.mul_comm],?_⟩
      intro slot selected inside found
      have lookupInside : offset + slot < size := by omega
      simp only [CompactArray.Tree.get?,if_pos lookupInside,Option.some.injEq] at found
      subst selected
      refine ⟨child,encoded,childSize,?_⟩
      have own : ByteLane child 0 child := ⟨by omega,by intro index _; simp⟩
      simpa only [childSize,Nat.add_zero] using repeatLane child child 0 count slot own inside
  | dense small values =>
    have folded : encodeArrayLeafRange callback values offset count = .ok image := by
      by_cases zero : count = 0
      · subst count
        cases values <;> simpa [encodeArrayRange,encodeArrayLeafRange,Pure.pure,Except.pure] using run
      · simpa [encodeArrayRange,Nat.min_eq_left bounded,zero] using run
    exact encode_array_leaf_slots callback stride safe values offset count bounded image folded
  | @split size large left right ihl ihr =>
    by_cases zero : count = 0
    · subst count
      simp [encodeArrayRange,Pure.pure,Except.pure] at run
      cases run
      exact ⟨by simp [ByteImage.empty],by intro slot value inside; omega⟩
    let before := min count (size / 2 - offset)
    have halfBound : size / 2 ≤ size := Nat.div_le_self size 2
    cases firstRun : encodeArrayRange callback left offset before with
    | error failure =>
      simp [encodeArrayRange,Nat.min_eq_left bounded,zero,before,firstRun,
        Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    | ok first =>
      cases laterRun : encodeArrayRange callback right (offset + before - size / 2) (count - before) with
      | error failure =>
        simp [encodeArrayRange,Nat.min_eq_left bounded,zero,before,firstRun,laterRun,
          Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      | ok later =>
        simp [encodeArrayRange,Nat.min_eq_left bounded,zero,before,firstRun,laterRun,
          Bind.bind,Except.bind,Pure.pure,Except.pure] at run
        cases run
        have beforeBound : before ≤ size / 2 - offset := Nat.min_le_right _ _
        have beforeCount : before ≤ count := Nat.min_le_left _ _
        obtain ⟨firstSize,firstSlots⟩ := ihl offset before beforeBound first firstRun
        obtain ⟨laterSize,laterSlots⟩ := ihr (offset + before - size / 2) (count - before)
          (by dsimp [before]; omega) later laterRun
        refine ⟨?_,?_⟩
        · rw [ByteImage.size_append,firstSize,laterSize,← Nat.add_mul]
          congr 1
          omega
        · intro slot value inside found
          by_cases early : slot < before
          · have inLeft : offset + slot < size / 2 := by omega
            simp only [CompactArray.Tree.get?,if_pos inLeft] at found
            obtain ⟨child,encoded,childSize,lane⟩ := firstSlots slot value early found
            exact ⟨child,encoded,childSize,lane.append_left⟩
          · have inRight : ¬ offset + slot < size / 2 := by dsimp [before] at early; omega
            simp only [CompactArray.Tree.get?,if_neg inRight] at found
            have position : offset + before - size / 2 + (slot - before) = offset + slot - size / 2 := by omega
            obtain ⟨child,encoded,childSize,lane⟩ := laterSlots (slot - before) value (by omega)
              (by simpa only [position] using found)
            refine ⟨child,encoded,childSize,?_⟩
            have placed := lane.append_right (left := first)
            have bytePosition : first.size + (slot - before) * stride = slot * stride := by
              rw [firstSize,← Nat.add_mul]
              congr 1
              omega
            simpa only [bytePosition] using placed
  | @periodic period unit positive phase size ih =>
    by_cases zero : count = 0
    · subst count
      simp [encodeArrayRange,Pure.pure,Except.pure] at run
      cases run
      exact ⟨by simp [ByteImage.empty],by intro slot value inside; omega⟩
    let start := (phase + offset) % period
    let before := min count (period - start)
    let remaining := count - before
    let copies := remaining / period
    have startBound : start < period := Nat.mod_lt _ positive
    have beforeBound : before ≤ period - start := Nat.min_le_right _ _
    have beforeCount : before ≤ count := Nat.min_le_left _ _
    have remainderBound : remaining % period < period := Nat.mod_lt _ positive
    have decomposition : count = before + copies * period + remaining % period := by
      have h := Nat.mod_add_div remaining period
      rw [Nat.mul_comm period (remaining / period)] at h
      dsimp only [remaining,copies] at *
      omega
    rw [encodeArrayRange] at run
    dsimp only at run
    simp only [Nat.min_eq_left bounded,beq_iff_eq,zero,ite_false,pure_bind] at run
    have distribute (condition : Prop) [Decidable condition]
        (yes no : Except SemError ByteImage) (next : ByteImage → Except SemError ByteImage) :
        ((if condition then yes else no) >>= next) =
          (if condition then yes >>= next else no >>= next) := by
      split <;> rfl
    have normalized :
        (encodeArrayRange callback unit start before >>= fun first =>
          ((if copies = 0 then pure ByteImage.empty else encodeArrayRange callback unit 0 period) >>= fun middle =>
            (encodeArrayRange callback unit 0 (remaining % period) >>= fun last =>
              pure (first.append ((middle.tile copies).append last))))) = .ok image := by
      simp only [distribute]
      exact run
    cases firstRun : encodeArrayRange callback unit start before with
    | error failure =>
      simp only [firstRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at normalized <;> cases normalized
    | ok first =>
      cases middleRun : (if copies = 0 then pure ByteImage.empty else encodeArrayRange callback unit 0 period) with
      | error failure =>
        rw [firstRun] at normalized
        dsimp only [Bind.bind,Except.bind] at normalized
        rw [middleRun] at normalized
        cases normalized
      | ok middle =>
        cases lastRun : encodeArrayRange callback unit 0 (remaining % period) with
        | error failure =>
          rw [firstRun] at normalized
          dsimp only [Bind.bind,Except.bind] at normalized
          rw [middleRun] at normalized
          dsimp only [Bind.bind,Except.bind] at normalized
          rw [lastRun] at normalized
          cases normalized
        | ok last =>
          rw [firstRun] at normalized
          dsimp only [Bind.bind,Except.bind] at normalized
          rw [middleRun] at normalized
          dsimp only [Bind.bind,Except.bind] at normalized
          rw [lastRun] at normalized
          cases normalized
          obtain ⟨firstSize,firstSlots⟩ := ih start before beforeBound first firstRun
          obtain ⟨lastSize,lastSlots⟩ := ih 0 (remaining % period) (by omega) last lastRun
          have middleSpec : (middle.tile copies).size = (copies * period) * stride ∧
              ∀ slot value, slot < copies * period → unit.get? (slot % period) = some value →
                ∃ child, callback value = .ok child ∧ child.size = stride ∧
                  ByteLane (middle.tile copies) (slot * stride) child := by
            by_cases noCopies : copies = 0
            · rw [noCopies,ByteImage.size_tile]
              simp only [Nat.mul_zero,Nat.zero_mul]
              exact ⟨True.intro,by intro slot value inside; omega⟩
            have folded : encodeArrayRange callback unit 0 period = .ok middle := by
              simpa [noCopies] using middleRun
            obtain ⟨middleSize,middleSlots⟩ := ih 0 period (by omega) middle folded
            refine ⟨?_,?_⟩
            · rw [ByteImage.size_tile,middleSize]
              simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
            · intro slot value inside found
              obtain ⟨child,encoded,childSize,lane⟩ := middleSlots (slot % period) value
                (Nat.mod_lt _ positive) (by simpa only [Nat.zero_add] using found)
              have copyInside : slot / period < copies := by
                apply (Nat.div_lt_iff_lt_mul positive).2
                simpa only [Nat.mul_comm] using inside
              have placed := repeatLane middle child ((slot % period) * stride) copies
                (slot / period) lane copyInside
              have position : slot / period * middle.size + slot % period * stride = slot * stride := by
                rw [middleSize,← Nat.mul_assoc,← Nat.add_mul]
                congr 1
                have h := Nat.mod_add_div slot period
                rw [Nat.mul_comm period (slot / period)] at h
                omega
              exact ⟨child,encoded,childSize,by simpa only [position] using placed⟩
          refine ⟨?_,?_⟩
          · rw [ByteImage.size_append,ByteImage.size_append,firstSize,middleSpec.1,lastSize,
              ← Nat.add_mul,← Nat.add_mul]
            congr 1
            omega
          · intro slot value inside found
            have inSource : offset + slot < size := by omega
            simp only [CompactArray.Tree.get?,if_pos inSource] at found
            have phaseAt : (phase + (offset + slot)) % period = (start + slot) % period := by
              dsimp only [start]
              rw [← Nat.add_assoc,Nat.add_mod (phase + offset) slot,
                Nat.add_mod ((phase + offset) % period) slot,Nat.mod_mod]
            rw [phaseAt] at found
            by_cases early : slot < before
            · have inUnit : start + slot < period := by omega
              rw [Nat.mod_eq_of_lt inUnit] at found
              obtain ⟨child,encoded,childSize,lane⟩ := firstSlots slot value early found
              exact ⟨child,encoded,childSize,lane.append_left⟩
            have wrapped : start + before = period := by dsimp [before] at early; omega
            by_cases inMiddle : slot - before < copies * period
            · have phaseMiddle : (start + slot) % period = (slot - before) % period := by
                have position : start + slot = period + (slot - before) := by omega
                rw [position,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod]
              rw [phaseMiddle] at found
              obtain ⟨child,encoded,childSize,lane⟩ := middleSpec.2 (slot - before) value inMiddle found
              have placed := lane.append_left (right := last) |>.append_right (left := first)
              have position : first.size + (slot - before) * stride = slot * stride := by
                rw [firstSize,← Nat.add_mul]
                congr 1
                omega
              exact ⟨child,encoded,childSize,by simpa only [position] using placed⟩
            · let tailSlot := slot - before - copies * period
              have tailBound : tailSlot < remaining % period := by dsimp [tailSlot]; omega
              have phaseLast : (start + slot) % period = tailSlot := by
                have position : start + slot = (copies + 1) * period + tailSlot := by
                  rw [Nat.add_mul,Nat.one_mul]
                  dsimp only [tailSlot]
                  omega
                rw [position,Nat.mul_comm (copies + 1) period,Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega)]
              rw [phaseLast] at found
              obtain ⟨child,encoded,childSize,lane⟩ := lastSlots tailSlot value tailBound
                (by simpa only [Nat.zero_add] using found)
              have placed := lane.append_right (left := middle.tile copies) |>.append_right (left := first)
              have position : first.size + ((middle.tile copies).size + tailSlot * stride) = slot * stride := by
                rw [firstSize,middleSpec.1,← Nat.add_mul,← Nat.add_mul]
                congr 1
                dsimp only [tailSlot]
                omega
              exact ⟨child,encoded,childSize,by simpa only [position] using placed⟩

/-- Indexed correspondence for every compact representation, provided the
    byte representation's actual repetition operation preserves retained lanes. -/
theorem ArrayImageEncoded.slots_of_repetition
    (repeatLane : ∀ (unit bytes : ByteImage) (offset copies copy : Nat),
      ByteLane unit offset bytes → copy < copies →
        ByteLane (unit.tile copies) (copy * unit.size + offset) bytes)
    (callback : Value → Except SemError ByteImage) (stride : Nat)
    (safe : ∀ value bytes, callback value = .ok bytes → bytes.size = stride)
    {size : Nat} (tree : CompactArray.Tree Value size) (image : ByteImage)
    (run : ArrayImageEncoded callback tree image) :
    image.size = size * stride ∧ ∀ slot value, slot < size → tree.get? slot = some value →
      ∃ child, callback value = .ok child ∧ child.size = stride ∧
        ByteLane image (slot * stride) child := by
  simpa only [Nat.zero_add] using
    encode_array_range_slots repeatLane callback stride safe tree 0 size (by omega) image run

/-- A successful dense-array fold gives the actual callback image at each
    logical slot, including zero-width children. No byte-sidecar premise is used. -/
theorem ArrayImageEncoded.dense_slots (callback : Value → Except SemError ByteImage)
    (stride : Nat) (safe : ∀ value bytes, callback value = .ok bytes → bytes.size = stride)
    {size : Nat} (small : size ≤ 16) (values : CompactArray.Leaf Value size)
    (image : ByteImage) (run : ArrayImageEncoded callback (.dense small values) image) :
    image.size = size * stride ∧ ∀ slot value, slot < size →
      values.get? slot = some value →
      ∃ child, callback value = .ok child ∧ child.size = stride ∧
        ByteLane image (slot * stride) child := by
  have folded : encodeArrayLeafRange callback values 0 size = .ok image := by
    by_cases empty : size = 0
    · subst size
      cases values
      simpa [ArrayImageEncoded,encodeArrayImage,encodeArrayRange,encodeArrayLeafRange] using run
    · simpa [ArrayImageEncoded,encodeArrayImage,encodeArrayRange,empty] using run
  simpa only [Nat.zero_add] using
    encode_array_leaf_slots callback stride safe values 0 size (by omega) image folded

/-- A nonempty uniform fold executes its actual element callback once before
    tiling the resulting image. Even zero-byte elements retain that callback. -/
theorem ArrayImageEncoded.uniform_image (callback : Value → Except SemError ByteImage)
    (count : Nat) (value : Value) (image : ByteImage) (nonempty : 0 < count)
    (run : ArrayImageEncoded callback (.uniform count value) image) :
    ∃ child, callback value = .ok child ∧ image = child.tile count := by
  cases encoded : callback value with
  | error failure =>
    simp [ArrayImageEncoded,encodeArrayImage,encodeArrayRange,Nat.ne_of_gt nonempty,
      encoded,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  | ok child =>
    refine ⟨child,rfl,?_⟩
    simpa [ArrayImageEncoded,encodeArrayImage,encodeArrayRange,Nat.ne_of_gt nonempty,
      encoded,Bind.bind,Except.bind,Pure.pure,Except.pure] using run.symm

/-- Actual image overwrite, rather than a claimed sidecar byte table. -/
def ImageOverwrite (before : ByteImage) (offset : Nat) (bytes after : ByteImage) : Prop :=
  overwrite before offset bytes = .ok after

private theorem overwrite_spec (before : ByteImage) (offset : Nat) (bytes after : ByteImage)
    (run : ImageOverwrite before offset bytes after) :
    after.size = before.size ∧ ByteLane after offset bytes ∧
      ∀ index, index < before.size → (index < offset ∨ offset + bytes.size ≤ index) → after.get index = before.get index := by
  unfold ImageOverwrite overwrite at run
  split at run
  · rename_i fits
    cases run
    have prefixSize : (before.slice 0 offset).size = offset := by
      rw [ByteImage.size_slice]; simp only [Nat.sub_zero]; omega
    have suffixSize : (before.slice (offset + bytes.size) (before.size - (offset + bytes.size))).size =
        before.size - (offset + bytes.size) := by rw [ByteImage.size_slice]; omega
    have size : ((before.slice 0 offset).append (bytes.append
        (before.slice (offset + bytes.size) (before.size - (offset + bytes.size))))).size = before.size := by
      rw [ByteImage.size_append,ByteImage.size_append,prefixSize,suffixSize]; omega
    refine ⟨size,⟨by rw [size]; exact fits,?_⟩,?_⟩
    · intro index inside
      rw [ByteImage.get_append,prefixSize,if_neg (by omega),Nat.add_sub_cancel_left,
        ByteImage.get_append,if_pos inside]
    · intro index inside outside
      rw [ByteImage.get_append,prefixSize]
      rcases outside with prior | later
      · rw [if_pos prior,ByteImage.get_slice before 0 offset index prior (by omega)]
        simp only [Nat.zero_add]
      · rw [if_neg (by omega),ByteImage.get_append,if_neg (by omega)]
        rw [ByteImage.get_slice before (offset + bytes.size) (before.size - (offset + bytes.size))
          (index - offset - bytes.size) (by omega) (by omega)]
        congr 1; omega
  · cases run

theorem ImageOverwrite.extent {before bytes after : ByteImage} {offset : Nat}
    (run : ImageOverwrite before offset bytes after) : after.size = before.size := (overwrite_spec _ _ _ _ run).1

theorem ImageOverwrite.lane {before bytes after : ByteImage} {offset : Nat}
    (run : ImageOverwrite before offset bytes after) : ByteLane after offset bytes := (overwrite_spec _ _ _ _ run).2.1

theorem ImageOverwrite.outside {before bytes after : ByteImage} {offset : Nat}
    (run : ImageOverwrite before offset bytes after) (index : Nat) (inside : index < before.size)
    (outside : index < offset ∨ offset + bytes.size ≤ index) : after.get index = before.get index :=
  (overwrite_spec _ _ _ _ run).2.2 index inside outside

/-- The actual enum prefix builder. Payload writes are a separate transition. -/
def EnumTagPrefix (size : Nat) (info : Enumeration) (position : Nat) (tag : Value) (image : ByteImage) : Prop :=
  tagPrefix size info position tag = .ok image

/-- Both direct encodings use the same actual initialized tag lane.
Reserved source storage profiles do not alter the tag byte semantics. -/
def DirectEncodingAt (encoding : EnumTagEncoding) (offset : Nat) : Prop :=
  encoding = .direct offset ∨ ∃ profiles, encoding = .directWithUninhabited offset profiles

theorem EnumTagPrefix.direct_encoding_lane (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (image : ByteImage) (offset : Nat) (encoding : DirectEncodingAt info.encoding offset)
    (run : EnumTagPrefix size info position (.int width raw) image) :
    ByteLane image offset (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)) := by
  rcases encoding with encoding | ⟨profiles, encoding⟩
  all_goals
    unfold EnumTagPrefix tagPrefix at run
    rw [encoding] at run
    change ImageOverwrite (ByteImage.fill size none) offset _ image at run
    exact run.lane

theorem EnumTagPrefix.direct_lane (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (image : ByteImage) (offset : Nat) (encoding : info.encoding = .direct offset)
    (run : EnumTagPrefix size info position (.int width raw) image) :
    ByteLane image offset (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)) := by
  exact EnumTagPrefix.direct_encoding_lane size info position width raw image offset (Or.inl encoding) run

theorem EnumTagPrefix.profiled_direct_lane (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (image : ByteImage) (offset : Nat) {profiles : List UninhabitedVariantLayout} (encoding : info.encoding = .directWithUninhabited offset profiles)
    (run : EnumTagPrefix size info position (.int width raw) image) :
    ByteLane image offset (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)) := by
  exact EnumTagPrefix.direct_encoding_lane size info position width raw image offset (Or.inr ⟨profiles, encoding⟩) run


theorem EnumTagPrefix.direct_encoding_exists (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (offset : Nat) (encoding : DirectEncodingAt info.encoding offset)
    (fits : offset + (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)).size ≤ size) :
    ∃ image, EnumTagPrefix size info position (.int width raw) image := by
  rcases encoding with encoding | ⟨profiles, encoding⟩
  all_goals
    unfold EnumTagPrefix tagPrefix
    rw [encoding]
    change ∃ image, overwrite (ByteImage.fill size none) offset _ = .ok image
    unfold overwrite
    simp only [ByteImage.size_fill]
    rw [if_pos fits]
    exact ⟨_,rfl⟩

theorem EnumTagPrefix.direct_exists (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (offset : Nat) (encoding : info.encoding = .direct offset)
    (fits : offset + (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)).size ≤ size) :
    ∃ image, EnumTagPrefix size info position (.int width raw) image := by
  exact EnumTagPrefix.direct_encoding_exists size info position width raw offset (Or.inl encoding) fits

theorem EnumTagPrefix.profiled_direct_exists (size : Nat) (info : Enumeration) (position width : Nat) (raw : Int)
    (offset : Nat) {profiles : List UninhabitedVariantLayout} (encoding : info.encoding = .directWithUninhabited offset profiles)
    (fits : offset + (ByteImage.ofList ((encodeIntBytes raw (tagBits info.tag / 8)).map some)).size ≤ size) :
    ∃ image, EnumTagPrefix size info position (.int width raw) image := by
  exact EnumTagPrefix.direct_encoding_exists size info position width raw offset (Or.inr ⟨profiles, encoding⟩) fits


theorem EnumTagPrefix.untagged_index (size : Nat) (info : Enumeration) (position : Nat) (tag : Value)
    (image : ByteImage) (encoding : info.encoding = .untagged) (run : EnumTagPrefix size info position tag image) :
    position = 0 := by
  unfold EnumTagPrefix tagPrefix at run
  rw [encoding] at run
  dsimp only at run
  split at run
  · rename_i selected; exact (by trustIrCompilerProof { exact Nat.eq_of_beq_eq_true selected } { exact eq_of_beq selected })
  · cases run

theorem EnumTagPrefix.single_index (size : Nat) (info : Enumeration) (position selected : Nat) (tag : Value)
    (image : ByteImage) (encoding : info.encoding = .singleInhabited selected) (run : EnumTagPrefix size info position tag image) :
    position = selected := by
  unfold EnumTagPrefix tagPrefix at run
  rw [encoding] at run
  dsimp only at run
  split at run
  · rename_i matched; exact (by trustIrCompilerProof { exact Nat.eq_of_beq_eq_true matched } { exact eq_of_beq matched })
  · cases run

theorem EnumTagPrefix.niche_lane (size : Nat) (info : Enumeration) (position : Nat) (tag : Value)
    (image : ByteImage) (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first offset repr) (tagged : position ≠ untagged)
    (run : EnumTagPrefix size info position tag image) :
    ByteLane image offset (ByteImage.ofList ((encodeIntBytes
      (truncateUnsigned (Int.ofNat first + Int.ofNat position - Int.ofNat start) (tagBits repr))
      (tagBits repr / 8)).map some)) := by
  unfold EnumTagPrefix tagPrefix at run
  rw [encoding] at run
  have different : (position == untagged) = false := by simp [tagged]
  simp only [different,Bool.false_eq_true,ite_false] at run
  change ImageOverwrite (ByteImage.fill size none) offset _ image at run
  exact run.lane

/-- The encoder's real post-payload niche guard. -/
def NichePayloadChecked (info : Enumeration) (position : Nat) (image : ByteImage) : Prop :=
  checkNichePayload info position image = .ok ()

theorem NichePayloadChecked.untagged_outside (info : Enumeration) (image : ByteImage)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first offset repr)
    (run : NichePayloadChecked info untagged image) :
    stop - start < (decodeIntBytes ((image.slice offset (tagBits repr / 8)).toList.map (·.getD 0)) +
      2 ^ tagBits repr - first) % (2 ^ tagBits repr) := by
  unfold NichePayloadChecked checkNichePayload at run
  by_cases outside : stop - start < (decodeIntBytes ((image.slice offset (tagBits repr / 8)).toList.map (·.getD 0)) +
      2 ^ tagBits repr - first) % (2 ^ tagBits repr)
  · exact outside
  have reserved : (decodeIntBytes ((image.slice offset (tagBits repr / 8)).toList.map (·.getD 0)) +
      2 ^ tagBits repr - first) % (2 ^ tagBits repr) ≤ stop - start := by omega
  simp [encoding,reserved,typeError] at run

theorem EnumEncodingSelects.lookup (info : Enumeration) (width : Nat) (raw : Int) (position : Nat)
    (run : EnumEncodingSelects info (.int width raw) position) :
    width = tagBits info.tag ∧ discriminantIndex info.discriminants (enumTagValue info.tag raw) = some position := by
  unfold EnumEncodingSelects enumIndex at run
  cases sized : (width == tagBits info.tag) with
  | false => simp [sized,typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  | true =>
    simp only [sized,ite_true,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    cases found : discriminantIndex info.discriminants (enumTagValue info.tag raw) with
    | none => rw [found] at run; cases run
    | some actual =>
      rw [found] at run
      dsimp only at run
      split at run
      · cases run
      · cases run; exact ⟨(by trustIrCompilerProof { exact Nat.eq_of_beq_eq_true sized } { exact eq_of_beq sized }),rfl⟩

/-- An actual disjoint write preserves every byte of an authenticated lane. -/
theorem ByteLane.after_write {before after bytes laneBytes : ByteImage} {offset laneOffset : Nat}
    (lane : ByteLane before laneOffset laneBytes) (run : ImageOverwrite before offset bytes after)
    (separated : offset + bytes.size ≤ laneOffset ∨ laneOffset + laneBytes.size ≤ offset) :
    ByteLane after laneOffset laneBytes := by
  refine ⟨by rw [run.extent]; exact lane.1,?_⟩
  intro index inside
  rw [run.outside (laneOffset + index) (by have bound := lane.1; omega) (by rcases separated with prior | later <;> omega)]
  exact lane.2 index inside

/-- Physical non-overlap also covers empty lanes and zero-sized child writes. -/
theorem ByteLane.after_disjoint_write {before after bytes laneBytes : ByteImage} {offset laneOffset : Nat}
    (lane : ByteLane before laneOffset laneBytes) (run : ImageOverwrite before offset bytes after)
    (separated : overlap laneOffset laneBytes.size offset bytes.size = false) :
    ByteLane after laneOffset laneBytes := by
  let left : Field := { ty := .U8, offset := laneOffset, size := laneBytes.size, align := 1 }
  let right : Field := { ty := .U8, offset, size := bytes.size, align := 1 }
  have safe := (overlap_false_iff_separated left right).mp separated
  change laneBytes.size = 0 ∨ bytes.size = 0 ∨ laneOffset + laneBytes.size ≤ offset ∨
    offset + bytes.size ≤ laneOffset at safe
  rcases safe with laneEmpty | writeEmpty | afterLane | beforeLane
  · refine ⟨by rw [run.extent]; exact lane.1,?_⟩
    intro index inside
    omega
  · refine ⟨by rw [run.extent]; exact lane.1,?_⟩
    intro index inside
    rw [run.outside (laneOffset + index) (by have bound := lane.1; omega) (by omega)]
    exact lane.2 index inside
  · exact lane.after_write run (.inr afterLane)
  · exact lane.after_write run (.inl beforeLane)

theorem EnumTagPrefix.untagged_exists (size : Nat) (info : Enumeration) (tag : Value)
    (encoding : info.encoding = .untagged) : EnumTagPrefix size info 0 tag (ByteImage.fill size none) := by
  unfold EnumTagPrefix tagPrefix
  simp [encoding,Pure.pure,Except.pure]

theorem EnumTagPrefix.single_exists (size : Nat) (info : Enumeration) (chosen : Nat) (tag : Value)
    (encoding : info.encoding = .singleInhabited chosen) :
    EnumTagPrefix size info chosen tag (ByteImage.fill size none) := by
  unfold EnumTagPrefix tagPrefix
  simp [encoding,Pure.pure,Except.pure]

theorem EnumTagPrefix.niche_untagged_exists (size : Nat) (info : Enumeration) (tag : Value)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first offset repr) :
    EnumTagPrefix size info untagged tag (ByteImage.fill size none) := by
  unfold EnumTagPrefix tagPrefix
  simp [encoding,Pure.pure,Except.pure]

theorem EnumTagPrefix.niche_tagged_exists (size : Nat) (info : Enumeration) (position : Nat) (tag : Value)
    (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first offset repr) (other : position ≠ untagged)
    (fits : offset + (ByteImage.ofList ((encodeIntBytes
      (truncateUnsigned (Int.ofNat first + Int.ofNat position - Int.ofNat start) (tagBits repr))
      (tagBits repr / 8)).map some)).size ≤ size) : ∃ image, EnumTagPrefix size info position tag image := by
  unfold EnumTagPrefix tagPrefix
  rw [encoding]
  have different : (position == untagged) = false := by simp [other]
  simp only [different,Bool.false_eq_true,ite_false]
  change ∃ image, overwrite (ByteImage.fill size none) offset _ = .ok image
  unfold overwrite
  simp only [ByteImage.size_fill]
  rw [if_pos fits]
  exact ⟨_,rfl⟩

/-- The actual payload field encoder, including its child calls and overwrites. -/
def FieldsEncoded (model : ByteModel) (order : FunctionAddressOrder)
    (fields : List (Nat × Plan)) (values : List Value) (allowUnwritten : Bool)
    (before after : Image) : Prop :=
  encodeFields model order fields values allowUnwritten before = .ok after

/-- An empty successful row has no values and leaves the whole image unchanged. -/
theorem FieldsEncoded.nil_iff {model : ByteModel} {order : FunctionAddressOrder}
    {values : List Value} {allowUnwritten : Bool} {before after : Image} :
    FieldsEncoded model order [] values allowUnwritten before after ↔ values = [] ∧ after = before := by
  cases values with
  | nil =>
    constructor
    · intro run
      simp only [FieldsEncoded,encodeFields,Pure.pure,Except.pure,Except.ok.injEq] at run
      exact ⟨rfl,run.symm⟩
    · intro ⟨_,same⟩
      cases same
      trustIrCompilerProof { rfl } { simp only [FieldsEncoded,encodeFields,Pure.pure,Except.pure] }
  | cons value later => simp [FieldsEncoded,encodeFields,typeError]

/-- Exact public decomposition of one successful private field-encoder step,
    including the real propagated unwritten-range metadata. -/
theorem FieldsEncoded.cons_iff {model : ByteModel} {order : FunctionAddressOrder}
    {offset : Nat} {plan : Plan} {fields : List (Nat × Plan)}
    {value : Value} {values : List Value} {allowUnwritten : Bool} {before after : Image} :
    FieldsEncoded model order ((offset,plan) :: fields) (value :: values) allowUnwritten before after ↔
      ∃ child bytes, encode model order plan value allowUnwritten = .ok child ∧
        ImageOverwrite before.bytes offset child.bytes bytes ∧
        FieldsEncoded model order fields values allowUnwritten
          { bytes, unwritten := before.unwritten ++
            child.unwritten.map (fun (start,count) => (offset + start,count)) } after := by
  constructor
  · intro run
    unfold FieldsEncoded at run
    rw [encodeFields] at run
    cases childRun : encode model order plan value allowUnwritten with
    | error error => simp [childRun,Bind.bind,Except.bind] at run
    | ok child =>
      simp only [childRun,Bind.bind,Except.bind] at run
      cases written : overwrite before.bytes offset child.bytes with
      | error error => simp [written,Except.bind] at run
      | ok bytes =>
        simp only [written,Except.bind] at run
        exact ⟨child,bytes,rfl,written,run⟩
  · intro ⟨child,bytes,childRun,written,rest⟩
    unfold ImageOverwrite at written
    unfold FieldsEncoded
    rw [encodeFields]
    simp only [childRun,Bind.bind,Except.bind,written]
    exact rest

/-- A successful nonempty field row has an actual first value and step. -/
theorem FieldsEncoded.head {model : ByteModel} {order : FunctionAddressOrder}
    {offset : Nat} {plan : Plan} {fields : List (Nat × Plan)}
    {values : List Value} {allowUnwritten : Bool} {before after : Image}
    (run : FieldsEncoded model order ((offset,plan) :: fields) values allowUnwritten before after) :
    ∃ value later child bytes, values = value :: later ∧
      encode model order plan value allowUnwritten = .ok child ∧
      ImageOverwrite before.bytes offset child.bytes bytes ∧
      FieldsEncoded model order fields later allowUnwritten
        { bytes, unwritten := before.unwritten ++
          child.unwritten.map (fun (start,count) => (offset + start,count)) } after := by
  cases values with
  | nil => simp [FieldsEncoded,encodeFields,typeError] at run
  | cons value later =>
    obtain ⟨child,bytes,encoded,written,rest⟩ := FieldsEncoded.cons_iff.mp run
    exact ⟨value,later,child,bytes,rfl,encoded,written,rest⟩

/-- The actual selected payload encoder, including inactive-variant refusal. -/
def VariantEncoded (model : ByteModel) (order : FunctionAddressOrder)
    (variants : List (Option (List (Nat × Plan)))) (position : Nat) (values : List Value)
    (before after : Image) : Prop :=
  encodeVariant model order variants position values before = .ok after

/-- A present selected row and its actual strict field encoding construct
one variant step, without unfolding unrelated payload ranks. -/
theorem VariantEncoded.of_fields (model : ByteModel) (order : FunctionAddressOrder)
    (variants : List (Option (List (Nat × Plan)))) (position : Nat) (values : List Value)
    (before after : Image) (fields : List (Nat × Plan))
    (row : (trustIrListGet? variants position) = some (some fields))
    (run : FieldsEncoded model order fields values false before after) :
    VariantEncoded model order variants position values before after := by
  unfold VariantEncoded
  induction variants generalizing position with
  | nil => cases row
  | cons first rest ih =>
    cases position with
    | zero =>
      have same : first = some fields := Option.some.inj row
      subst first
      rw [encodeVariant]
      exact run
    | succ position =>
      rw [encodeVariant]
      exact ih position row

/-- Actual selection, prefix construction, strict payload encoding and its
final guard compose into the real encoder, independently of plan rank. -/
theorem encode_enumeration_of_components (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value)
    (position : Nat) (allowUnwritten : Bool) (bytes : ByteImage) (image : Image)
    (selected : EnumEncodingSelects info tag position)
    (built : EnumTagPrefix layout.size info position tag bytes)
    (payload : VariantEncoded model order variants position values { bytes } image)
    (checked : NichePayloadChecked info position image.bytes) :
    encode model order (.enumeration ty layout info variants) (.aggregate (tag :: values)) allowUnwritten = .ok image := by
  unfold EnumEncodingSelects at selected
  unfold EnumTagPrefix at built
  unfold VariantEncoded at payload
  unfold NichePayloadChecked at checked
  rw [encode]
  simp only [Value.isUninit,Bool.false_eq_true,ite_false,selected,built,payload,checked,
    Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- A typed selector rejection propagates its exact error before prefix or
payload construction; no impossible source value is encoded. -/
theorem encode_enumeration_of_rejection (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value)
    (allowUnwritten : Bool) (error : SemError) (rejected : EnumEncodingRejects info tag error) :
    encode model order (.enumeration ty layout info variants) (.aggregate (tag :: values)) allowUnwritten = .error error := by
  unfold EnumEncodingRejects at rejected
  rw [encode]
  simp only [Value.isUninit,Bool.false_eq_true,ite_false,rejected,Bind.bind,Except.bind,Pure.pure,Except.pure]

private theorem fields_encoding_extent (model : ByteModel) (order : FunctionAddressOrder)
    (fields : List (Nat × Plan)) (values : List Value) (allowUnwritten : Bool)
    (before after : Image)
    (run : encodeFields model order fields values allowUnwritten before = .ok after) :
    after.bytes.size = before.bytes.size := by
  induction fields generalizing values before with
  | nil =>
    cases values <;> simp [encodeFields,typeError,Pure.pure,Except.pure] at run
    cases run
    rfl
  | cons pair rest ih =>
    obtain ⟨offset,plan⟩ := pair
    cases values with
    | nil => simp [encodeFields,typeError] at run
    | cons value later =>
      rw [encodeFields] at run
      cases childRun : encode model order plan value allowUnwritten with
      | error error => simp [childRun,Bind.bind,Except.bind] at run
      | ok child =>
        simp only [childRun,Bind.bind,Except.bind] at run
        cases written : overwrite before.bytes offset child.bytes with
        | error error => simp [written,Except.bind] at run
        | ok bytes =>
          simp only [written,Except.bind] at run
          have extent : bytes.size = before.bytes.size := ImageOverwrite.extent written
          exact (ih later _ run).trans extent

theorem FieldsEncoded.extent {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    {before after : Image} (run : FieldsEncoded model order fields values allowUnwritten before after) :
    after.bytes.size = before.bytes.size :=
  fields_encoding_extent model order fields values allowUnwritten before after run

theorem VariantEncoded.extent {model : ByteModel} {order : FunctionAddressOrder}
    {variants : List (Option (List (Nat × Plan)))} {position : Nat} {values : List Value}
    {before after : Image} (run : VariantEncoded model order variants position values before after) :
    after.bytes.size = before.bytes.size := by
  unfold VariantEncoded at run
  induction variants generalizing position with
  | nil => simp [encodeVariant,typeError] at run
  | cons fields rest ih =>
    cases position with
    | zero =>
      cases fields with
      | none => simp [encodeVariant,typeError] at run
      | some fields =>
        rw [encodeVariant] at run
        exact fields_encoding_extent model order fields values false before after run
    | succ position =>
      rw [encodeVariant] at run
      exact ih run

theorem EnumTagPrefix.extent {size position : Nat} {info : Enumeration} {tag : Value}
    {image : ByteImage} (run : EnumTagPrefix size info position tag image) : image.size = size := by
  unfold EnumTagPrefix tagPrefix at run
  cases encoding : info.encoding with
  | untagged =>
    simp only [encoding] at run
    split at run
    · simp only [Pure.pure,Except.pure,Except.ok.injEq] at run
      cases run
      exact ByteImage.size_fill _ _
    · cases run
  | singleInhabited selected =>
    simp only [encoding] at run
    split at run
    · simp only [Pure.pure,Except.pure,Except.ok.injEq] at run
      cases run
      exact ByteImage.size_fill _ _
    · cases run
  | direct offset =>
    simp only [encoding] at run
    cases tag <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    exact (ImageOverwrite.extent run).trans (ByteImage.size_fill _ _)
  | directWithUninhabited offset profiles =>
    simp only [encoding] at run
    cases tag <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    exact (ImageOverwrite.extent run).trans (ByteImage.size_fill _ _)
  | niche untagged start stop first offset repr =>
    by_cases selected : position = untagged
    · simp [encoding,selected,Pure.pure,Except.pure] at run
      cases run
      exact ByteImage.size_fill _ _
    · simp only [encoding] at run
      have different : (position == untagged) = false := by simp [selected]
      simp only [different,Bool.false_eq_true,ite_false] at run
      exact (ImageOverwrite.extent run).trans (ByteImage.size_fill _ _)

/-- Successful initialized enum encoding exposes the actual encoder composition. -/
theorem encode_enumeration_steps (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value)
    (allowUnwritten : Bool) (image : Image)
    (run : encode model order (.enumeration ty layout info variants)
      (.aggregate (tag :: values)) allowUnwritten = .ok image) :
    ∃ position bytes,
      EnumEncodingSelects info tag position ∧
      EnumTagPrefix layout.size info position tag bytes ∧
      VariantEncoded model order variants position values { bytes } image ∧
      NichePayloadChecked info position image.bytes := by
  rw [encode] at run
  simp only [Value.isUninit, Bool.false_eq_true, ite_false, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at run
  cases selected : enumIndex info tag with
  | error error => simp [selected,Except.bind] at run
  | ok position =>
    simp only [selected,Except.bind] at run
    cases built : tagPrefix layout.size info position tag with
    | error error => simp [built,Except.bind] at run
    | ok bytes =>
      simp only [built,Except.bind] at run
      cases payload : encodeVariant model order variants position values { bytes } with
      | error error => simp [payload,Except.bind] at run
      | ok result =>
        simp only [payload,Except.bind] at run
        cases checked : checkNichePayload info position result.bytes with
        | error error => simp [checked,Except.bind] at run
        | ok unit =>
          cases unit
          simp only [checked,Except.bind,Except.ok.injEq] at run
          cases run
          exact ⟨position,bytes,selected,built,payload,checked⟩

theorem encode_enumeration_extent (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
    (variants : List (Option (List (Nat × Plan)))) (tag : Value) (values : List Value)
    (allowUnwritten : Bool) (image : Image)
    (run : encode model order (.enumeration ty layout info variants)
      (.aggregate (tag :: values)) allowUnwritten = .ok image) : image.bytes.size = layout.size := by
  obtain ⟨position,bytes,_,built,payload,_⟩ :=
    encode_enumeration_steps model order ty layout info variants tag values allowUnwritten image run
  exact (VariantEncoded.extent payload).trans (EnumTagPrefix.extent built)

/-- Every successful encoder result has the exact retained plan extent. -/
theorem encode_extent (model : ByteModel) (order : FunctionAddressOrder) (plan : Plan)
    (value : Value) (allowUnwritten : Bool) (image : Image)
    (run : encode model order plan value allowUnwritten = .ok image) :
    image.bytes.size = plan.layout.size := by
  have original := run
  by_cases uninit : value.isUninit = true
  · cases plan <;> trustIrCompilerProof { rw [encode] at run } { rw [encode.eq_def] at run }
    all_goals simp only [uninit,ite_true] at run
    all_goals
      split at run
      · simp only [Pure.pure,Except.pure,Except.ok.injEq] at run
        cases run
        exact ByteImage.size_fill _ _
      · cases run
  · have initialized : value.isUninit = false := by
      cases flag : value.isUninit with
      | false => rfl
      | true => exact False.elim (uninit flag)
    cases plan with
    | leaf ty layout =>
      trustIrCompilerProof { rw [encode] at run } { rw [encode.eq_def] at run }
      simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases leafRun : encodeLeaf model order ty value with
      | error error => simp [leafRun,Bind.bind,Except.bind] at run
      | ok bytes =>
        simp only [leafRun,Bind.bind,Except.bind] at run
        by_cases fits : bytes.length = layout.size
        · simp [fits,Pure.pure,Except.pure] at run
          cases run
          simpa [ByteImage.size_ofList] using fits
        · simp [fits,typeError] at run
    | fnItem target layout =>
      trustIrCompilerProof { rw [encode] at run } { rw [encode.eq_def] at run }
      simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      repeat' first
        | (solve | cases run)
        | (simp only [typeError,ub,Bind.bind,Except.bind,Pure.pure,Except.pure] at run)
        | (split at run)
      all_goals cases run
      all_goals simp_all [Plan.layout,ByteImage.empty]
    | fields ty layout fields =>
      trustIrCompilerProof { rw [encode] at run } { rw [encode.eq_def] at run }
      simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases value <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      exact (FieldsEncoded.extent run).trans (ByteImage.size_fill _ _)
    | array ty layout count element =>
      trustIrCompilerProof { rw [encode] at run } { rw [encode.eq_def] at run }
      simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases value <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      rename_i values
      by_cases census : values.size = count
      · simp only [census,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false] at run
        cases arrayRun : encodeArrayImage (fun value => do
          pure (← encode model order element value false).bytes) values.tree with
        | error error =>
          simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at arrayRun
          simp [arrayRun,Except.bind] at run
        | ok bytes =>
          simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at arrayRun
          simp only [arrayRun,Except.bind] at run
          by_cases fits : bytes.size = layout.size
          · simp [fits,Pure.pure,Except.pure] at run
            cases run
            exact fits
          · simp [fits,typeError] at run
      · simp [census,typeError] at run
    | enumeration ty layout info variants =>
      trustIrCompilerProof { rw [encode] at run } { rw [encode.eq_def] at run }
      simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases value <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      rename_i values
      cases values with
      | nil => cases run
      | cons tag payload =>
        exact encode_enumeration_extent model order ty layout info variants tag payload allowUnwritten image original

/-- Nonempty uniform arrays run the real child encoder once and retain its
    tiled byte image. Symbolic arithmetic avoids unfolding a logical count. -/
theorem encode_uniform_array (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (value : Value) (child : Image) (positive : 0 < count)
    (encoded : encode model order element value false = .ok child)
    (extent : layout.size = child.bytes.size * count) :
    encode model order (.array ty layout count element) (.array (CompactArray.Packed.uniform count value)) false =
      .ok { bytes := child.bytes.tile count } := by
  rw [encode]
  simp only [Value.isUninit,Value.isPoison,Bool.false_eq_true,ite_false,
    CompactArray.Packed.uniform,bne,beq_self_eq_true,Bool.not_true,Bind.bind,Except.bind,Pure.pure,Except.pure]
  simp only [encodeArrayImage,encodeArrayRange,Nat.sub_zero,Nat.min_self,
    show (count == 0) = false from beq_false_of_ne (by omega),ite_false,encoded,
    Bind.bind,Except.bind,Pure.pure,Except.pure,ByteImage.size_tile,extent,
    beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false]

/-- Successful ordinary array encoding exposes the actual compact fold and
its checked logical census, without expanding the represented values. -/
theorem encode_array_steps (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (value : Value) (image : Image)
    (run : encode model order (.array ty layout count element) value false = .ok image) :
    ∃ values, value = .array values ∧ values.size = count ∧
      ArrayImageEncoded (fun child => do
        pure (← encode model order element child false).bytes) values.tree image.bytes := by
  rw [encode] at run
  by_cases uninit : value.isUninit = true
  · simp only [uninit,ite_true,Bool.false_eq_true,ite_false] at run
    cases run
  · have initialized : value.isUninit = false := by
      cases flag : value.isUninit with
      | false => rfl
      | true => exact False.elim (uninit flag)
    simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,
      Pure.pure,Except.pure] at run
    cases value <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    rename_i values
    by_cases census : values.size = count
    · simp only [census,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false] at run
      cases arrayRun : encodeArrayImage (fun child => do
        pure (← encode model order element child false).bytes) values.tree with
      | error failure =>
        simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at arrayRun
        simp [arrayRun,Except.bind] at run
      | ok bytes =>
        simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at arrayRun
        simp only [arrayRun,Except.bind] at run
        by_cases fits : bytes.size = layout.size
        · simp [fits,Pure.pure,Except.pure] at run
          cases run
          exact ⟨values,rfl,census,arrayRun⟩
        · simp [fits,typeError] at run
    · simp [census,typeError] at run

/-- Every retained child plan occupies a range disjoint from the lane. -/
def FieldsAvoidLane (fields : List (Nat × Plan)) (offset count : Nat) : Prop :=
  ∀ field ∈ fields, overlap offset count field.1 field.2.layout.size = false

/-- Actual recursive payload writes preserve a lane when their real extents are disjoint. -/
theorem FieldsEncoded.preserves_lane {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    {before after : Image} {offset : Nat} {bytes : ByteImage}
    (run : FieldsEncoded model order fields values allowUnwritten before after)
    (lane : ByteLane before.bytes offset bytes)
    (separated : FieldsAvoidLane fields offset bytes.size) : ByteLane after.bytes offset bytes := by
  unfold FieldsEncoded at run
  induction fields generalizing values before with
  | nil =>
    cases values <;> simp [encodeFields,typeError,Pure.pure,Except.pure] at run
    cases run
    exact lane
  | cons pair rest ih =>
    obtain ⟨fieldOffset,plan⟩ := pair
    cases values with
    | nil => simp [encodeFields,typeError] at run
    | cons value later =>
      rw [encodeFields] at run
      cases childRun : encode model order plan value allowUnwritten with
      | error error => simp [childRun,Bind.bind,Except.bind] at run
      | ok child =>
        simp only [childRun,Bind.bind,Except.bind] at run
        cases written : overwrite before.bytes fieldOffset child.bytes with
        | error error => simp [written,Except.bind] at run
        | ok next =>
          simp only [written,Except.bind] at run
          have actualExtent := encode_extent model order plan value allowUnwritten child childRun
          have avoids : overlap offset bytes.size fieldOffset child.bytes.size = false := by
            rw [actualExtent]
            exact separated (fieldOffset,plan) ((trustIrListMemConsSelf _ _))
          have retained := ByteLane.after_disjoint_write lane written avoids
          have remaining : FieldsAvoidLane rest offset bytes.size := by
            intro field member
            exact separated field (List.mem_cons_of_mem _ member)
          exact ih run retained remaining

/-- Successful selected payload encoding retains its actual field row. -/
theorem VariantEncoded.fields {model : ByteModel} {order : FunctionAddressOrder}
    {variants : List (Option (List (Nat × Plan)))} {position : Nat} {values : List Value}
    {before after : Image} (run : VariantEncoded model order variants position values before after) :
    ∃ fields, (trustIrListGet? variants position) = some (some fields) ∧
      FieldsEncoded model order fields values false before after := by
  unfold VariantEncoded at run
  induction variants generalizing position with
  | nil => simp [encodeVariant,typeError] at run
  | cons fields rest ih =>
    cases position with
    | zero =>
      cases fields with
      | none => simp [encodeVariant,typeError] at run
      | some fields =>
        rw [encodeVariant] at run
        exact ⟨fields,rfl,run⟩
    | succ position =>
      rw [encodeVariant] at run
      obtain ⟨fields,found,encoded⟩ := ih run
      exact ⟨fields,found,encoded⟩

theorem VariantEncoded.preserves_lane {model : ByteModel} {order : FunctionAddressOrder}
    {variants : List (Option (List (Nat × Plan)))} {position : Nat} {values : List Value}
    {before after : Image} {offset : Nat} {bytes : ByteImage}
    (run : VariantEncoded model order variants position values before after)
    (lane : ByteLane before.bytes offset bytes)
    (separated : ∀ fields, (trustIrListGet? variants position) = some (some fields) →
      FieldsAvoidLane fields offset bytes.size) : ByteLane after.bytes offset bytes := by
  obtain ⟨fields,found,encoded⟩ := run.fields
  exact encoded.preserves_lane lane (separated fields found)

theorem EnumEncodingSelects.functional {info : Enumeration} {tag : Value} {first second : Nat}
    (left : EnumEncodingSelects info tag first) (right : EnumEncodingSelects info tag second) : first = second := by
  unfold EnumEncodingSelects at left right
  rw [left] at right
  exact Except.ok.inj right

theorem EnumTagPrefix.direct_encoding_tag {size position offset : Nat} {info : Enumeration} {tag : Value}
    {image : ByteImage} (encoding : DirectEncodingAt info.encoding offset)
    (run : EnumTagPrefix size info position tag image) : ∃ width raw, tag = .int width raw := by
  rcases encoding with encoding | ⟨profiles, encoding⟩
  all_goals
    unfold EnumTagPrefix tagPrefix at run
    rw [encoding] at run
    cases tag <;> simp [typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    exact ⟨_,_,rfl⟩

theorem EnumTagPrefix.direct_tag {size position offset : Nat} {info : Enumeration} {tag : Value}
    {image : ByteImage} (encoding : info.encoding = .direct offset)
    (run : EnumTagPrefix size info position tag image) : ∃ width raw, tag = .int width raw := by
  exact EnumTagPrefix.direct_encoding_tag (Or.inl encoding) run

theorem EnumTagPrefix.profiled_direct_tag {size position offset : Nat} {info : Enumeration} {tag : Value}
    {image : ByteImage} {profiles : List UninhabitedVariantLayout} (encoding : info.encoding = .directWithUninhabited offset profiles)
    (run : EnumTagPrefix size info position tag image) : ∃ width raw, tag = .int width raw := by
  exact EnumTagPrefix.direct_encoding_tag (Or.inr ⟨profiles, encoding⟩) run


private theorem encodeLeaf_memory_success (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (value : Value) (bytes : List UInt8) (run : encodeLeaf model order ty value = .ok bytes) :
    encodeMemoryWithFunctions model order ty value = .ok bytes := by
  simp only [encodeLeaf,ub,typeError,rejectUninit,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  repeat' first
    | exact run
    | (cases run)
    | (split at run)

/-- Successful ordinary leaf storage supplies the actual contextual scalar
    encoder call, exact extent and initialized image; no decoder premise is used. -/
theorem encode_leaf_memory_success (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Value) (image : Image)
    (run : encode model order (.leaf ty layout) value false = .ok image) :
    ∃ bytes, encodeMemoryWithFunctions model order ty value = .ok bytes ∧
      bytes.length = layout.size ∧ image.bytes = ByteImage.ofList (bytes.map some) := by
  by_cases uninit : value.isUninit = true
  · rw [encode] at run
    simp [uninit,rejectUninit,ub] at run
  · have initialized : value.isUninit = false := by
      cases flag : value.isUninit with
      | false => rfl
      | true => exact False.elim (uninit flag)
    rw [encode] at run
    simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    cases leafRun : encodeLeaf model order ty value with
    | error error => simp [leafRun,Bind.bind,Except.bind] at run
    | ok bytes =>
      simp only [leafRun,Bind.bind,Except.bind] at run
      by_cases fits : bytes.length = layout.size
      · simp [fits,Pure.pure,Except.pure] at run
        cases run
        exact ⟨bytes,encodeLeaf_memory_success model order ty value bytes leafRun,fits,rfl⟩
      · simp [fits,typeError] at run

/-- An ordinary scalar plan cannot acquire the prepared nominal operation.
The original universal scalar-success law forces this refusal for every value. -/
theorem encode_fnItem_as_scalar_leaf_refuses (model : ByteModel) (order : FunctionAddressOrder)
    (target : FuncId) (layout : MemoryTypeLayout) (value : Value) (image : Image) :
    encode model order (.leaf (.FnItem target) layout) value false ≠ .ok image := by
  intro success
  obtain ⟨bytes,scalar,_,_⟩ :=
    encode_leaf_memory_success model order (.FnItem target) layout value image success
  trustIrCompilerProof {
    simp only [encodeMemoryWithFunctions] at scalar
  } {
    simp only [encodeMemoryWithFunctions] at scalar
    cases scalar
  }

/-- Ordinary successful leaf storage passed the real fat-metadata guard.
    Raw contextual scalar success alone does not imply this guard. -/
theorem encode_leaf_fat_valid (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (encoded : encode model order (.leaf ty layout) input false = .ok stored) :
    fatPtrStoreValueValidFor model ty input = true := by
  by_cases valid : fatPtrStoreValueValidFor model ty input = true
  · exact valid
  · have invalid : fatPtrStoreValueValidFor model ty input = false := by
      cases flag : fatPtrStoreValueValidFor model ty input with
      | false => rfl
      | true => exact False.elim (valid flag)
    rw [encode] at encoded
    by_cases uninit : input.isUninit = true
    · simp [uninit,rejectUninit,ub] at encoded
    · have initialized : input.isUninit = false := by
        cases flag : input.isUninit with
        | false => rfl
        | true => exact False.elim (uninit flag)
      by_cases poison : input.isPoison = true
      · simp [initialized,encodeLeaf,poison,ub,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
      · have clean : input.isPoison = false := by
          cases flag : input.isPoison with
          | false => rfl
          | true => exact False.elim (poison flag)
        simp [initialized,encodeLeaf,clean,invalid,typeError,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded

/-- The actual aggregate integer leaf checks source width and byte extent
before retaining the contextual memory encoder's initialized byte image. -/
theorem encode_integer_leaf_of_memory (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int) (bytes : List UInt8)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (size : bytes.length = layout.size)
    (encoded : encodeMemoryWithFunctions model order ty (.int width raw) = .ok bytes) :
    encode model order (.leaf ty layout) (.int width raw) false =
      .ok { bytes := ByteImage.ofList (bytes.map some) } := by
  have fat : fatPtrStoreValueValidFor model ty (.int width raw) = true := by
    cases model <;> cases ty <;> simp only [Ty.isInteger] at integer <;> try cases integer
    all_goals rfl
  rw [encode]
  simp [encodeLeaf,Value.isUninit,Value.isPoison,fat,integer,typed,encoded,size,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- A thin-pointer or null value reaches the actual memory word encoder
with the source leaf's checked byte extent. -/
theorem encode_pointer_leaf_of_memory (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Value) (bytes : List UInt8)
    (pointer : ty.isPointerLike = true)
    (word : (∃ address provenance, value = .ptr address provenance) ∨ value = .nullPtr)
    (size : bytes.length = layout.size)
    (encoded : encodeMemoryWithFunctions model order ty value = .ok bytes) :
    encode model order (.leaf ty layout) value false = .ok { bytes := ByteImage.ofList (bytes.map some) } := by
  rcases word with ⟨address,provenance,rfl⟩ | rfl
  all_goals
    cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
  all_goals rw [encode]
  all_goals simp [encodeLeaf,Value.isUninit,Value.isPoison,Ty.isInteger,fatPtrStoreValueValidFor,
    fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,encoded,size,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Function leaves preserve the contextual function-word codec and exact extent. -/
theorem encode_function_leaf_of_memory (model : ByteModel) (order : FunctionAddressOrder)
    (signature : FuncTyId) (layout : MemoryTypeLayout) (value : Value) (bytes : List UInt8)
    (word : (∃ target, value = .fnDef signature target) ∨ value = .nullPtr)
    (size : bytes.length = layout.size)
    (encoded : encodeMemoryWithFunctions model order (.Func signature) value = .ok bytes) :
    encode model order (.leaf (.Func signature) layout) value false = .ok { bytes := ByteImage.ofList (bytes.map some) } := by
  rcases word with ⟨target,rfl⟩ | rfl
  all_goals cases model
  all_goals rw [encode]
  all_goals simp [encodeLeaf,Value.isUninit,Value.isPoison,Ty.isInteger,fatPtrStoreValueValidFor,
    fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,encoded,size,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Fat-pointer leaves retain their actual kind/metadata admission check;
raw memory-word success alone does not waive that check. -/
theorem encode_fat_pointer_leaf_of_memory (model : ByteModel) (order : FunctionAddressOrder)
    (kind : FatPtrKind) (layout : MemoryTypeLayout) (data : Nat) (provenance : Option AllocId)
    (metadata : Value) (bytes : List UInt8)
    (valid : fatPtrStoreValueValidFor model (.FatPtr kind) (.fatPtr data provenance metadata) = true)
    (size : bytes.length = layout.size)
    (encoded : encodeMemoryWithFunctions model order (.FatPtr kind) (.fatPtr data provenance metadata) = .ok bytes) :
    encode model order (.leaf (.FatPtr kind) layout) (.fatPtr data provenance metadata) false =
      .ok { bytes := ByteImage.ofList (bytes.map some) } := by
  rw [encode]
  simp [encodeLeaf,Value.isUninit,Value.isPoison,valid,Ty.isInteger,encoded,size,
    Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Float leaves retain the typed codec's exact failure and byte-count checks. -/
theorem encode_float_leaf_of_type (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Float) (floating : ty.isFloat = true) :
    encode model order (.leaf ty layout) (.float value) false =
      (encodeFloatAt ty value).bind (fun bytes =>
        if bytes.length != layout.size then .error (.typeError "memory image: leaf byte count mismatch")
        else .ok { bytes := ByteImage.ofList (bytes.map some) }) := by
  cases ty <;> simp only [Ty.isFloat] at floating <;> try cases floating
  all_goals rw [encode]
  all_goals cases model <;> simp [typeError,ub,rejectUninit,encodeLeaf,Value.isUninit,Value.isPoison,Ty.isInteger,
    fatPtrStoreValueValidFor,fatPtrStoreValueValid,fatPtrStoreValueValidAtModel,
    encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,encodeValueAt,encodeTypedAtModel,
    Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- A typed leaf is a byte operation after source-plan admission. Its exact
    target is retained even though no address or payload byte is emitted. -/
theorem encode_fnItem (model : ByteModel) (order : FunctionAddressOrder)
    (target : FuncId) (layout : MemoryTypeLayout) (value : Value)
    (allowUnwritten : Bool) :
    encode model order (.fnItem target layout) value allowUnwritten = (do
      if value.isUninit then
        if allowUnwritten then
          return { bytes := ByteImage.fill layout.size none, unwritten := [(0, layout.size)] }
        else return ← rejectUninit
      if layout.size != 0 || layout.alignment != 1 then
        return ← typeError "memory image: function item layout is not zero-sized/alignment-one"
      if value.isPoison then return ← ub "memory image: inspecting poison"
      match value with
      | .fnItem actual =>
        if actual == target then pure { bytes := ByteImage.empty }
        else typeError "memory image: function item identity does not match its source type"
      | _ => typeError "memory image: expected a nominal function item") := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta encode encode._mutual
      rw [WellFounded.fix_eq]
    rfl
  } {
    rw [encode.eq_def] <;> rfl
  }

/-- The array equation keeps the real compact traversal and its element
    callback, without reducing a rank containing the logical array count. -/
theorem encode_array (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (value : Value) (allowUnwritten : Bool) :
    encode model order (.array ty layout count element) value allowUnwritten = (do
      if value.isUninit then
        if allowUnwritten then
          return { bytes := ByteImage.fill layout.size none, unwritten := [(0, layout.size)] }
        else return ← rejectUninit
      let values ← match value with
        | .array values => pure values
        | _ => typeError "memory image: expected array elements"
      if values.size != count then return ← typeError "memory image: array census mismatch"
      let bytes ← encodeArrayImage (fun value => do
        pure (← encode model order element value false).bytes) values.tree
      if bytes.size != layout.size then return ← typeError "memory image: array byte count mismatch"
      pure { bytes }) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta encode encode._mutual
      rw [WellFounded.fix_eq]
    rfl
  } {
    rw [encode.eq_def] <;> rfl
  }

end TrustIr.AggregateMemory
