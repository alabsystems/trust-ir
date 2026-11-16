-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Rules
import TrustIr.Layout.Index

namespace TrustIr.SourceLayout

@[noinline] def tagBits : EnumTagRepr → Nat
  | .u8 | .i8 => 8
  | .u16 | .i16 => 16
  | .u32 | .i32 => 32
  | .u64 | .i64 => 64
  | .u128 | .i128 => 128

def tagSigned : EnumTagRepr → Bool
  | .i8 | .i16 | .i32 | .i64 | .i128 => true
  | _ => false

def tagFits (repr : EnumTagRepr) (value : Int) : Bool :=
  let width := tagBits repr
  if tagSigned repr then -(2 ^ (width - 1)) ≤ value && value < 2 ^ (width - 1)
  else 0 ≤ value && value < 2 ^ (if width == 128 then width - 1 else width)

def discriminants (definition : EnumDef) : Option (List Int) :=
  let explicit := (List.range definition.variants.length).map
    (fun position => (trustIrListGet? definition.discriminants position).join)
  let rec go : List (Option Int) → Option Int → List Int → Option (List Int)
    | [], _, out => some out.reverse
    | first :: rest, next, out => do
      let value ← first.orElse (fun _ => next)
      if out.contains value then none
      else go rest (if value + 1 < 2 ^ (tagBits .i128 - 1) then some (value + 1) else none) (value :: out)
  go explicit (some 0) []

def canonicalTag (definition : EnumDef) : Option EnumTagRepr := do
  if definition.variants.isEmpty then none
  let values ← discriminants definition
  match definition.tagRepr with
  | some repr => if values.all (tagFits repr) then some repr else none
  | none =>
    let candidates : List EnumTagRepr :=
      if values.all (fun value => 0 ≤ value) then [.u8, .u16, .u32, .u64]
      else [.i8, .i16, .i32, .i64]
    candidates.find? (fun repr => values.all (tagFits repr))

private def validLane (id size align offset laneSize laneAlign : Nat) : Result Unit := do
  let endOffset ← checked (offset + laneSize)
  if offset % laneAlign != 0 || laneAlign > align || endOffset > size then
    throw (.incoherent "enum" id)

private def profileTagLanes (id offset width : Nat) : List UninhabitedVariantLayout → Result Unit
  | [] => pure ()
  | profile :: rest => do
    validLane id profile.size profile.align offset width width
    profileTagLanes id offset width rest

/-- Sorted, unique profiles cover exactly the least-fixed-point dead rows.
    Rejection is an initial enum check, before any child storage is solved. -/
def directProfilesCover (definition : EnumDef) (dead : List Bool)
    (profiles : List UninhabitedVariantLayout) : Bool :=
  definition.variants.length < 2 ^ 32 && profiles.length < 2 ^ 32 &&
  dead.length == definition.variants.length &&
  profiles.map (·.variant) == (numbered dead).filterMap
    (fun (impossible, position) => if impossible then some position else none)

/-- Validate physical extents without querying the impossible source types.
    These fields retain their source identity but never acquire a value codec. -/
def uninhabitedVariant (mode : Mode) (id : Nat) (descriptor : EnumLayoutDescriptor)
    (profile : UninhabitedVariantLayout) (types : List Ty) : Result Summary := do
  let reject : Result Summary := .error (.incoherent "enum" id)
  if profile.variant ≥ 2 ^ 32 || profile.fields.length ≥ 2 ^ 32 ||
      !powerOfTwo profile.align || profile.size % profile.align != 0 ||
      profile.align > descriptor.align || profile.size > descriptor.size then
    return ← reject
  let offsets ← match trustIrListGet? descriptor.variantFieldOffsets profile.variant with
    | some offsets => pure offsets | none => throw (.incoherent "enum" id)
  if offsets.length != types.length || profile.fields.length != types.length then
    return ← reject
  let fields := ((types.zip offsets).zip profile.fields).map
    (fun ((ty, offset), storage) =>
      ({ ty, offset, size := storage.size, align := storage.align } : Field))
  for field in fields do
    let _ ← checked field.size
    let _ ← checked field.align
    let limit ← checked (field.offset + field.size)
    if !powerOfTwo field.align || field.size % field.align != 0 || field.offset % field.align != 0 ||
        field.align > profile.align || limit > profile.size then
      return ← reject
  if hasOverlap fields then return ← reject
  finish mode { size := profile.size, align := some profile.align, fields }

/-- Place canonical variant-relative fields in the shared payload region. -/
def placePayload (offset : Nat) (variants : List Summary) : List (List Field) :=
  variants.map (fun variant => variant.fields.map (fun field => { field with offset := offset + field.offset }))

/-- The explicit no-tag selector is checked against the full original rows.
    A conservative false fact never licenses skipping a physical child. -/
def singleInhabitedValid (definition : EnumDef) (descriptor : EnumLayoutDescriptor)
    (uninhabited : List Bool) (selected : Nat) : Bool :=
  selected < definition.variants.length && selected < 2 ^ 32 &&
    uninhabited.length == definition.variants.length &&
    descriptor.variantFieldOffsets.length == definition.variants.length &&
    (numbered uninhabited).all (fun (impossible, position) =>
      if position == selected then !impossible
      else impossible && ((trustIrListGet? descriptor.variantFieldOffsets position).getD []).isEmpty)

/-- Actual physical-row selector used by the source compiler. Selection is
    available only for an authored single-inhabited encoding whose complete
    original-row flag and offset checks succeed. -/
def enumPhysicalSelection (definition : EnumDef) (uninhabited : List Bool) : Option Nat :=
  match definition.layout with
  | some descriptor => match descriptor.encoding with
    | .singleInhabited selected =>
      if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
    | _ => none
  | none => none

private def makeEnum (mode : Mode) (definition : EnumDef) (tag : EnumTagRepr)
    (values : List Int) (uninhabited : List Bool) (variants : List Summary) : Result Summary := do
  let id := definition.id.index
  let tagSize := tagBits tag / 8
  match definition.layout with
  | none =>
    let payloadSize := variants.foldl (fun out value => max out value.size) 0
    let payloadAlign := variants.foldl (fun out value => max out (value.align.getD 1)) 1
    let payloadOffset ← alignUp tagSize payloadAlign
    let align := max tagSize payloadAlign
    let size ← alignUp (← checked (payloadOffset + payloadSize)) align
    let fields := placePayload payloadOffset variants
    finish mode { size, align := some align, enumeration := some { tag, discriminants := values, encoding := .direct 0, variants := fields, uninhabited } }
  | some descriptor =>
    let variantFields := variants.map (·.fields)
    let reject : Result Summary := .error (.incoherent "enum" id)
    match descriptor.encoding with
    | .untagged => if variants.length != 1 then return ← reject
    | .singleInhabited selected =>
      if !singleInhabitedValid definition descriptor uninhabited selected then return ← reject
    | .direct offset =>
      validLane id descriptor.size descriptor.align offset tagSize tagSize
      if variantFields.any (fun fields => fields.any (fun field =>
          overlap offset tagSize field.offset field.size)) then return ← reject
    | .directWithUninhabited offset profiles =>
      validLane id descriptor.size descriptor.align offset tagSize tagSize
      profileTagLanes id offset tagSize profiles
      if variantFields.any (fun fields => fields.any (fun field =>
          overlap offset tagSize field.offset field.size)) then return ← reject
    | .niche untagged start stop first offset repr =>
      let nicheSize := tagBits repr / 8
      let mask := 2 ^ tagBits repr - 1
      if variants.length ≥ 2 ^ 32 || untagged ≥ variants.length || start > stop || stop ≥ variants.length ||
          first > mask || stop - start > mask then return ← reject
      validLane id descriptor.size descriptor.align offset nicheSize nicheSize
      let covered := (numbered uninhabited).all (fun (uninhabited, position) =>
        uninhabited || position == untagged || (start ≤ position && position ≤ stop))
      if !covered then return ← reject
      let untaggedFields := (trustIrListGet? variantFields untagged).getD []
      if !untaggedFields.any (fun field => field.size != 0 && field.offset ≤ offset &&
          offset + nicheSize ≤ field.offset + field.size) then return ← reject
      if (numbered variantFields).any (fun (fields, position) =>
          position != untagged && start ≤ position && position ≤ stop &&
          fields.any (fun field => overlap offset nicheSize field.offset field.size)) then
        return ← reject
    finish mode { size := descriptor.size, align := some descriptor.align, enumeration := some { tag, discriminants := values, encoding := descriptor.encoding, variants := variantFields, uninhabited } }

/-- A witness of the actual enum finalizer computation, without asserting
that arbitrary supplied child summaries describe valid source layouts. -/
def EnumConstruction (mode : Mode) (definition : EnumDef) (tag : EnumTagRepr)
    (values : List Int) (uninhabited : List Bool) (variants : List Summary) (output : Summary) : Prop :=
  makeEnum mode definition tag values uninhabited variants = .ok output

/-- Exact lane checks performed by the descriptor finalizer. -/
def EnumLaneBounds (size align offset laneSize laneAlign : Nat) : Prop :=
  offset % laneAlign = 0 ∧ laneAlign ≤ align ∧ offset + laneSize ≤ size ∧ offset + laneSize ≤ word64Max

private theorem validLane_bounds (id size align offset laneSize laneAlign : Nat)
    (run : validLane id size align offset laneSize laneAlign = .ok ()) :
    EnumLaneBounds size align offset laneSize laneAlign := by
  unfold validLane at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExceptOf.throw] at run
  cases bounded : checked (offset + laneSize) with
  | error error => simp [bounded] at run
  | ok extent =>
    simp only [bounded] at run
    have exactExtent := checked_ok _ _ bounded
    have aligned : offset % laneAlign = 0 := by
      by_cases good : offset % laneAlign = 0
      · exact good
      · simp [good] at run
    have capped : laneAlign ≤ align := by
      by_cases good : laneAlign ≤ align
      · exact good
      · have bad : align < laneAlign := by omega
        simp [bad] at run
    have contained : extent ≤ size := by
      by_cases good : extent ≤ size
      · exact good
      · have bad : size < extent := by omega
        simp [bad] at run
    exact ⟨aligned, capped, by omega, exactExtent.2⟩

private theorem profileTagLanes_bounds (id offset width : Nat)
    (profiles : List UninhabitedVariantLayout)
    (run : profileTagLanes id offset width profiles = .ok ()) :
    ∀ profile ∈ profiles, EnumLaneBounds profile.size profile.align offset width width := by
  induction profiles with
  | nil => simp
  | cons first rest later =>
    simp only [profileTagLanes, Bind.bind, Except.bind] at run
    cases lane : validLane id first.size first.align offset width width with
    | error error => simp [lane] at run
    | ok unit =>
      cases unit
      simp only [lane] at run
      intro profile member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact validLane_bounds _ _ _ _ _ _ lane
      · exact later run profile member

/-- Boolean outcomes are retained exactly, including structural-fact and
inactive-row checks; they do not authenticate caller-supplied child layouts. -/
def EnumDescriptorChecks (definition : EnumDef) (tag : EnumTagRepr) (uninhabited : List Bool)
    (variants : List Summary) (descriptor : EnumLayoutDescriptor) : Prop :=
  let fields := variants.map (·.fields)
  match descriptor.encoding with
  | .untagged => variants.length = 1
  | .singleInhabited selected => singleInhabitedValid definition descriptor uninhabited selected = true
  | .direct offset =>
      EnumLaneBounds descriptor.size descriptor.align offset (tagBits tag / 8) (tagBits tag / 8) ∧
      fields.any (fun row => row.any (fun field => overlap offset (tagBits tag / 8) field.offset field.size)) = false
  | .directWithUninhabited offset profiles =>
      EnumLaneBounds descriptor.size descriptor.align offset (tagBits tag / 8) (tagBits tag / 8) ∧
      (∀ profile ∈ profiles, EnumLaneBounds profile.size profile.align offset (tagBits tag / 8) (tagBits tag / 8)) ∧
      fields.any (fun row => row.any (fun field => overlap offset (tagBits tag / 8) field.offset field.size)) = false
  | .niche untagged start stop first offset repr =>
      (variants.length ≥ 2 ^ 32 || untagged ≥ variants.length || start > stop || stop ≥ variants.length ||
        first > 2 ^ tagBits repr - 1 || stop - start > 2 ^ tagBits repr - 1) = false ∧
      EnumLaneBounds descriptor.size descriptor.align offset (tagBits repr / 8) (tagBits repr / 8) ∧
      (numbered uninhabited).all (fun (impossible, position) =>
        impossible || position == untagged || (start ≤ position && position ≤ stop)) = true ∧
      ((trustIrListGet? fields untagged).getD []).any (fun field => field.size != 0 && field.offset ≤ offset &&
        offset + tagBits repr / 8 ≤ field.offset + field.size) = true ∧
      (numbered fields).any (fun (row, position) => position != untagged && start ≤ position && position ≤ stop &&
        row.any (fun field => overlap offset (tagBits repr / 8) field.offset field.size)) = false

theorem EnumConstruction.descriptor_finish {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor) :
    finish mode { size := descriptor.size, align := some descriptor.align, enumeration := some { tag, discriminants := values, encoding := descriptor.encoding, variants := variants.map (·.fields), uninhabited } } = .ok output := by
  unfold EnumConstruction makeEnum at constructed
  rw [authored] at constructed
  dsimp only at constructed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExceptOf.throw] at constructed
  repeat first
    | exact constructed
    | (split at constructed)
    | cases constructed

theorem EnumConstruction.descriptor_checks {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor) :
    EnumDescriptorChecks definition tag uninhabited variants descriptor := by
  unfold EnumConstruction makeEnum at constructed
  rw [authored] at constructed
  dsimp only at constructed
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExceptOf.throw] at constructed
  unfold EnumDescriptorChecks
  cases encoding : descriptor.encoding with
  | untagged =>
    simp only [encoding] at constructed ⊢
    by_cases one : variants.length = 1
    · exact one
    · simp [one] at constructed
  | singleInhabited selected =>
    simp only [encoding] at constructed ⊢
    cases selectedValid : singleInhabitedValid definition descriptor uninhabited selected with
    | false => simp [selectedValid] at constructed
    | true => rfl
  | direct offset =>
    simp only [encoding] at constructed ⊢
    cases lane : validLane definition.id.index descriptor.size descriptor.align offset (tagBits tag / 8) (tagBits tag / 8) with
    | error error => simp [lane] at constructed
    | ok unit =>
      cases unit
      simp only [lane] at constructed
      have noOverlap : (variants.map (·.fields)).any (fun row => row.any
          (fun field => overlap offset (tagBits tag / 8) field.offset field.size)) = false := by
        cases h : (variants.map (·.fields)).any (fun row => row.any
            (fun field => overlap offset (tagBits tag / 8) field.offset field.size)) <;> simp_all
      exact ⟨validLane_bounds _ _ _ _ _ _ lane, noOverlap⟩
  | directWithUninhabited offset profiles =>
    simp only [encoding] at constructed ⊢
    cases lane : validLane definition.id.index descriptor.size descriptor.align offset (tagBits tag / 8) (tagBits tag / 8) with
    | error error => simp [lane] at constructed
    | ok unit =>
      cases unit
      simp only [lane] at constructed
      cases checkedProfiles : profileTagLanes definition.id.index offset (tagBits tag / 8) profiles with
      | error error => simp [checkedProfiles] at constructed
      | ok unit =>
        cases unit
        simp only [checkedProfiles] at constructed
        have noOverlap : (variants.map (·.fields)).any (fun row => row.any
            (fun field => overlap offset (tagBits tag / 8) field.offset field.size)) = false := by
          cases h : (variants.map (·.fields)).any (fun row => row.any
              (fun field => overlap offset (tagBits tag / 8) field.offset field.size)) <;> simp_all
        exact ⟨validLane_bounds _ _ _ _ _ _ lane,
          profileTagLanes_bounds _ _ _ _ checkedProfiles, noOverlap⟩
  | niche untagged start stop first offset repr =>
    simp only [encoding] at constructed ⊢
    have ranges : (variants.length ≥ 2 ^ 32 || untagged ≥ variants.length || start > stop || stop ≥ variants.length ||
        first > 2 ^ tagBits repr - 1 || stop - start > 2 ^ tagBits repr - 1) = false := by
      cases h : (variants.length ≥ 2 ^ 32 || untagged ≥ variants.length || start > stop || stop ≥ variants.length ||
        first > 2 ^ tagBits repr - 1 || stop - start > 2 ^ tagBits repr - 1) <;> simp_all
    simp only [ranges, Bool.false_eq_true, ite_false] at constructed
    cases lane : validLane definition.id.index descriptor.size descriptor.align offset (tagBits repr / 8) (tagBits repr / 8) with
    | error error => simp [lane] at constructed
    | ok unit =>
      cases unit
      simp only [lane] at constructed
      have covered : (numbered uninhabited).all (fun (impossible, position) =>
          impossible || position == untagged || (start ≤ position && position ≤ stop)) = true := by
        cases h : (numbered uninhabited).all (fun (impossible, position) =>
          impossible || position == untagged || (start ≤ position && position ≤ stop)) <;> simp_all
      simp only [covered, Bool.not_true, Bool.false_eq_true, ite_false] at constructed
      have carrier : ((trustIrListGet? (variants.map (·.fields)) untagged).getD []).any
          (fun field => field.size != 0 && field.offset ≤ offset && offset + tagBits repr / 8 ≤ field.offset + field.size) = true := by
        cases h : ((trustIrListGet? (variants.map (·.fields)) untagged).getD []).any
          (fun field => field.size != 0 && field.offset ≤ offset && offset + tagBits repr / 8 ≤ field.offset + field.size) <;> simp_all
      simp only [carrier, Bool.not_true, Bool.false_eq_true, ite_false] at constructed
      have disjoint : (numbered (variants.map (·.fields))).any (fun (row, position) =>
          position != untagged && start ≤ position && position ≤ stop &&
          row.any (fun field => overlap offset (tagBits repr / 8) field.offset field.size)) = false := by
        cases h : (numbered (variants.map (·.fields))).any (fun (row, position) =>
          position != untagged && start ≤ position && position ≤ stop &&
          row.any (fun field => overlap offset (tagBits repr / 8) field.offset field.size)) <;> simp_all
      exact ⟨ranges, validLane_bounds _ _ _ _ _ _ lane, covered, carrier, disjoint⟩

/-- Successful canonical construction exposes the exact checked payload plan
and the original final guard, not a separately recomputed layout oracle. -/
theorem EnumConstruction.canonical_view {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none) :
    ∃ offset extent size,
      alignUp (tagBits tag / 8) (variants.foldl (fun out value => max out (value.align.getD 1)) 1) = .ok offset ∧
      checked (offset + variants.foldl (fun out value => max out value.size) 0) = .ok extent ∧
      alignUp extent (max (tagBits tag / 8) (variants.foldl (fun out value => max out (value.align.getD 1)) 1)) = .ok size ∧
      finish mode { size, align := some (max (tagBits tag / 8) (variants.foldl (fun out value => max out (value.align.getD 1)) 1)), enumeration := some { tag, discriminants := values, encoding := .direct 0, variants := placePayload offset variants, uninhabited } } = .ok output := by
  unfold EnumConstruction makeEnum at constructed
  rw [canonical] at constructed
  dsimp only at constructed
  simp only [Bind.bind, Except.bind] at constructed
  cases placed : alignUp (tagBits tag / 8) (variants.foldl (fun out value => max out (value.align.getD 1)) 1) with
  | error error => simp [placed] at constructed
  | ok offset =>
    simp only [placed] at constructed
    cases bounded : checked (offset + variants.foldl (fun out value => max out value.size) 0) with
    | error error => simp [bounded] at constructed
    | ok extent =>
      simp only [bounded] at constructed
      cases rounded : alignUp extent (max (tagBits tag / 8)
          (variants.foldl (fun out value => max out (value.align.getD 1)) 1)) with
      | error error => simp [rounded] at constructed
      | ok size =>
        simp only [rounded] at constructed
        exact ⟨offset, extent, size, rfl, bounded, rounded, constructed⟩

private def enumHeaderInvalid (definition : EnumDef) (uninhabited : List Bool)
    (count : Nat) (descriptor : EnumLayoutDescriptor) : Bool :=
  !powerOfTwo descriptor.align || descriptor.size % descriptor.align != 0 ||
    descriptor.variantFieldOffsets.length != count ||
    (match descriptor.encoding with
      | .singleInhabited selected => !singleInhabitedValid definition descriptor uninhabited selected
      | _ => false)

private def descriptorInitial (mode : Mode) (definition : EnumDef) (tag : EnumTagRepr)
    (uninhabited : List Bool) (count : Nat) (referencesValid : Bool)
    (descriptor : EnumLayoutDescriptor) : Result (List Summary) := do
  let id := definition.id.index
  if enumHeaderInvalid definition uninhabited count descriptor then
    throw (.incoherent "enum" id)
  match descriptor.encoding with
  | .directWithUninhabited offset profiles =>
    let _ ← checked descriptor.size
    let _ ← checked descriptor.align
    validLane id descriptor.size descriptor.align offset (tagBits tag / 8) (tagBits tag / 8)
    if !referencesValid || !directProfilesCover definition uninhabited profiles then
      throw (.incoherent "enum" id)
    for profile in profiles do
      let source ← match trustIrListGet? definition.variants profile.variant with
        | some source => pure source | none => throw (.incoherent "enum" id)
      let storage ← uninhabitedVariant mode id descriptor profile source.fields
      validLane id profile.size profile.align offset (tagBits tag / 8) (tagBits tag / 8)
      if storage.fields.any (fun field =>
          overlap offset (tagBits tag / 8) field.offset field.size) then
        throw (.incoherent "enum" id)
  | _ => pure ()
  pure []

private theorem descriptorInitial_view (mode : Mode) (definition : EnumDef) (tag : EnumTagRepr)
    (uninhabited : List Bool) (count : Nat) (referencesValid : Bool)
    (descriptor : EnumLayoutDescriptor) (state : List Summary)
    (run : descriptorInitial mode definition tag uninhabited count referencesValid descriptor = .ok state) :
    enumHeaderInvalid definition uninhabited count descriptor = false ∧ state = [] := by
  have header : enumHeaderInvalid definition uninhabited count descriptor = false := by
    cases invalid : enumHeaderInvalid definition uninhabited count descriptor with
    | false => rfl
    | true =>
      unfold descriptorInitial at run
      rw [invalid] at run
      cases run
  refine ⟨header, ?_⟩
  -- Each successful check preserves the initializer's exact empty state.
  -- The profile loop contributes its actual result without unfolding its body.
  have completed : ∀ checks : Result Unit,
      (do let _ ← checks; pure ([] : List Summary)) = .ok state → state = [] := by
    intro checks success
    cases checks with
    | error error => cases success
    | ok unit => cases success; rfl
  unfold descriptorInitial at run
  rw [header] at run
  dsimp only at run
  cases encoding : descriptor.encoding with
  | direct offset => rw [encoding] at run; cases run; rfl
  | niche selected first last start offset ty => rw [encoding] at run; cases run; rfl
  | untagged => rw [encoding] at run; cases run; rfl
  | singleInhabited selected => rw [encoding] at run; cases run; rfl
  | directWithUninhabited offset profiles =>
    rw [encoding] at run
    dsimp only at run
    cases sizeCheck : checked descriptor.size with
    | error error => rw [sizeCheck] at run; cases run
    | ok size =>
      rw [sizeCheck] at run
      cases alignCheck : checked descriptor.align with
      | error error => rw [alignCheck] at run; cases run
      | ok align =>
        rw [alignCheck] at run
        cases laneCheck : validLane definition.id.index descriptor.size descriptor.align offset
            (tagBits tag / 8) (tagBits tag / 8) with
        | error error => rw [laneCheck] at run; cases run
        | ok unit =>
          rw [laneCheck] at run
          cases references : (!referencesValid || !directProfilesCover definition uninhabited profiles) with
          | true => rw [references] at run; cases run
          | false =>
            rw [references] at run
            exact completed (forIn profiles PUnit.unit _) run

/-- Variant nodes finish their own field checks before the next variant is
    requested. Tag and niche placement then use the complete source plan. -/
def enumEquation (mode : Mode) (definition : EnumDef) (uninhabited : List Bool)
    (variants : List Nat) (referencesValid : Bool := true) : Equation :=
  let id := definition.id.index
  match canonicalTag definition, discriminants definition with
  | some tag, some values =>
    { kind := .variants
      initial := match definition.layout with
        | none => .ok []
        | some descriptor =>
          descriptorInitial mode definition tag uninhabited variants.length referencesValid descriptor
      steps := variants.map (fun child => .child child fun value state => .ok (value :: state))
      finish := fun state => makeEnum mode definition tag values uninhabited state.reverse }
  | _, _ => .done (.error (.incoherent "enum" id))

/-- Actual finite execution exposes the collected summaries and the precise
finalizer call, retaining the computed tag and discriminant outcomes. -/
theorem Equation.Executes.canonicalEnum_view {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∃ tag values state,
      canonicalTag definition = some tag ∧ discriminants definition = some values ∧
      StepsDerivation graph (nodes.map (fun child => .child child fun value state => .ok (value :: state))) [] state ∧
      EnumConstruction mode definition tag values uninhabited state.reverse output := by
  cases ht : canonicalTag definition with
  | none =>
    have selected : enumEquation mode definition uninhabited nodes =
        Equation.done (.error (.incoherent "enum" definition.id.index)) := by
      unfold enumEquation
      rw [ht]
    rw [selected] at run
    rcases run with ⟨first, last, impossible, steps, finished⟩
    cases impossible
  | some tag =>
    cases hv : discriminants definition with
    | none =>
      have selected : enumEquation mode definition uninhabited nodes =
          Equation.done (.error (.incoherent "enum" definition.id.index)) := by
        unfold enumEquation
        rw [ht, hv]
      rw [selected] at run
      rcases run with ⟨first, last, impossible, steps, finished⟩
      cases impossible
    | some values =>
      have selected : enumEquation mode definition uninhabited nodes =
          { kind := .variants, initial := .ok [],
            steps := nodes.map (fun child => .child child fun value state => .ok (value :: state)),
            finish := fun state => makeEnum mode definition tag values uninhabited state.reverse } := by
        unfold enumEquation
        rw [ht, hv]
        dsimp only
        rw [canonical]
      rw [selected] at run
      rcases run with ⟨first, last, initial, steps, finished⟩
      cases initial
      exact ⟨tag, values, last, rfl, rfl, steps, finished⟩

/-- Descriptor execution also retains the actual aggregate-header check
before requesting any physical child. -/
theorem Equation.Executes.descriptorEnum_view {graph : Graph} {output : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (run : (enumEquation mode definition uninhabited nodes).Executes graph output) :
    ∃ tag values state,
      canonicalTag definition = some tag ∧ discriminants definition = some values ∧
      (!powerOfTwo descriptor.align || descriptor.size % descriptor.align != 0 ||
        descriptor.variantFieldOffsets.length != nodes.length ||
        (match descriptor.encoding with
          | .singleInhabited selected => !singleInhabitedValid definition descriptor uninhabited selected
          | _ => false)) = false ∧
      StepsDerivation graph (nodes.map (fun child => .child child fun value state => .ok (value :: state))) [] state ∧
      EnumConstruction mode definition tag values uninhabited state.reverse output := by
  cases ht : canonicalTag definition with
  | none =>
    have selected : enumEquation mode definition uninhabited nodes =
        Equation.done (.error (.incoherent "enum" definition.id.index)) := by
      unfold enumEquation
      rw [ht]
    rw [selected] at run
    rcases run with ⟨first, last, impossible, steps, finished⟩
    cases impossible
  | some tag =>
    cases hv : discriminants definition with
    | none =>
      have selected : enumEquation mode definition uninhabited nodes =
          Equation.done (.error (.incoherent "enum" definition.id.index)) := by
        unfold enumEquation
        rw [ht, hv]
      rw [selected] at run
      rcases run with ⟨first, last, impossible, steps, finished⟩
      cases impossible
    | some values =>
      have selected : enumEquation mode definition uninhabited nodes =
          { kind := .variants
            initial := descriptorInitial mode definition tag uninhabited nodes.length true descriptor
            steps := nodes.map (fun child => .child child fun value state => .ok (value :: state))
            finish := fun state => makeEnum mode definition tag values uninhabited state.reverse } := by
        unfold enumEquation
        rw [ht, hv]
        dsimp only
        rw [authored]
      rw [selected] at run
      rcases run with ⟨first, last, initial, steps, finished⟩
      obtain ⟨admitted, empty⟩ := descriptorInitial_view mode definition tag uninhabited
        nodes.length true descriptor first initial
      cases empty
      exact ⟨tag, values, last, rfl, rfl, admitted, steps, finished⟩

/-- Every successful enum construction passes its actual final summary through
`finish`, including all descriptor encodings and the canonical layout path. -/
private theorem makeEnum_finish_property (mode : Mode) (definition : EnumDef)
    (tag : EnumTagRepr) (values : List Int) (uninhabited : List Bool)
    (variants : List Summary) (property : Summary → Prop)
    (safe : ∀ input output, finish mode input = .ok output → property output)
    (output : Summary)
    (success : makeEnum mode definition tag values uninhabited variants = .ok output) :
    property output := by
  unfold makeEnum at success
  try dsimp only at success
  split at success
  · simp only [Except.bind, Bind.bind] at success
    repeat first
      | exact safe _ _ success
      | (split at success)
      | (cases success)
  · split at success
    all_goals simp only [Except.bind, Except.pure, Bind.bind, Pure.pure,
      MonadExceptOf.throw] at success
    all_goals repeat first
      | exact safe _ _ success
      | (split at success)
      | (cases success)

/-- The full enum equation's finalizer inherits any successful `finish`
property; no child-layout or source-metadata validity oracle is required. -/
theorem enumEquation_finish_property (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) (property : Summary → Prop)
    (safe : ∀ input output, finish mode input = .ok output → property output)
    (state : (enumEquation mode definition uninhabited variants).State)
    (output : Summary)
    (success : (enumEquation mode definition uninhabited variants).finish state = .ok output)
    (initial : ∃ first, (enumEquation mode definition uninhabited variants).initial = .ok first) :
    property output := by
  revert state
  cases ht : canonicalTag definition <;> cases hv : discriminants definition
  all_goals unfold enumEquation at initial ⊢
  all_goals dsimp only at initial ⊢
  all_goals rw [ht, hv] at initial ⊢
  all_goals dsimp only [Equation.done] at initial ⊢
  all_goals first
    | (rcases initial with ⟨first, impossible⟩; cases impossible)
    | (intro state success
       exact makeEnum_finish_property mode definition _ _ uninhabited _ property safe output success)

end TrustIr.SourceLayout
