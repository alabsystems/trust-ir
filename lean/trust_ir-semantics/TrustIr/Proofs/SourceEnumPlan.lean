-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceEnumGraph
import TrustIr.Semantics.AggregatePlans

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Resolution of the original source's type row, including missing rows. -/
def SourceElement (source : Environment) (id : TyId) (ty : Ty) : Prop :=
  ((trustIrListGet? source.types id.index)).join = some ty

theorem SourceElement.row {source : Environment} {id : TyId} {ty : Ty}
    (resolved : SourceElement source id ty) : (trustIrListGet? source.types id.index) = some (some ty) := by
  unfold SourceElement at resolved
  cases row : (trustIrListGet? source.types id.index) with
  | none => rw [row] at resolved; cases resolved
  | some actual =>
    cases actual with
    | none => rw [row] at resolved; cases resolved
    | some actual => rw [row] at resolved; cases resolved; rfl

theorem SourceElement.functional {source : Environment} {id : TyId} {first second : Ty}
    (left : SourceElement source id first) (right : SourceElement source id second) :
    first = second := by
  have same := left.symm.trans right
  cases same
  rfl

/-- A typed summary from an actual query in the original source's history. -/
def ActualSummary (source : Environment) (ty : Ty) (value : Summary) : Prop :=
  ∃ before next : Session, Session.Reachable source before ∧
    before.query .execution ty = .ok (value,next)

theorem actual_summary_policy (source : Environment) :
    QueryOriginPolicy (SourceElement source) (ActualSummary source) (Session.Reachable source) := by
  constructor
  · intro session history ty value next run
    exact ⟨⟨session,next,history,run⟩,.queried history run⟩
  · intro session history id ty row
    rw [history.index_eq] at row
    change ((trustIrArrayGet? source.types.toArray id.index)).join = some ty at row
    change ((trustIrListGet? source.types id.index)).join = some ty
    trustIrCompilerProof {
      simpa only [Array.get?_eq_getElem?,CompilerCompat.getElem?_toArray] using row
    } {
      simpa only [CompilerCompat.getElem?_toArray] using row
    }

theorem prepared_plan_origin (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (run : (prepare source roots).query ty = .ok plan) : Plan.Origin (SourceElement source) (ActualSummary source) ty plan :=
  prepare_query_origin (SourceElement source) (ActualSummary source) (Session.Reachable source) (actual_summary_policy source)
    source .prepared roots ty plan run

theorem prepared_enum_plan_view (source : Environment) (roots : List Ty) (id : EnumId) (plan : Plan)
    (run : (prepare source roots).query (.Enum id) = .ok plan) :
    ∃ layout info variants value, plan = .enumeration (.Enum id) layout info variants ∧
      ActualSummary source (.Enum id) value ∧ value.enumeration = some info ∧
      VariantOrigins (SourceElement source) (ActualSummary source) info.uninhabited variants :=
  (prepared_plan_origin source roots (.Enum id) plan run).enum_view

/-- Actual plan metadata keeps the original physical source occurrence,
    exact execution mode and computed flags, including prepared-cache hits. -/
theorem prepared_enum_plan_source (source : Environment) (roots : List Ty) (id : EnumId) (plan : Plan)
    (run : (prepare source roots).query (.Enum id) = .ok plan) :
    ∃ layout info variants value position definition,
      plan = .enumeration (.Enum id) layout info variants ∧ value.enumeration = some info ∧
      (trustIrListGet? source.enums position) = some definition ∧ definition.id = id ∧
      EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) .execution definition value ∧
      VariantOrigins (SourceElement source) (ActualSummary source) info.uninhabited variants := by
  obtain ⟨layout,info,variants,value,shape,actual,present,children⟩ := prepared_enum_plan_view source roots id plan run
  obtain ⟨before,next,history,queried⟩ := actual
  obtain ⟨position,definition,row,identity,origin⟩ := history.query_enum_origin .execution id value queried
  exact ⟨layout,info,variants,value,position,definition,shape,present,row,identity,origin,children⟩

/-- An actually accepted initialized active capture has a present payload
    plan at its actual capture-selected position. Codec selection agreement
    and child-field source typing are separate obligations. -/
theorem prepared_enum_active_payload (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (roots : List Ty) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (plan : Plan) (run : (prepare source roots).query (.Enum id) = .ok plan)
    (fuel : Nat) (values : List Value) (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ layout info variants tag payload position variant fields,
      plan = .enumeration (.Enum id) layout info variants ∧ values = tag :: payload ∧
      EnumTagSelects definition tag position ∧ (trustIrListGet? definition.variants position) = some variant ∧
      (trustIrListGet? info.uninhabited position) = some false ∧ (trustIrListGet? variants position) = some (some fields) ∧
      ∀ field ∈ fields, Plan.Origin (SourceElement source) (ActualSummary source) field.2.ty field.2 := by
  obtain ⟨layout,info,variants,value,shape,actual,present,children⟩ := prepared_enum_plan_view source roots id plan run
  obtain ⟨before,next,history,queried⟩ := actual
  obtain ⟨tag,payload,position,variant,valuesShape,selected,row,flag⟩ :=
    history.query_enum_capture_active_flag_false ctx associated admitted .execution id definition resolved
      value info present queried fuel values initialized checked
  obtain ⟨fields,found,origins⟩ := children.live_at position flag
  exact ⟨layout,info,variants,tag,payload,position,variant,fields,shape,valuesShape,selected,row,flag,found,origins⟩

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.PlanOriginControls

theorem live_unit_payload (resolves : TyId → Ty → Prop) (valid : Ty → SourceLayout.Summary → Prop) :
    VariantOrigins resolves valid [false] [some []] :=
  .live (by intro field member; cases member) .nil

theorem ordered_payloads (resolves : TyId → Ty → Prop) (valid : Ty → SourceLayout.Summary → Prop) :
    VariantOrigins resolves valid [true,false] [none,some []] := .omitted (live_unit_payload resolves valid)

theorem false_flag_cannot_be_absent (resolves : TyId → Ty → Prop) (valid : Ty → SourceLayout.Summary → Prop) :
    ¬ VariantOrigins resolves valid [false] [none] := by
  intro origin
  have wrong := (origin.absent_iff 0).mp rfl
  cases wrong

theorem true_flag_cannot_be_present (resolves : TyId → Ty → Prop) (valid : Ty → SourceLayout.Summary → Prop) :
    ¬ VariantOrigins resolves valid [true] [some []] := by
  intro origin
  have wrong := (origin.absent_iff 0).mpr rfl
  cases wrong

theorem equal_lengths_do_not_authenticate_order (resolves : TyId → Ty → Prop) (valid : Ty → SourceLayout.Summary → Prop) :
    ¬ VariantOrigins resolves valid [false,true] [none,some []] := by
  intro origin
  have wrong := (origin.absent_iff 0).mp rfl
  cases wrong

theorem enum_cannot_use_scalar_plan (resolves : TyId → Ty → Prop) (valid : Ty → SourceLayout.Summary → Prop) (id : EnumId)
    (layout : MemoryTypeLayout) : ¬ Plan.Origin resolves valid (.Enum id) (.leaf (.Enum id) layout) := by
  intro origin
  cases origin with
  | leaf ty layout kind value summary extent => exact kind

private def definition : EnumDef :=
  { id := ⟨0⟩, name := "NeverOrUnit",
    variants := [{ name := "Never", fields := [.Never] }, { name := "Unit", fields := [] }] }
private def source : SourceLayout.Environment := { enums := [definition] }
private def info : SourceLayout.Enumeration :=
  { tag := .u8, discriminants := [0,1],
    encoding := .direct 0, variants := [[],[]], uninhabited := [false,false] }

theorem forged_flags_have_no_actual_summary (value : SourceLayout.Summary)
    (present : value.enumeration = some info) : ¬ ActualSummary source (.Enum ⟨0⟩) value := by
  intro actual
  obtain ⟨before,next,history,queried⟩ := actual
  obtain ⟨position,actualDefinition,row,identity,origin⟩ := history.query_enum_origin .execution ⟨0⟩ value queried
  have member := SourceLayout.numbered_source_member source.enums actualDefinition position
    ((SourceLayout.numbered_member_iff_get _ _ _).2 row)
  change actualDefinition ∈ [definition] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst actualDefinition
  have flags := origin.flags info present
  change [false,false] = [true,false] at flags
  have wrong := (List.cons.inj flags).1
  cases wrong

theorem forged_plan_has_no_actual_origin :
    ¬ Plan.Origin (SourceElement source) (ActualSummary source) (.Enum ⟨0⟩)
      (.enumeration (.Enum ⟨0⟩) ⟨1,1⟩ info [some [],some []]) := by
  intro origin
  obtain ⟨layout,enumeration,variants,value,shape,actual,present,children⟩ := origin.enum_view
  cases shape
  exact forged_flags_have_no_actual_summary value present actual

end TrustIr.AggregateMemory.PlanOriginControls
