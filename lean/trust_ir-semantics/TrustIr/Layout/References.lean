-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Extension
import TrustIr.Layout.Enums

namespace TrustIr.SourceLayout

/-- All child requests, including requests after checks, stay in a region.
Checks and their ordering remain the original equation's executable functions. -/
def StepsIn (region : Nat → Prop) {σ : Type} (steps : List (Step σ)) : Prop :=
  steps.foldr (fun step rest => match step with
    | .check _ => rest
    | .child node _ => region node ∧ rest) True

/-- Every node in a region has its original equation, whose entire dependency
list stays in that region. The graph may contain unrelated open components. -/
def Graph.ClosedRegion (graph : Graph) (region : Nat → Prop) : Prop :=
  ∀ node, region node → ∃ equation, graph.nodes.find node = some equation ∧ StepsIn region equation.steps

/-- Every child reference in every installed equation is below the graph's
allocation frontier. This does not imply the referenced equation is installed. -/
def Graph.ReferenceBounds (graph : Graph) : Prop :=
  ∀ node equation, graph.nodes.find node = some equation → StepsIn (fun child => child < graph.count) equation.steps

/-- Every reserved or allocated node below the frontier has an equation. -/
def Graph.Complete (graph : Graph) : Prop :=
  ∀ node, node < graph.count → ∃ equation, graph.nodes.find node = some equation

/-- Equation presence, without asserting its contents or successful evaluation. -/
def Graph.Present (graph : Graph) (node : Nat) : Prop := ∃ equation, graph.nodes.find node = some equation

/-- Domain growth retains old installed nodes and fills every newly allocated
slot. Reserved slots below the old frontier may still be absent. -/
structure Graph.DomainCovers (before after : Graph) : Prop where
  count_mono : before.count ≤ after.count
  old : ∀ node, before.Present node → after.Present node
  fresh : ∀ node, before.count ≤ node → node < after.count → after.Present node

theorem Graph.DomainCovers.refl (graph : Graph) : graph.DomainCovers graph :=
  ⟨Nat.le_refl _,fun _ found => found,fun _ lower upper => by omega⟩

theorem Graph.DomainCovers.trans {first middle last : Graph}
    (left : first.DomainCovers middle) (right : middle.DomainCovers last) : first.DomainCovers last := by
  refine ⟨Nat.le_trans left.count_mono right.count_mono,fun node found => right.old node (left.old node found),?_⟩
  intro node lower upper
  by_cases earlier : node < middle.count
  · exact right.old node (left.fresh node lower earlier)
  · exact right.fresh node (by omega) upper

theorem Graph.present_insert (graph : Graph) (node : Nat) (equation : Equation) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).Present node :=
  ⟨equation,by simp [NatIndexTree.find_insert]⟩

theorem Graph.DomainCovers.write (graph : Graph) (node : Nat) (equation : Equation) :
    graph.DomainCovers { graph with nodes := graph.nodes.insert node equation } := by
  refine ⟨Nat.le_refl _,?_,?_⟩
  · intro query found
    by_cases same : query = node
    · subst query; exact Graph.present_insert graph node equation
    · obtain ⟨old,lookup⟩ := found
      exact ⟨old,by change (graph.nodes.insert node equation).find query = some old; rw [NatIndexTree.find_insert,if_neg same]; exact lookup⟩
  · intro query lower upper
    change query < graph.count at upper
    omega

theorem Graph.DomainCovers.allocate (graph : Graph) (equation : Equation) :
    graph.DomainCovers { graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } := by
  have written := Graph.DomainCovers.write graph graph.count equation
  refine ⟨Nat.le_succ _,written.old,?_⟩
  intro node lower upper
  have same : node = graph.count := by change node < graph.count + 1 at upper; omega
  subst node
  exact Graph.present_insert graph graph.count equation

theorem Graph.DomainCovers.complete_with_reserved {before after : Graph} (coverage : before.DomainCovers after)
    (reserved : ∀ node, node < before.count → after.Present node) : after.Complete := by
  intro node inside
  by_cases original : node < before.count
  · exact reserved node original
  · exact coverage.fresh node (by omega) inside

/-- Replacing equations cannot create holes when the initial domain was complete. -/
theorem Graph.DomainCovers.complete {before after : Graph} (coverage : before.DomainCovers after)
    (complete : before.Complete) : after.Complete :=
  coverage.complete_with_reserved (fun node inside => coverage.old node (complete node inside))

def CoversGraph {α : Type} (action : StateM Graph α) : Prop := ∀ (graph : Graph), graph.DomainCovers (action graph).2

theorem CoversGraph.pure {α : Type} (value : α) : CoversGraph (pure value : StateM Graph α) := fun graph => .refl graph

theorem CoversGraph.get : CoversGraph (get : StateM Graph Graph) := fun graph => .refl graph

theorem CoversGraph.bind {α β : Type} {action : StateM Graph α} {next : α → StateM Graph β}
    (first : CoversGraph action) (later : ∀ value, CoversGraph (next value)) : CoversGraph (action >>= next) :=
  fun graph => (first graph).trans (later (action graph).1 (action graph).2)

theorem CoversGraph.forIn {α β : Type} (rows : List α) (initial : β)
    (body : α → β → StateM Graph (ForInStep β)) (safe : ∀ row, row ∈ rows → ∀ acc, CoversGraph (body row acc)) :
    CoversGraph (forIn rows initial body) := by
  induction rows generalizing initial with
  | nil => rw [List.forIn_nil]; exact CoversGraph.pure _
  | cons first rest ih =>
    rw [List.forIn_cons]
    apply CoversGraph.bind (safe first ((trustIrListMemConsSelf _ _)) initial)
    intro step
    cases step with
    | done value => exact CoversGraph.pure _
    | yield value => exact ih value (fun row member => safe row (List.mem_cons_of_mem _ member))

def Installs {α : Type} (node : Nat) (action : StateM Graph α) : Prop :=
  ∀ graph, (action graph).2.Present node

theorem Installs.bind_left {α β : Type} {node : Nat} {action : StateM Graph α} {next : α → StateM Graph β}
    (installed : Installs node action) (later : ∀ value, CoversGraph (next value)) : Installs node (action >>= next) :=
  fun graph => (later (action graph).1 (action graph).2).old node (installed graph)

theorem Installs.bind_right {α β : Type} {node : Nat} (action : StateM Graph α) {next : α → StateM Graph β}
    (later : ∀ value, Installs node (next value)) : Installs node (action >>= next) :=
  fun graph => later (action graph).1 (action graph).2

theorem Installs.forIn_member {α : Type} (rows : List α)
    (body : α → Unit → StateM Graph (ForInStep Unit)) (destination : α → Nat)
    (covers : ∀ row, CoversGraph (body row ()))
    (yields : ∀ row graph, (body row () graph).1 = .yield ())
    (writes : ∀ row, Installs (destination row) (body row ()))
    (row : α) (member : row ∈ rows) : Installs (destination row) (forIn rows () body) := by
  induction rows generalizing row with
  | nil => cases member
  | cons first rest ih =>
    intro graph
    have selected := yields first graph
    cases executed : body first () graph with
    | mk outcome after =>
      rw [executed] at selected
      cases selected
      have covered : CoversGraph (forIn rest () body) :=
        CoversGraph.forIn rest () body (fun row _ acc => by cases acc; exact covers row)
      rcases List.mem_cons.mp member with same | later
      · subst row
        have installed := writes first graph
        rw [executed] at installed
        have retained := (covered after).old (destination first) installed
        simpa only [List.forIn_cons,Bind.bind,StateT.bind,executed] using retained
      · have retained := ih row later after
        simpa only [List.forIn_cons,Bind.bind,StateT.bind,executed] using retained

theorem StepsIn.mono {first second : Nat → Prop} {σ : Type} {steps : List (Step σ)}
    (included : ∀ node, first node → second node) (safe : StepsIn first steps) : StepsIn second steps := by
  induction steps with
  | nil => trivial
  | cons step rest ih =>
    cases step with
    | check update => exact ih safe
    | child node update => exact ⟨included node safe.1,ih safe.2⟩

theorem StepsIn.append {region : Nat → Prop} {σ : Type} {left right : List (Step σ)}
    (first : StepsIn region left) (second : StepsIn region right) : StepsIn region (left ++ right) := by
  induction left with
  | nil => exact second
  | cons step rest ih =>
    cases step with
    | check update => exact ih first
    | child node update => exact ⟨first.1,ih first.2⟩

theorem StepsIn.children {region : Nat → Prop} {α σ : Type} (rows : List α) (node : α → Nat)
    (update : α → Summary → σ → Except Error σ)
    (safe : ∀ row ∈ rows, region (node row)) :
    StepsIn region (rows.map (fun row => .child (node row) (update row))) := by
  induction rows with
  | nil => trivial
  | cons first rest ih =>
    exact ⟨safe first ((trustIrListMemConsSelf _ _)),ih (fun row member => safe row (List.mem_cons_of_mem _ member))⟩

theorem Equation.references_done (region : Nat → Prop) (result : Except Error Summary) :
    StepsIn region (Equation.done result).steps := True.intro

theorem Equation.references_alias {region : Nat → Prop} (node : Nat) (safe : region node) :
    StepsIn region (Equation.alias node).steps := ⟨safe,True.intro⟩

theorem Equation.references_scaled {region : Nat → Prop} (mode : Mode) (count node : Nat) (safe : region node) :
    StepsIn region (scaled mode count node).steps := ⟨safe,True.intro⟩

theorem Equation.references_canonicalFields {region : Nat → Prop} (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) (safe : ∀ field ∈ fields, region field.2) :
    StepsIn region (canonicalFields mode kind id fields).steps :=
  StepsIn.children fields (·.2) _ safe

theorem Equation.references_declaredFields {region : Nat → Prop} (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat))
    (safe : ∀ field ∈ fields, region field.2.2) :
    StepsIn region (declaredFields mode kind id size align clamp transparent fields).steps :=
  StepsIn.children fields (·.2.2) _ safe

theorem Equation.references_enum {region : Nat → Prop} (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) (safe : ∀ node ∈ variants, region node) :
    StepsIn region (enumEquation mode definition uninhabited variants).steps := by
  cases ht : canonicalTag definition with
  | none => unfold enumEquation; rw [ht]; exact True.intro
  | some tag =>
    cases hv : discriminants definition with
    | none => unfold enumEquation; rw [ht,hv]; exact True.intro
    | some values =>
      unfold enumEquation
      rw [ht,hv]
      exact StepsIn.children variants id _ safe

theorem Equation.references_sequence {region : Nat → Prop} (children : List Nat) (next : Equation)
    (prefixSafe : ∀ node ∈ children, region node) (nextSafe : StepsIn region next.steps) :
    StepsIn region (Equation.sequence children next).steps := by
  unfold Equation.sequence
  apply StepsIn.append
  · apply StepsIn.append
    · exact StepsIn.children children id _ prefixSafe
    · exact True.intro
  · change StepsIn region (next.steps.map _)
    generalize entriesEq : next.steps = entries at nextSafe ⊢
    clear entriesEq
    induction entries with
    | nil => trivial
    | cons step rest ih =>
      cases step with
      | check update => exact ih nextSafe
      | child node update => exact ⟨nextSafe.1,ih nextSafe.2⟩

theorem Equation.references_canonicalZip {region : Nat → Prop} (mode : Mode) (kind : String) (id : Nat)
    (fields : List Ty) (nodes : List Nat) (safe : ∀ node ∈ nodes, region node) :
    StepsIn region (canonicalFields mode kind id (fields.zip nodes)).steps := by
  induction fields generalizing nodes with
  | nil => trivial
  | cons field rest ih =>
    cases nodes with
    | nil => trivial
    | cons node nodes =>
      exact ⟨safe node ((trustIrListMemConsSelf _ _)),ih nodes (fun child member => safe child (List.mem_cons_of_mem _ member))⟩

theorem Equation.references_declaredZip {region : Nat → Prop} (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List Ty) (nodes offsets : List Nat)
    (safe : ∀ node ∈ nodes, region node) :
    StepsIn region (declaredFields mode kind id size align clamp transparent
      ((fields.zip nodes).zip offsets |>.map (fun ((ty,child),offset) => (ty,some offset,child)))).steps := by
  induction fields generalizing nodes offsets with
  | nil => trivial
  | cons field rest ih =>
    cases nodes with
    | nil => trivial
    | cons node nodes =>
      cases offsets with
      | nil => trivial
      | cons offset offsets =>
        exact ⟨safe node ((trustIrListMemConsSelf _ _)),ih nodes offsets (fun child member => safe child (List.mem_cons_of_mem _ member))⟩

theorem Equation.references_declaredMapZip {region : Nat → Prop} {α : Type}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List α) (ty : α → Ty) (offset : α → Option Nat) (nodes : List Nat)
    (safe : ∀ node ∈ nodes, region node) :
    StepsIn region (declaredFields mode kind id size align clamp transparent
      (fields.zip nodes |>.map (fun (field,child) => (ty field,offset field,child)))).steps := by
  induction fields generalizing nodes with
  | nil => trivial
  | cons field rest ih =>
    cases nodes with
    | nil => trivial
    | cons node nodes =>
      exact ⟨safe node ((trustIrListMemConsSelf _ _)),ih nodes (fun child member => safe child (List.mem_cons_of_mem _ member))⟩

theorem Equation.references_variantFields {region : Nat → Prop} (mode : Mode) (id size align : Nat)
    (children : List (Ty × Nat)) (offsets : List Nat) (safe : ∀ child ∈ children, region child.2) :
    StepsIn region (declaredFields mode "enum" id size align word64Max false
      (children.zip offsets |>.map (fun ((ty,child),offset) => (ty,some offset,child)))).steps := by
  induction children generalizing offsets with
  | nil => trivial
  | cons child children ih =>
    rcases child with ⟨ty,node⟩
    cases offsets with
    | nil => trivial
    | cons offset offsets =>
      exact ⟨safe (ty,node) ((trustIrListMemConsSelf _ _)),
        ih offsets (fun child member => safe child (List.mem_cons_of_mem _ member))⟩

theorem Graph.ReferenceBounds.empty (count : Nat) : ({ count := count } : Graph).ReferenceBounds := by
  intro node equation absent
  cases absent

theorem Graph.ReferenceBounds.insert {graph : Graph} (valid : graph.ReferenceBounds)
    (count : Nat) (growth : graph.count ≤ count) (node : Nat) (equation : Equation)
    (safe : StepsIn (fun child => child < count) equation.steps) :
    ({ graph with nodes := graph.nodes.insert node equation, count := count } : Graph).ReferenceBounds := by
  intro query actual found
  change (graph.nodes.insert node equation).find query = some actual at found
  rw [NatIndexTree.find_insert] at found
  split at found
  · cases found; exact safe
  · exact (valid query actual found).mono (fun _ inside => Nat.lt_of_lt_of_le inside growth)

/-- Bounds plus installation, rather than either condition alone, establish
closure of the complete prepared prefix. -/
theorem Graph.closed_prefix {graph : Graph} (bounds : graph.ReferenceBounds) (complete : graph.Complete) :
    graph.ClosedRegion (fun node => node < graph.count) := by
  intro node inside
  obtain ⟨equation,found⟩ := complete node inside
  exact ⟨equation,found,bounds node equation found⟩

end TrustIr.SourceLayout
