-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.References

namespace TrustIr.SourceLayout

/-- Ordered checks and updates are identical; only child node numbers vary. -/
inductive StepsCorrespond (relation : Nat → Nat → Prop) {σ : Type} :
    List (Step σ) → List (Step σ) → Prop where
  | nil : StepsCorrespond relation [] []
  | check (update : σ → Except Error σ) {left right : List (Step σ)}
      (later : StepsCorrespond relation left right) :
      StepsCorrespond relation (.check update :: left) (.check update :: right)
  | child (update : Summary → σ → Except Error σ) {first second : Nat}
      {left right : List (Step σ)} (paired : relation first second)
      (later : StepsCorrespond relation left right) :
      StepsCorrespond relation (.child first update :: left) (.child second update :: right)

/-- Equation correspondence retains the accumulator, initialization, finish,
ordered checks and child updates. Equal byte extents alone are insufficient. -/
inductive Equation.Corresponds (relation : Nat → Nat → Prop) : Equation → Equation → Prop where
  | mk (kind : Accumulator) (initial : Except Error kind.State)
      (finish : kind.State → Except Error Summary) {left right : List (Step kind.State)}
      (steps : StepsCorrespond relation left right) :
      Corresponds relation { kind, initial, steps := left, finish }
        { kind, initial, steps := right, finish }

def Graph.Correspondence (left right : Graph) (relation : Nat → Nat → Prop) : Prop :=
  ∀ first second, relation first second →
    ∃ leftEquation rightEquation, left.nodes.find first = some leftEquation ∧
      right.nodes.find second = some rightEquation ∧
      leftEquation.Corresponds relation rightEquation

/-- Ordered source/child rows are retained, including duplicates. -/
inductive RowsCorrespond {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : RowsCorrespond relation [] []
  | cons {first : α} {second : β} {left : List α} {right : List β}
      (paired : relation first second) (later : RowsCorrespond relation left right) :
      RowsCorrespond relation (first :: left) (second :: right)

theorem RowsCorrespond.same_length {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (paired : RowsCorrespond relation left right) : left.length = right.length := by
  induction paired with
  | nil => rfl
  | cons pair later ih => exact congrArg Nat.succ ih

theorem RowsCorrespond.mono {α β : Type} {relation other : α → β → Prop} {left : List α} {right : List β}
    (paired : RowsCorrespond relation left right) (included : ∀ a b, relation a b → other a b) :
    RowsCorrespond other left right := by
  induction paired with
  | nil => exact .nil
  | cons pair later ih => exact .cons (included _ _ pair) ih

theorem RowsCorrespond.map {α β γ δ : Type} {relation : α → β → Prop} {other : γ → δ → Prop}
    {left : List α} {right : List β} (paired : RowsCorrespond relation left right)
    (first : α → γ) (second : β → δ) (respects : ∀ a b, relation a b → other (first a) (second b)) :
    RowsCorrespond other (left.map first) (right.map second) := by
  induction paired with
  | nil => exact .nil
  | cons pair later ih => exact .cons (respects _ _ pair) ih

theorem RowsCorrespond.zip_left_same {α β γ : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : RowsCorrespond relation left right) (values : List γ) :
    RowsCorrespond (fun a b => a.1 = b.1 ∧ relation a.2 b.2) (values.zip left) (values.zip right) := by
  induction paired generalizing values with
  | nil => cases values <;> exact .nil
  | cons pair later ih =>
    cases values with
    | nil => exact .nil
    | cons value rest => exact .cons ⟨rfl,pair⟩ (ih rest)

theorem RowsCorrespond.zip_right_same {α β γ : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : RowsCorrespond relation left right) (values : List γ) :
    RowsCorrespond (fun a b => relation a.1 b.1 ∧ a.2 = b.2) (left.zip values) (right.zip values) := by
  induction paired generalizing values with
  | nil => exact .nil
  | cons pair later ih =>
    cases values with
    | nil => exact .nil
    | cons value rest => exact .cons ⟨pair,rfl⟩ (ih rest)

theorem StepsCorrespond.append {relation : Nat → Nat → Prop} {σ : Type}
    {left right tail otherTail : List (Step σ)} (paired : StepsCorrespond relation left right)
    (later : StepsCorrespond relation tail otherTail) :
    StepsCorrespond relation (left ++ tail) (right ++ otherTail) := by
  induction paired with
  | nil => exact later
  | check update steps ih => exact .check update ih
  | child update pair steps ih => exact .child update pair ih

theorem StepsCorrespond.mono {first second : Nat → Nat → Prop} {σ : Type}
    {left right : List (Step σ)} (paired : StepsCorrespond first left right)
    (included : ∀ a b, first a b → second a b) : StepsCorrespond second left right := by
  induction paired with
  | nil => exact .nil
  | check update later ih => exact .check update ih
  | child update paired later ih => exact .child update (included _ _ paired) ih

theorem Equation.Corresponds.mono {first second : Nat → Nat → Prop} {left right : Equation}
    (paired : left.Corresponds first right) (included : ∀ a b, first a b → second a b) :
    left.Corresponds second right := by
  cases paired with
  | mk kind initial finish steps => exact .mk kind initial finish (steps.mono included)

theorem StepsCorrespond.self_on {relation : Nat → Nat → Prop} {region : Nat → Prop}
    {σ : Type} {steps : List (Step σ)} (inside : StepsIn region steps)
    (diagonal : ∀ node, region node → relation node node) : StepsCorrespond relation steps steps := by
  induction steps with
  | nil => exact .nil
  | cons step rest ih =>
    cases step with
    | check update => exact .check update (ih inside)
    | child node update => exact .child update (diagonal node inside.1) (ih inside.2)

theorem Equation.Corresponds.self_on {relation : Nat → Nat → Prop} {region : Nat → Prop}
    (equation : Equation) (inside : StepsIn region equation.steps)
    (diagonal : ∀ node, region node → relation node node) : equation.Corresponds relation equation := by
  cases equation with
  | mk kind initial steps finish => exact .mk kind initial finish (StepsCorrespond.self_on inside diagonal)

theorem Graph.Correspondence.grow {left right leftNext rightNext : Graph} {relation : Nat → Nat → Prop}
    (paired : left.Correspondence right relation) (leftGrowth : left.Extends leftNext)
    (rightGrowth : right.Extends rightNext) : leftNext.Correspondence rightNext relation := by
  intro first second related
  obtain ⟨leftEquation,rightEquation,leftFound,rightFound,equations⟩ := paired first second related
  exact ⟨leftEquation,rightEquation,leftGrowth _ _ leftFound,rightGrowth _ _ rightFound,equations⟩

/-- Related roots may be added without asserting global equality, injectivity
or disjoint numeric allocation ranges. Existing node pairs remain related. -/
theorem Graph.Correspondence.adjoin {left right : Graph} {relation : Nat → Nat → Prop}
    (paired : left.Correspondence right relation) {first second : Nat} {leftEquation rightEquation : Equation}
    (leftFound : left.nodes.find first = some leftEquation) (rightFound : right.nodes.find second = some rightEquation)
    (equations : leftEquation.Corresponds (fun a b => relation a b ∨ a = first ∧ b = second) rightEquation) :
    left.Correspondence right (fun a b => relation a b ∨ a = first ∧ b = second) := by
  intro a b related
  rcases related with original | ⟨rfl,rfl⟩
  · obtain ⟨l,r,lf,rf,eqs⟩ := paired a b original
    exact ⟨l,r,lf,rf,eqs.mono (fun _ _ member => Or.inl member)⟩
  · exact ⟨leftEquation,rightEquation,leftFound,rightFound,equations⟩

/-- Independent allocations may use different frontiers, or coincident numeric
IDs. The new roots are paired without changing any old equation pair. -/
theorem Graph.Correspondence.allocate_pair {left right : Graph} {relation : Nat → Nat → Prop}
    (paired : left.Correspondence right relation) (leftBounded : left.Bounded) (rightBounded : right.Bounded)
    {leftEquation rightEquation : Equation} (equations : leftEquation.Corresponds relation rightEquation) :
    ({ left with nodes := left.nodes.insert left.count leftEquation, count := left.count + 1 } : Graph).Correspondence
      { right with nodes := right.nodes.insert right.count rightEquation, count := right.count + 1 }
      (fun a b => relation a b ∨ a = left.count ∧ b = right.count) := by
  apply (paired.grow (Graph.Extends.allocate leftBounded leftEquation)
    (Graph.Extends.allocate rightBounded rightEquation)).adjoin
    (leftEquation := leftEquation) (rightEquation := rightEquation)
  · simp [NatIndexTree.find_insert]
  · simp [NatIndexTree.find_insert]
  · exact equations.mono (fun _ _ member => Or.inl member)

/-- A common closed original component supplies the diagonal part of a
correspondence even when fresh equations disagree outside it. -/
theorem Graph.Correspondence.closed_region {base left right : Graph} {region : Nat → Prop}
    (closed : base.ClosedRegion region) (leftGrowth : base.Extends left) (rightGrowth : base.Extends right) :
    left.Correspondence right (fun a b => a = b ∧ region a) := by
  intro a b paired
  rcases paired with ⟨rfl,inside⟩
  obtain ⟨equation,found,dependencies⟩ := closed a inside
  exact ⟨equation,equation,leftGrowth _ _ found,rightGrowth _ _ found,
    Equation.Corresponds.self_on equation dependencies (fun _ member => ⟨rfl,member⟩)⟩

theorem Equation.Corresponds.scaled {relation : Nat → Nat → Prop} (mode : Mode) (count : Nat)
    {first second : Nat} (paired : relation first second) :
    (scaled mode count first).Corresponds relation (scaled mode count second) :=
  .mk .summary _ _ (.child _ paired .nil)

theorem Equation.Corresponds.alias {relation : Nat → Nat → Prop} {first second : Nat}
    (paired : relation first second) : (Equation.alias first).Corresponds relation (Equation.alias second) :=
  .mk .summary _ _ (.child _ paired .nil)

theorem Equation.Corresponds.done (relation : Nat → Nat → Prop) (result : Result Summary) :
    (Equation.done result).Corresponds relation (Equation.done result) := .mk .summary _ _ .nil

theorem Equation.Corresponds.canonicalFields {relation : Nat → Nat → Prop}
    (mode : Mode) (kind : String) (id : Nat) {left right : List (Ty × Nat)}
    (paired : RowsCorrespond (fun a b => a.1 = b.1 ∧ relation a.2 b.2) left right) :
    (SourceLayout.canonicalFields mode kind id left).Corresponds relation (SourceLayout.canonicalFields mode kind id right) := by
  apply Equation.Corresponds.mk .placements _ _
  induction paired with
  | nil => exact .nil
  | @cons first second left right pair later ih =>
    rcases first with ⟨ty,node⟩
    rcases second with ⟨otherTy,otherNode⟩
    rcases pair with ⟨same,related⟩
    cases same
    exact .child _ related ih

theorem Equation.Corresponds.declaredFields {relation : Nat → Nat → Prop}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    {left right : List (Ty × Option Nat × Nat)}
    (paired : RowsCorrespond (fun a b => a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ relation a.2.2 b.2.2) left right) :
    (SourceLayout.declaredFields mode kind id size align clamp transparent left).Corresponds relation
      (SourceLayout.declaredFields mode kind id size align clamp transparent right) := by
  apply Equation.Corresponds.mk .placements _ _
  induction paired with
  | nil => exact .nil
  | @cons first second left right pair later ih =>
    rcases first with ⟨ty,offset,node⟩
    rcases second with ⟨otherTy,otherOffset,otherNode⟩
    rcases pair with ⟨sameTy,sameOffset,related⟩
    cases sameTy
    cases sameOffset
    exact .child _ related ih

theorem Equation.Corresponds.canonicalZip {relation : Nat → Nat → Prop}
    (mode : Mode) (kind : String) (id : Nat) (types : List Ty) {left right : List Nat}
    (paired : RowsCorrespond relation left right) :
    (SourceLayout.canonicalFields mode kind id (types.zip left)).Corresponds relation
      (SourceLayout.canonicalFields mode kind id (types.zip right)) :=
  Equation.Corresponds.canonicalFields mode kind id (paired.zip_left_same types)

theorem Equation.Corresponds.declaredMapZip {relation : Nat → Nat → Prop}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (types : List Ty) (offsets : List Nat) {left right : List Nat} (paired : RowsCorrespond relation left right) :
    (SourceLayout.declaredFields mode kind id size align clamp transparent
      ((types.zip left).zip offsets |>.map (fun ((ty,node),offset) => (ty,some offset,node)))).Corresponds relation
    (SourceLayout.declaredFields mode kind id size align clamp transparent
      ((types.zip right).zip offsets |>.map (fun ((ty,node),offset) => (ty,some offset,node)))) := by
  apply Equation.Corresponds.declaredFields
  apply ((paired.zip_left_same types).zip_right_same offsets).map
  intro a b related
  rcases a with ⟨⟨ty,node⟩,offset⟩
  rcases b with ⟨⟨otherTy,otherNode⟩,otherOffset⟩
  rcases related with ⟨⟨sameTy,related⟩,sameOffset⟩
  exact ⟨sameTy,congrArg some sameOffset,related⟩

/-- Validator prefixes, deferred initialization checks and lifted child
updates all retain their original order through tuple sequencing. -/
theorem Equation.Corresponds.sequence {relation : Nat → Nat → Prop}
    {left right : List Nat} (children : RowsCorrespond relation left right) {first second : Equation}
    (equations : first.Corresponds relation second) :
    (Equation.sequence left first).Corresponds relation (Equation.sequence right second) := by
  cases equations with
  | mk kind initial finish steps =>
    apply Equation.Corresponds.mk (.deferred kind) _ _
    apply StepsCorrespond.append
    · apply StepsCorrespond.append
      · induction children with
        | nil => exact .nil
        | cons pair later ih => exact .child _ pair ih
      · exact .check _ .nil
    · induction steps with
      | nil => exact .nil
      | check update later ih => exact .check _ ih
      | child update pair later ih => exact .child _ pair ih

theorem Graph.Correspondence.scaled_roots {base left right : Graph} {region : Nat → Prop}
    (closed : base.ClosedRegion region) (leftGrowth : base.Extends left) (rightGrowth : base.Extends right)
    (mode : Mode) (count : Nat) {child first second : Nat} (inside : region child)
    (leftFound : left.nodes.find first = some (scaled mode count child))
    (rightFound : right.nodes.find second = some (scaled mode count child)) :
    left.Correspondence right (fun a b => (a = b ∧ region a) ∨ a = first ∧ b = second) :=
  (Graph.Correspondence.closed_region closed leftGrowth rightGrowth).adjoin leftFound rightFound
    (Equation.Corresponds.scaled mode count (Or.inl ⟨rfl,inside⟩))

end TrustIr.SourceLayout
