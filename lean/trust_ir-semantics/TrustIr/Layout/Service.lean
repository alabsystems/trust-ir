-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Extension
import TrustIr.Layout.References
import TrustIr.Layout.Correspondence
import TrustIr.Layout.Bounds
import TrustIr.Layout.Geometry
import TrustIr.Layout.EnumGeometry
import TrustIr.Layout.Storage
import TrustIr.Layout.Alignment
import TrustIr.Layout.FieldAlignment
import TrustIr.Layout.EncodingGeometry
import TrustIr.Layout.Metadata
import TrustIr.Layout.EnumOrigin
import TrustIr.Layout.StructOrigin
import TrustIr.Layout.Scalar
import TrustIr.Layout.Enums
import TrustIr.Layout.Inhabit
import TrustIr.Semantics.ClosureTypes

namespace TrustIr.SourceLayout

private abbrev Build := StateM Graph

private def add (equation : Equation) : Build Nat := do
  let graph ← get
  let node := graph.count
  set ({ graph with nodes := graph.nodes.insert node equation, count := node + 1 } : Graph)
  pure node

private def put (node : Nat) (equation : Equation) : Build Unit :=
  modify fun graph => { graph with nodes := graph.nodes.insert node equation }

private def failed (error : Error) : Build Nat := add (.done (.error error))

/-- Scalar sharing concerns only byte summaries. Declared field types, Func
    identities and value codecs remain separate and are never equated here. -/
private def addScalar (result : Result Summary) : Build Nat := do
  match result with
  | .error error => failed error
  | .ok value =>
    let key := 64 * value.size + (value.align.map Nat.succ).getD 0
    let graph ← get
    match graph.leaves.find key with
    | some node => pure node
    | none =>
      let node ← add (.done (.ok value))
      modify fun graph => { graph with leaves := graph.leaves.insert key node }
      pure node
private theorem add_preserves (equation : Equation) : PreservesGraph (add equation) := by
  intro graph bounded
  exact ⟨Nat.le_succ _, bounded.allocate equation, Graph.Extends.allocate bounded equation⟩

private theorem failed_preserves (error : Error) : PreservesGraph (failed error) :=
  add_preserves (.done (.error error))

private theorem addScalar_preserves (result : Result Summary) : PreservesGraph (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_preserves error
  | ok value =>
    apply PreservesGraph.bind PreservesGraph.get
    intro graph
    split
    · exact PreservesGraph.pure _
    · apply PreservesGraph.bind (add_preserves _)
      intro node
      apply PreservesGraph.bind (PreservesGraph.leaves (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesGraph.pure _

private theorem add_word (equation : Equation) (safe : equation.InvariantRule (WordBounds 1)) :
    PreservesState Graph.WordInvariant (add equation) := by
  intro graph valid
  exact valid.insert graph.count equation safe

private theorem put_word (node : Nat) (equation : Equation)
    (safe : equation.InvariantRule (WordBounds 1)) :
    PreservesState Graph.WordInvariant (put node equation) := by
  intro graph valid
  exact valid.insert node equation safe

private theorem failed_word (error : Error) :
    PreservesState Graph.WordInvariant (failed error) :=
  add_word _ (Equation.WordGuarded.failed error).rule

private theorem leaves_word (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState Graph.WordInvariant
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun _ valid => valid

private theorem addScalar_word (result : Result Summary)
    (safe : ∀ value, result = .ok value → WordBounds 1 value) :
    PreservesState Graph.WordInvariant (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_word error
  | ok value =>
    apply PreservesState.bind (PreservesState.get Graph.WordInvariant)
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_word _ (Equation.WordGuarded.done _ safe).rule)
      intro node
      apply PreservesState.bind (leaves_word (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _

private def globalTuples (index : Index) : Nat := 2 * index.count
private def globalClosures (index : Index) : Nat := globalTuples index + 1

/-- Source descriptor lookup resolves every row, keeps alias ambiguity and
    malformed-row priority, and compares the full actual tuple identity. -/
def tupleDescriptor (source : Environment) (ty : Ty) : Result (Option TupleLayoutDescriptor) :=
  (TupleIndex.ofRows source.types.toArray source.tupleLayouts).lookup ty

def closureDescriptor (source : Environment) (id : ClosureTyId) : Result (Option ClosureLayoutDescriptor) :=
  (ClosureIndex.ofRows source.closures.toArray source.closureLayouts).lookup id

private def scalar (mode : Mode) (source : Environment) (ty : Ty) : Option (Result Summary) :=
  let plain (size : Nat) := some (finish mode { size, align := some size })
  let pointer := plain source.model.pointerBytes
  let scalarTarget (result : Option (Result Summary)) :=
    if mode == .shape && !source.canonicalScalars then some (.error .scalarTarget) else result
  match ty with
  | .Bool | .I8 | .U8 => scalarTarget (plain 1)
  | .I16 | .U16 | .F16 => scalarTarget (plain 2)
  | .I32 | .U32 | .F32 | .Char => scalarTarget (plain 4)
  | .I64 | .U64 | .F64 => scalarTarget (plain 8)
  | .I128 | .U128 => scalarTarget (plain 16)
  | .Isize | .Usize | .Ptr | .PtrConst _ | .PtrMut _ | .Ref _ | .RefMut _ | .Rc _ | .Func _ =>
    scalarTarget pointer
  | .FatPtr _ =>
    if !source.canonicalScalars then some (.error .scalarTarget)
    else some (finish mode { size := 2 * source.model.pointerBytes, align := some source.model.pointerBytes })
  | .Unit => some (.ok { size := 0, align := some 1 })
  | .Never =>
    if mode == .shape then some (.ok { size := 0, align := none })
    else some (.error (.unsupported ty))
  | .Handle _ _ => if mode == .shape then pointer else some (.error (.unsupported ty))
  | .Error | .Dialect _ _ _ | .Set _ _ | .Sequence _ | .Record _ => some (.error (.unsupported ty))
  | _ => none

private theorem scalar_word (mode : Mode) (source : Environment) (ty : Ty)
    (result : Result Summary) (value : Summary)
    (found : scalar mode source ty = some result) (success : result = .ok value) :
    WordBounds 1 value := by
  cases ty
  all_goals dsimp only [scalar] at found
  all_goals repeat first
    | exact finish_word_bounds mode _ value ((Option.some.inj found).trans success)
    | (have same := Except.ok.inj ((Option.some.inj found).trans success)
       cases same
       exact WordBounds.unit)
    | (have same := Except.ok.inj ((Option.some.inj found).trans success)
       cases same
       exact WordBounds.never)
    | (have impossible := (Option.some.inj found).trans success; cases impossible)
    | cases found
    | split at found

private theorem scalar_admissible (mode : Mode) (source : Environment) (ty : Ty)
    (result : Result Summary) (value : Summary)
    (found : scalar mode source ty = some result) (success : result = .ok value) :
    ScalarSummary source.model.pointerBytes value := by
  cases ty
  all_goals dsimp only [scalar] at found
  all_goals repeat first
    | (apply ScalarSummary.of_finish (success := (Option.some.inj found).trans success)
       first | exact .plain _ (by simp) | exact .fat)
    | (have same := Except.ok.inj ((Option.some.inj found).trans success)
       cases same
       first | exact .unit | exact .never)
    | (have impossible := (Option.some.inj found).trans success; cases impossible)
    | cases found
    | split at found

private theorem scalar_finish_bounds (mode : Mode) (source : Environment) (ty : Ty)
    (result : Result Summary) (value : Summary)
    (found : scalar mode source ty = some result) (success : result = .ok value) :
    FinishBounds mode value := by
  cases ty
  all_goals dsimp only [scalar] at found
  all_goals repeat first
    | (have guarded := (finish_ok_iff mode _ value).mp ((Option.some.inj found).trans success)
       exact guarded.1 ▸ guarded.2)
    | (have same := Except.ok.inj ((Option.some.inj found).trans success)
       cases same
       first | exact FinishBounds.unit mode | exact FinishBounds.never mode)
    | (have impossible := (Option.some.inj found).trans success; cases impossible)
    | cases found
    | split at found


/-- Actual interning preserves exact scalar metadata on both cache hits and
fresh allocations. No cache hit is justified merely by a byte-size bound. -/
private theorem addScalar_exact (lower pointerBytes : Nat) (graph : Graph)
    (bounded : graph.Bounded) (frontier : lower ≤ graph.count)
    (valid : graph.ScalarInvariant lower pointerBytes) (value : Summary)
    (scalarValue : ScalarSummary pointerBytes value) (node : Nat) (after : Graph)
    (run : addScalar (.ok value) graph = (node, after)) :
    after.ScalarInvariant lower pointerBytes ∧ lower ≤ node ∧
      after.nodes.find node = some (Equation.done (.ok value)) := by
  let allocated : Graph :=
    { graph with nodes := graph.nodes.insert graph.count (Equation.done (.ok value)), count := graph.count + 1 }
  let completed : Graph := { allocated with leaves := graph.leaves.insert (scalarKey value) graph.count }
  cases cached : graph.leaves.find (scalarKey value) with
  | some cachedNode =>
    simp only [scalarKey] at cached
    have same : (cachedNode, graph) = (node, after) := by
      simpa only [addScalar, add, cached, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
        StateT.get, StateT.set, StateT.modifyGet, get, getThe, set, modify, modifyGet,
        MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet] using run
    cases same
    exact ⟨valid, valid.lookup scalarValue cached⟩
  | none =>
    simp only [scalarKey] at cached
    have same : (graph.count, completed) = (node, after) := by
      simpa only [addScalar, add, cached, completed, allocated, scalarKey, Bind.bind, StateT.bind,
        Pure.pure, StateT.pure, StateT.get, StateT.set, StateT.modifyGet, get, getThe, set, modify,
        modifyGet, MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet] using run
    rcases Prod.mk.inj same with ⟨nodeSame, graphSame⟩
    subst node
    subst after
    have preserved : allocated.ScalarInvariant lower pointerBytes :=
      valid.weaken (Graph.Extends.allocate bounded _) rfl
    have installed : allocated.nodes.find graph.count = some (Equation.done (.ok value)) := by
      change (graph.nodes.insert graph.count (Equation.done (.ok value))).find graph.count = _
      rw [NatIndexTree.find_insert, if_pos rfl]
    exact ⟨preserved.cache graph.count frontier value scalarValue installed, frontier, installed⟩


private def ScalarState (lower pointerBytes : Nat) (graph : Graph) : Prop :=
  graph.Bounded ∧ lower ≤ graph.count ∧ graph.ScalarInvariant lower pointerBytes

private theorem add_scalar_state (lower pointerBytes : Nat) (equation : Equation) :
    PreservesState (ScalarState lower pointerBytes) (add equation) := by
  intro graph state
  exact ⟨state.1.allocate equation, Nat.le_trans state.2.1 (Nat.le_succ _),
    state.2.2.weaken (Graph.Extends.allocate state.1 equation) rfl⟩

private theorem put_scalar_state (lower pointerBytes node : Nat) (reserved : node < lower)
    (equation : Equation) : PreservesState (ScalarState lower pointerBytes) (put node equation) := by
  intro graph state
  exact ⟨state.1.put node (Nat.lt_of_lt_of_le reserved state.2.1) equation,
    state.2.1, state.2.2.put node reserved equation⟩

private theorem addScalar_scalar_state (lower pointerBytes : Nat) (result : Result Summary)
    (safe : ∀ value, result = .ok value → ScalarSummary pointerBytes value) :
    PreservesState (ScalarState lower pointerBytes) (addScalar result) := by
  cases result with
  | error error => exact add_scalar_state lower pointerBytes _
  | ok value =>
    intro graph state
    have growth := addScalar_preserves (.ok value) graph state.1
    have exactValue := addScalar_exact lower pointerBytes graph state.1 state.2.1 state.2.2
      value (safe value rfl) _ _ rfl
    exact ⟨growth.bounded, Nat.le_trans state.2.1 growth.count_mono, exactValue.1⟩


mutual
  /-- Inline syntax is compiled structurally. Nominal references point to
      reserved original source positions; they never recursively expand here. -/
  private def compileTy (index : Index) (mode : Mode) (ty : Ty) : Build Nat := do
    let source := index.source
    if mode == .execution && !source.canonicalScalars then return ← failed .scalarTarget
    match scalar mode source ty with
    | some result => addScalar result
    | none =>
      match ty with
      | .Struct id =>
        match (if mode == .shape then index.structShapePositions else index.structPositions).find id.index with
        | some position => pure (index.node mode (index.structBase + position))
        | none => failed (.missingStruct id.index)
      | .Enum id =>
        match (if mode == .shape then index.enumShapePositions else index.enumPositions).find id.index with
        | some position => pure (index.node mode (index.enumBase + position))
        | none => failed (.missingEnum id.index)
      | .Array element count =>
        if !((trustIrArrayGet? index.typeRows element.index)).isSome then failed (.missingType element.index)
        else if count > word64Max then failed .sizeOverflow
        else add (scaled mode count (index.node mode element.index))
      | .Vector count element =>
        if mode == .execution && count == 0 then failed (.unsupported ty)
        else if count ≥ 2 ^ 32 then failed .sizeOverflow
        else add (scaled mode count (← compileTy index mode element))
      | .Refine base _ =>
        if mode == .execution then failed (.unsupported ty)
        else if !((trustIrArrayGet? index.typeRows base.index)).isSome then failed (.missingType base.index)
        else pure (index.node .shape base.index)
      | .Closure id =>
        if mode == .execution then failed (.unsupported ty)
        else if !((trustIrArrayGet? index.closureRows id.index)).isSome then failed (.missingClosure id.index)
        else pure (index.node .shape (index.closureBase + id.index))
      | .Tuple fields =>
        match index.tupleDeclarations.lookup ty with
        | .error error => failed error
        | .ok descriptor =>
          let equation ← match descriptor with
            | none => do
              if mode == .shape && !fields.isEmpty then pure (.done (.error (.unsupported ty)))
              else
                let children ← compileTypes index mode fields
                pure (canonicalFields mode "tuple" 0 (fields.zip children))
            | some descriptor => do
              if !source.hasTargetInfo then pure (.done (.error (.missingTarget "tuple")))
              else if descriptor.fieldOffsets.length != fields.length then
                pure (.done (.error (.incoherent "tuple" descriptor.tupleType.index)))
              else
                -- A declared tuple is validated by source shape, including
                -- actual Closure and Refine dependencies. Its descriptor may
                -- answer size/align without admitting a byte codec for a leaf.
                let children ← compileTypes index .shape fields
                pure (declaredFields mode "tuple" descriptor.tupleType.index descriptor.size descriptor.align
                  word64Max false ((fields.zip children).zip descriptor.fieldOffsets |>.map
                    (fun ((field, child), offset) => (field, some offset, child))))
          add (if mode == .execution then sequence [globalTuples index] equation else equation)
      | _ => failed (.unsupported ty)
  private def compileTypes (index : Index) (mode : Mode) : List Ty → Build (List Nat)
    | [] => pure []
    | first :: rest => do
      let child ← compileTy index mode first
      let later ← compileTypes index mode rest
      pure (child :: later)
end

mutual
  private theorem compileTy_preserves (index : Index) (mode : Mode) (ty : Ty) :
      PreservesGraph (compileTy index mode ty) := by
    cases hty : ty
    all_goals rw [compileTy.eq_def]
    all_goals dsimp only [scalar]
    all_goals simp only [pure_bind, bind_pure]
    case Vector count element =>
      repeat first
        | exact failed_preserves _
        | (apply PreservesGraph.bind (compileTy_preserves index mode element)
           intro child
           exact add_preserves _)
        | split
    case Tuple fields =>
      repeat first
        | exact failed_preserves _
        | exact add_preserves _
        | (apply PreservesGraph.bind (compileTypes_preserves index mode fields)
           intro children
           exact add_preserves _)
        | (apply PreservesGraph.bind (compileTypes_preserves index .shape fields)
           intro children
           exact add_preserves _)
        | split
    all_goals repeat first
      | exact addScalar_preserves _
      | exact add_preserves _
      | exact PreservesGraph.pure _
      | split
  termination_by sizeOf ty
  private theorem compileTypes_preserves (index : Index) (mode : Mode) (types : List Ty) :
      PreservesGraph (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases htypes : types with
    | nil => exact PreservesGraph.pure _
    | cons first rest =>
      apply PreservesGraph.bind (compileTy_preserves index mode first)
      intro child
      apply PreservesGraph.bind (compileTypes_preserves index mode rest)
      intro later
      exact PreservesGraph.pure _
  termination_by sizeOf types
end

/-- Query-time compilation cannot fill or change a pre-reserved slot. -/
private def KeepsPrefix {α : Type} (lower : Nat) (action : Build α) : Prop :=
  ∀ graph, graph.Bounded → lower ≤ graph.count → ∀ node, node < lower →
    (action graph).2.nodes.find node = graph.nodes.find node

private theorem KeepsPrefix.pure {α : Type} (lower : Nat) (value : α) :
    KeepsPrefix lower (pure value : Build α) := fun _ _ _ _ _ => rfl

private theorem KeepsPrefix.get (lower : Nat) : KeepsPrefix lower (get : Build Graph) := fun _ _ _ _ _ => rfl

private theorem KeepsPrefix.leaves (lower : Nat) (update : NatIndexTree Nat → NatIndexTree Nat) :
    KeepsPrefix lower (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun _ _ _ _ _ => rfl

private theorem KeepsPrefix.bind {α β : Type} {action : Build α} {next : α → Build β} (lower : Nat)
    (growth : PreservesGraph action) (first : KeepsPrefix lower action)
    (later : ∀ value, KeepsPrefix lower (next value)) : KeepsPrefix lower (action >>= next) := by
  intro graph bounded frontier node inside
  have extended := growth graph bounded
  exact (later (action graph).1 (action graph).2 extended.bounded
    (Nat.le_trans frontier extended.count_mono) node inside).trans (first graph bounded frontier node inside)

private theorem KeepsPrefix.add (lower : Nat) (equation : Equation) : KeepsPrefix lower (SourceLayout.add equation) := by
  intro graph bounded frontier node inside
  change (graph.nodes.insert graph.count equation).find node = graph.nodes.find node
  rw [NatIndexTree.find_insert,if_neg (by omega : node ≠ graph.count)]

private theorem KeepsPrefix.scalar (lower : Nat) (result : Result Summary) : KeepsPrefix lower (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact KeepsPrefix.add lower _
  | ok value =>
    apply KeepsPrefix.bind lower PreservesGraph.get (KeepsPrefix.get lower)
    intro graph
    split
    · exact fun _ _ _ _ _ => rfl
    · apply KeepsPrefix.bind lower (add_preserves _) (KeepsPrefix.add lower _)
      intro node
      apply KeepsPrefix.bind lower
        (PreservesGraph.leaves (fun leaves => leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
        (KeepsPrefix.leaves lower (fun leaves => leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact fun _ _ _ _ _ => rfl

set_option maxHeartbeats 1000000 in
mutual
  private theorem compileTy_keeps_prefix (lower : Nat) (index : Index) (mode : Mode) (ty : Ty) :
      KeepsPrefix lower (compileTy index mode ty) := by
    cases hty : ty
    all_goals rw [compileTy.eq_def]
    all_goals dsimp only [scalar]
    all_goals simp only [pure_bind,bind_pure]
    case Vector count element =>
      repeat first
        | exact KeepsPrefix.add lower _
        | (apply KeepsPrefix.bind lower (compileTy_preserves index mode element)
             (compileTy_keeps_prefix lower index mode element)
           intro child
           exact KeepsPrefix.add lower _)
        | split
    case Tuple fields =>
      repeat first
        | exact KeepsPrefix.add lower _
        | (apply KeepsPrefix.bind lower (compileTypes_preserves index mode fields)
             (compileTypes_keeps_prefix lower index mode fields)
           intro children
           exact KeepsPrefix.add lower _)
        | (apply KeepsPrefix.bind lower (compileTypes_preserves index .shape fields)
             (compileTypes_keeps_prefix lower index .shape fields)
           intro children
           exact KeepsPrefix.add lower _)
        | split
    all_goals repeat first
      | exact KeepsPrefix.scalar lower _
      | exact KeepsPrefix.add lower _
      | exact fun _ _ _ _ _ => rfl
      | split
    termination_by sizeOf ty
  private theorem compileTypes_keeps_prefix (lower : Nat) (index : Index) (mode : Mode) (types : List Ty) :
      KeepsPrefix lower (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases htypes : types with
    | nil => exact fun _ _ _ _ _ => rfl
    | cons first rest =>
      apply KeepsPrefix.bind lower (compileTy_preserves index mode first) (compileTy_keeps_prefix lower index mode first)
      intro child
      apply KeepsPrefix.bind lower (compileTypes_preserves index mode rest) (compileTypes_keeps_prefix lower index mode rest)
      intro later
      exact fun _ _ _ _ _ => rfl
    termination_by sizeOf types
end

private theorem compileTuple_word (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState Graph.WordInvariant (compileTypes index mode fields))
    (shapeSafe : PreservesState Graph.WordInvariant (compileTypes index .shape fields)) :
    PreservesState Graph.WordInvariant (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_word _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_word
       apply Equation.WordGuarded.rule
       repeat first
         | exact Equation.WordGuarded.failed _
         | exact Equation.WordGuarded.canonicalFields _ _ _ _
         | exact Equation.WordGuarded.declaredFields _ _ _ _ _ _ _ _
         | apply Equation.WordGuarded.sequence
         | split)
    | split

mutual
  private theorem compileTy_word (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState Graph.WordInvariant (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_word _
    · split
      · rename_i result found
        exact addScalar_word result (fun value success => scalar_word mode index.source ty result value found success)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact failed_word _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_word _
            | (apply PreservesState.bind (compileTy_word index mode element)
               intro child
               exact add_word _ (Equation.WordGuarded.scaled mode count child).rule)
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_word index mode fields
            (compileTypes_word index mode fields) (compileTypes_word index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_word _
          | exact add_word _ (Equation.WordGuarded.scaled _ _ _).rule
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_word (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState Graph.WordInvariant (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_word index mode first)
      intro child
      apply PreservesState.bind (compileTypes_word index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private theorem compileTuple_scalar_state (lower : Nat) (index : Index) (mode : Mode)
    (fields : List Ty)
    (modeSafe : PreservesState (ScalarState lower index.source.model.pointerBytes) (compileTypes index mode fields))
    (shapeSafe : PreservesState (ScalarState lower index.source.model.pointerBytes) (compileTypes index .shape fields)) :
    PreservesState (ScalarState lower index.source.model.pointerBytes) (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact add_scalar_state _ _ _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | split

mutual
  private theorem compileTy_scalar_state (lower : Nat) (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState (ScalarState lower index.source.model.pointerBytes) (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact add_scalar_state _ _ _
    · split
      · rename_i result found
        exact addScalar_scalar_state lower _ result (fun value success =>
          scalar_admissible mode index.source ty result value found success)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact add_scalar_state _ _ _
        case Vector count element scalarNone =>
          repeat first
            | exact add_scalar_state _ _ _
            | (apply PreservesState.bind (compileTy_scalar_state lower index mode element)
               intro child
               exact add_scalar_state _ _ _)
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_scalar_state lower index mode fields
            (compileTypes_scalar_state lower index mode fields) (compileTypes_scalar_state lower index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact add_scalar_state _ _ _
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_scalar_state (lower : Nat) (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState (ScalarState lower index.source.model.pointerBytes) (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_scalar_state lower index mode first)
      intro child
      apply PreservesState.bind (compileTypes_scalar_state lower index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def structEquation (index : Index) (mode : Mode) (definition : StructDef) : Build Equation := do
  let id := definition.id.index
  if mode == .shape && definition.size.isNone then
    return .done (.error (.missingMetadata "struct" id "size"))
  if mode == .shape && definition.align.isNone then
    return .done (.error (.missingMetadata "struct" id "align"))
  match definition.size, definition.align with
  | none, none =>
    if mode == .shape || definition.fields.any (fun field => field.offset.isSome) then
      pure (.done (.error (.incoherent "struct" id)))
    else
      let types := definition.fields.map (·.ty)
      pure (canonicalFields mode "struct" id (types.zip (← compileTypes index mode types)))
  | some size, some align =>
    if mode == .execution && !index.source.canonicalScalars then
      return .done (.error .scalarTarget)
    let clamp ← match definition.repr with
      | .packed clamp =>
        if powerOfTwo clamp && clamp < 2 ^ 32 then pure clamp else pure 0
      | _ => pure word64Max
    if clamp == 0 then pure (.done (.error (.incoherent "struct" id)))
    else
      let types := definition.fields.map (·.ty)
      let children ← compileTypes index mode types
      pure (declaredFields mode "struct" id size align clamp
        (match definition.repr with | .transparent => true | _ => false)
        (definition.fields.zip children |>.map (fun (field, child) => (field.ty, field.offset, child))))
  | _, _ => pure (.done (.error (.incoherent "struct" id)))

private def closureEquation (index : Index) (position : Nat) (definition : ClosureTy) : Build Equation := do
  match index.closureDeclarations.lookup ⟨position⟩ with
  | .error error => pure (.done (.error error))
  | .ok none => pure (.done (.error (.unsupported (.Closure ⟨position⟩))))
  | .ok (some descriptor) =>
    if !index.source.hasTargetInfo then pure (.done (.error (.missingTarget "closure")))
    else if descriptor.captureOffsets.length != definition.captures.length then
      pure (.done (.error (.incoherent "closure" position)))
    else
      let children ← compileTypes index .shape definition.captures
      pure (declaredFields .shape "closure" position descriptor.size descriptor.align word64Max false
        ((definition.captures.zip children).zip descriptor.captureOffsets |>.map
          (fun ((ty, child), offset) => (ty, some offset, child))))

private def enumNodes (index : Index) (mode : Mode) (descriptor : Bool) : List Ty → Build (List (Ty × Nat))
  | [] => pure []
  | ty :: rest => do
    let child ← match ty with
      | .Never =>
        if descriptor then add (.done (.ok { size := 0, align := some 1 })) else compileTy index mode ty
      | _ => compileTy index mode ty
    pure ((ty, child) :: (← enumNodes index mode descriptor rest))

/-- A construction postcondition for the actual returned equation. Child
compilation is unrestricted: aggregate final guards enforce these bounds. -/
private def BuildsModeEquation (mode : Mode) (action : Build Equation) : Prop :=
  ∀ graph, (action graph).1.ModeGuarded mode

private theorem BuildsModeEquation.pure (mode : Mode) (equation : Equation)
    (safe : equation.ModeGuarded mode) : BuildsModeEquation mode (pure equation) :=
  fun _ => safe

private theorem BuildsModeEquation.bind {α : Type} (mode : Mode) (action : Build α)
    {next : α → Build Equation} (later : ∀ value, BuildsModeEquation mode (next value)) :
    BuildsModeEquation mode (action >>= next) :=
  fun graph => later (action graph).1 (action graph).2

private theorem structEquation_mode (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsModeEquation mode (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsModeEquation.pure; exact Equation.ModeGuarded.failed _ _)
    | (apply BuildsModeEquation.pure; exact Equation.ModeGuarded.canonicalFields _ _ _ _)
    | (apply BuildsModeEquation.pure; exact Equation.ModeGuarded.declaredFields _ _ _ _ _ _ _ _)
    | (apply BuildsModeEquation.bind mode (compileTypes index mode _); intro children)
    | split

private theorem closureEquation_mode (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsModeEquation .shape (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsModeEquation.pure; exact Equation.ModeGuarded.failed _ _)
    | (apply BuildsModeEquation.pure; exact Equation.ModeGuarded.declaredFields _ _ _ _ _ _ _ _)
    | (apply BuildsModeEquation.bind .shape (compileTypes index .shape _); intro children)
    | split

/-- Actual placement and finalization establish storage geometry without
assuming valid child layouts or a caller-provided cache oracle. -/
private def BuildsFieldEquation (action : Build Equation) : Prop :=
  ∀ graph, (action graph).1.FieldGuarded

private theorem BuildsFieldEquation.pure (equation : Equation)
    (safe : equation.FieldGuarded) : BuildsFieldEquation (pure equation) :=
  fun _ => safe

private theorem BuildsFieldEquation.bind {α : Type} (action : Build α)
    {next : α → Build Equation} (later : ∀ value, BuildsFieldEquation (next value)) :
    BuildsFieldEquation (action >>= next) :=
  fun graph => later (action graph).1 (action graph).2

private theorem structEquation_fields (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsFieldEquation (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsFieldEquation.pure; exact Equation.FieldGuarded.failed _)
    | (apply BuildsFieldEquation.pure; exact Equation.FieldGuarded.canonicalFields _ _ _ _)
    | (apply BuildsFieldEquation.pure; exact Equation.FieldGuarded.declaredFields _ _ _ _ _ _ _ _)
    | (apply BuildsFieldEquation.bind (compileTypes index mode _); intro children)
    | split

private theorem closureEquation_fields (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsFieldEquation (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsFieldEquation.pure; exact Equation.FieldGuarded.failed _)
    | (apply BuildsFieldEquation.pure; exact Equation.FieldGuarded.declaredFields _ _ _ _ _ _ _ _)
    | (apply BuildsFieldEquation.bind (compileTypes index .shape _); intro children)
    | split

private def BuildsAlignmentEquation (mode : Mode) (kind : String) (action : Build Equation) : Prop :=
  ∀ graph, (action graph).1.AlignmentGuarded mode kind

private theorem BuildsAlignmentEquation.pure (mode : Mode) (kind : String) (equation : Equation)
    (safe : equation.AlignmentGuarded mode kind) : BuildsAlignmentEquation mode kind (pure equation) :=
  fun _ => safe

private theorem BuildsAlignmentEquation.bind {α : Type} (mode : Mode) (kind : String) (action : Build α)
    {next : α → Build Equation} (later : ∀ value, BuildsAlignmentEquation mode kind (next value)) :
    BuildsAlignmentEquation mode kind (action >>= next) :=
  fun graph => later (action graph).1 (action graph).2

private theorem structEquation_alignment (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsAlignmentEquation mode "struct" (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsAlignmentEquation.pure; exact Equation.AlignmentGuarded.failed _ _ _)
    | (apply BuildsAlignmentEquation.pure; exact Equation.AlignmentGuarded.canonicalFields _ _ _ _)
    | (apply BuildsAlignmentEquation.pure; exact Equation.AlignmentGuarded.declaredFields _ _ _ _ _ _ _ _)
    | (apply BuildsAlignmentEquation.bind mode "struct" (compileTypes index mode _); intro children)
    | split

private theorem closureEquation_alignment (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsAlignmentEquation .shape "closure" (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsAlignmentEquation.pure; exact Equation.AlignmentGuarded.failed _ _ _)
    | (apply BuildsAlignmentEquation.pure; exact Equation.AlignmentGuarded.declaredFields _ _ _ _ _ _ _ _)
    | (apply BuildsAlignmentEquation.bind .shape "closure" (compileTypes index .shape _); intro children)
    | split

/-- Exact production construction, including the returned graph. -/
def StructCompilation (index : Index) (mode : Mode) (definition : StructDef)
    (before : Graph) (equation : Equation) (after : Graph) : Prop :=
  structEquation index mode definition before = (equation, after)

def ClosureCompilation (index : Index) (position : Nat) (definition : ClosureTy)
    (before : Graph) (equation : Equation) (after : Graph) : Prop :=
  closureEquation index position definition before = (equation, after)

theorem StructCompilation.mode_guarded {index : Index} {mode : Mode} {definition : StructDef}
    {before after : Graph} {equation : Equation}
    (compiled : StructCompilation index mode definition before equation after) :
    equation.ModeGuarded mode := by
  have safe := structEquation_mode index mode definition before
  change structEquation index mode definition before = (equation, after) at compiled
  rw [compiled] at safe
  exact safe

theorem ClosureCompilation.mode_guarded {index : Index} {position : Nat} {definition : ClosureTy}
    {before after : Graph} {equation : Equation}
    (compiled : ClosureCompilation index position definition before equation after) :
    equation.ModeGuarded .shape := by
  have safe := closureEquation_mode index position definition before
  change closureEquation index position definition before = (equation, after) at compiled
  rw [compiled] at safe
  exact safe

theorem StructCompilation.derivation_bounds {index : Index} {mode : Mode} {definition : StructDef}
    {before after graph : Graph} {equation : Equation} {node : Nat} {value : Summary}
    (compiled : StructCompilation index mode definition before equation after)
    (found : graph.nodes.find node = some equation) (derived : NodeDerivation graph node value) :
    FinishBounds mode value := NodeDerivation.mode_guarded found compiled.mode_guarded derived

theorem ClosureCompilation.derivation_bounds {index : Index} {position : Nat} {definition : ClosureTy}
    {before after graph : Graph} {equation : Equation} {node : Nat} {value : Summary}
    (compiled : ClosureCompilation index position definition before equation after)
    (found : graph.nodes.find node = some equation) (derived : NodeDerivation graph node value) :
    FinishBounds .shape value := NodeDerivation.mode_guarded found compiled.mode_guarded derived

/-- A struct equation can be installed directly at its reserved mode row. -/
theorem StructCompilation.reserved_rule {index : Index} {mode : Mode} {definition : StructDef}
    {before after : Graph} {equation : Equation}
    (compiled : StructCompilation index mode definition before equation after)
    (position : Nat) (inside : position < index.count) :
    equation.IndexedRule (fun node value => FinishBounds (index.nodeMode node) value)
      (index.node mode position) :=
  compiled.mode_guarded.indexed index.nodeMode _ (index.nodeMode_node mode position inside)

theorem ClosureCompilation.reserved_rule {index : Index} {position : Nat} {definition : ClosureTy}
    {before after : Graph} {equation : Equation}
    (compiled : ClosureCompilation index position definition before equation after)
    (owner : Nat) (inside : owner < index.count) :
    equation.IndexedRule (fun node value => FinishBounds (index.nodeMode node) value)
      (index.node .shape owner) :=
  compiled.mode_guarded.indexed index.nodeMode _ (index.nodeMode_node .shape owner inside)

theorem StructCompilation.field_guarded {index : Index} {mode : Mode} {definition : StructDef}
    {before after : Graph} {equation : Equation}
    (compiled : StructCompilation index mode definition before equation after) : equation.FieldGuarded := by
  have safe := structEquation_fields index mode definition before
  change structEquation index mode definition before = (equation, after) at compiled
  rw [compiled] at safe
  exact safe

theorem ClosureCompilation.field_guarded {index : Index} {position : Nat} {definition : ClosureTy}
    {before after : Graph} {equation : Equation}
    (compiled : ClosureCompilation index position definition before equation after) : equation.FieldGuarded := by
  have safe := closureEquation_fields index position definition before
  change closureEquation index position definition before = (equation, after) at compiled
  rw [compiled] at safe
  exact safe

theorem StructCompilation.derivation_geometry {index : Index} {mode : Mode} {definition : StructDef}
    {before after graph : Graph} {equation : Equation} {node : Nat} {value : Summary}
    (compiled : StructCompilation index mode definition before equation after)
    (found : graph.nodes.find node = some equation) (derived : NodeDerivation graph node value) :
    FieldGeometry value := NodeDerivation.field_geometry found compiled.field_guarded derived

theorem ClosureCompilation.derivation_geometry {index : Index} {position : Nat} {definition : ClosureTy}
    {before after graph : Graph} {equation : Equation} {node : Nat} {value : Summary}
    (compiled : ClosureCompilation index position definition before equation after)
    (found : graph.nodes.find node = some equation) (derived : NodeDerivation graph node value) :
    FieldGeometry value := NodeDerivation.field_geometry found compiled.field_guarded derived

theorem StructCompilation.alignment_guarded {index : Index} {mode : Mode} {definition : StructDef}
    {before after : Graph} {equation : Equation}
    (compiled : StructCompilation index mode definition before equation after) :
    equation.AlignmentGuarded mode "struct" := by
  have safe := structEquation_alignment index mode definition before
  change structEquation index mode definition before = (equation, after) at compiled
  rw [compiled] at safe
  exact safe

theorem ClosureCompilation.alignment_guarded {index : Index} {position : Nat} {definition : ClosureTy}
    {before after : Graph} {equation : Equation}
    (compiled : ClosureCompilation index position definition before equation after) :
    equation.AlignmentGuarded .shape "closure" := by
  have safe := closureEquation_alignment index position definition before
  change closureEquation index position definition before = (equation, after) at compiled
  rw [compiled] at safe
  exact safe

theorem StructCompilation.derivation_alignment {index : Index} {mode : Mode} {definition : StructDef}
    {before after graph : Graph} {equation : Equation} {node : Nat} {value : Summary}
    (compiled : StructCompilation index mode definition before equation after)
    (found : graph.nodes.find node = some equation) (derived : NodeDerivation graph node value) :
    AlignmentGeometry (FieldAlignmentRequired mode "struct") value :=
  NodeDerivation.alignment_geometry mode "struct" found compiled.alignment_guarded derived

theorem ClosureCompilation.derivation_alignment {index : Index} {position : Nat} {definition : ClosureTy}
    {before after graph : Graph} {equation : Equation} {node : Nat} {value : Summary}
    (compiled : ClosureCompilation index position definition before equation after)
    (found : graph.nodes.find node = some equation) (derived : NodeDerivation graph node value) :
    AlignmentGeometry (fun _ => True) value :=
  (NodeDerivation.alignment_geometry .shape "closure" found compiled.alignment_guarded derived).weaken
    (fun _ _ => Or.inr (Or.inl rfl))

private theorem structEquation_preserves (index : Index) (mode : Mode) (definition : StructDef) :
    PreservesGraph (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesGraph.pure _
    | (apply PreservesGraph.bind (compileTypes_preserves _ _ _)
       intro children
       exact PreservesGraph.pure _)
    | split

private theorem closureEquation_preserves (index : Index) (position : Nat) (definition : ClosureTy) :
    PreservesGraph (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesGraph.pure _
    | (apply PreservesGraph.bind (compileTypes_preserves _ _ _)
       intro children
       exact PreservesGraph.pure _)
    | split

private theorem enumNodes_preserves (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesGraph (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesGraph.pure _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesGraph.bind (compileTy_preserves _ _ _)
         intro child
         apply PreservesGraph.bind ih
         intro later
         exact PreservesGraph.pure _)
      | (apply PreservesGraph.bind (add_preserves _)
         intro child
         apply PreservesGraph.bind ih
         intro later
         exact PreservesGraph.pure _)
      | split

private theorem structEquation_scalar_state (lower : Nat) (index : Index) (mode : Mode) (definition : StructDef) :
    PreservesState (ScalarState lower index.source.model.pointerBytes) (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (compileTypes_scalar_state lower _ _ _)
       intro children
       exact PreservesState.pure _ _)
    | split

private theorem closureEquation_scalar_state (lower : Nat) (index : Index) (position : Nat) (definition : ClosureTy) :
    PreservesState (ScalarState lower index.source.model.pointerBytes) (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (compileTypes_scalar_state lower _ _ _)
       intro children
       exact PreservesState.pure _ _)
    | split

private theorem enumNodes_scalar_state (lower : Nat) (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState (ScalarState lower index.source.model.pointerBytes) (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_scalar_state lower _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_scalar_state lower _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private def BuildsEquation (action : Build Equation) : Prop :=
  ∀ graph, graph.WordInvariant →
    (action graph).2.WordInvariant ∧ (action graph).1.InvariantRule (WordBounds 1)

private theorem BuildsEquation.pure (equation : Equation)
    (safe : equation.InvariantRule (WordBounds 1)) :
    BuildsEquation (pure equation) := fun _ valid => ⟨valid, safe⟩

private theorem BuildsEquation.bind {α : Type} {action : Build α} {next : α → Build Equation}
    (first : PreservesState Graph.WordInvariant action)
    (later : ∀ value, BuildsEquation (next value)) : BuildsEquation (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (first graph valid)

private theorem BuildsEquation.install_yield {α : Type} {action : Build Equation}
    (node : Nat) (result : α) (safe : BuildsEquation action) :
    PreservesState Graph.WordInvariant (do put node (← action); Pure.pure result) := by
  intro graph valid
  have built := safe graph valid
  exact put_word node (action graph).1 built.2 (action graph).2 built.1

private theorem copyRoot_word (child : Nat) : BuildsEquation (do
    let graph ← get
    pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  refine ⟨valid, ?_⟩
  change ((graph.nodes.find child).getD (alias child)).InvariantRule (WordBounds 1)
  cases found : graph.nodes.find child with
  | none => exact .alias child
  | some equation => exact valid child equation found

private theorem structEquation_word (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsEquation (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsEquation.pure; exact (Equation.WordGuarded.failed _).rule)
    | (apply BuildsEquation.pure; exact (Equation.WordGuarded.canonicalFields _ _ _ _).rule)
    | (apply BuildsEquation.pure; exact (Equation.WordGuarded.declaredFields _ _ _ _ _ _ _ _).rule)
    | (apply BuildsEquation.bind (compileTypes_word _ _ _); intro children)
    | split

private theorem closureEquation_word (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsEquation (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsEquation.pure; exact (Equation.WordGuarded.failed _).rule)
    | (apply BuildsEquation.pure; exact (Equation.WordGuarded.declaredFields _ _ _ _ _ _ _ _).rule)
    | (apply BuildsEquation.bind (compileTypes_word _ _ _); intro children)
    | split

private theorem enumNodes_word (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState Graph.WordInvariant (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_word _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_word _ (Equation.WordGuarded.done _
           (by intro value same; cases same; exact WordBounds.unit)).rule)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private theorem variantEquation_word (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).WordGuarded := by
  repeat first
    | exact Equation.WordGuarded.failed _
    | exact Equation.WordGuarded.canonicalFields _ _ _ _
    | exact Equation.WordGuarded.declaredFields _ _ _ _ _ _ _ _
    | split

private theorem enumRoot_word (index : Index) (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
      Equation.done (.error Error.scalarTarget)
    else enumEquation mode definition uninhabited variants).WordGuarded := by
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact Equation.WordGuarded.failed _
  · exact Equation.WordGuarded.enumeration _ _ _ _

private theorem variantEquation_mode (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).ModeGuarded mode := by
  repeat first
    | exact Equation.ModeGuarded.failed mode _
    | exact Equation.ModeGuarded.canonicalFields _ _ _ _
    | exact Equation.ModeGuarded.declaredFields _ _ _ _ _ _ _ _
    | split

private theorem enumRoot_mode (index : Index) (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
      Equation.done (.error Error.scalarTarget)
    else enumEquation mode definition uninhabited variants).ModeGuarded mode := by
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact Equation.ModeGuarded.failed mode _
  · exact Equation.ModeGuarded.enumeration _ _ _ _

private structure IndexReady (index : Index) : Prop where
  types : index.typeRows.size = index.source.types.length
  structs : index.structCount = index.source.structs.length
  enums : index.enumCount = index.source.enums.length
  closures : index.closureRows.size = index.source.closures.length

private theorem indexReady (source : Environment) : IndexReady (Index.ofEnvironment source) := by
  trustIrCompilerProof {
    constructor <;> simp [Index.ofEnvironment, Array.size_toArray]
  } {
    constructor <;> simp [Index.ofEnvironment, List.size_toArray]
  }

private theorem zip_right_member {α β : Type} (left : List α) (right : List β)
    (a : α) (b : β) (member : (a,b) ∈ left.zip right) : b ∈ right := by
  induction left generalizing right with
  | nil => cases member
  | cons first rest ih =>
    cases right with
    | nil => cases member
    | cons second right =>
      cases member with
      | head => exact .head _
      | tail _ member => exact .tail _ (ih right member)

private theorem range_loop_bound (bound count : Nat) (tail : List Nat) (position : Nat)
    (inside : count ≤ bound) (tailBound : ∀ value, value ∈ tail → value < bound)
    (member : position ∈ List.range.loop count tail) : position < bound := by
  induction count generalizing tail with
  | zero => exact tailBound position member
  | succ count ih =>
    apply ih (count :: tail) (by omega) _ member
    intro value present
    cases present with
    | head => omega
    | tail _ present => exact tailBound value present

private theorem numbered_bound {α : Type} (rows : List α) (row : α) (position : Nat)
    (member : (row, position) ∈ numbered rows) : position < rows.length := by
  apply range_loop_bound rows.length rows.length [] position (Nat.le_refl _)
  · intro value impossible; cases impossible
  · exact zip_right_member rows (List.range rows.length) row position member

private theorem reserved_node (index : Index) (mode : Mode) (position : Nat)
    (inside : position < index.count) : index.node mode position < globalClosures index + 1 := by
  unfold Index.node globalClosures globalTuples
  split <;> omega

private theorem reserved_type (index : Index) (ready : IndexReady index) (mode : Mode)
    (row : Option Ty) (position : Nat) (member : (row, position) ∈ numbered index.source.types) :
    index.node mode position < globalClosures index + 1 := by
  apply reserved_node
  have bound := numbered_bound _ _ _ member
  have exactCount := ready.types
  unfold Index.count Index.closureBase Index.enumBase Index.structBase
  omega

private theorem reserved_struct (index : Index) (ready : IndexReady index) (mode : Mode)
    (row : StructDef) (position : Nat) (member : (row, position) ∈ numbered index.source.structs) :
    index.node mode (index.structBase + position) < globalClosures index + 1 := by
  apply reserved_node
  have bound := numbered_bound _ _ _ member
  have exactCount := ready.structs
  unfold Index.count Index.closureBase Index.enumBase Index.structBase
  omega

private theorem reserved_enum (index : Index) (ready : IndexReady index) (mode : Mode)
    (row : EnumDef) (position : Nat) (member : (row, position) ∈ numbered index.source.enums) :
    index.node mode (index.enumBase + position) < globalClosures index + 1 := by
  apply reserved_node
  have bound := numbered_bound _ _ _ member
  have exactCount := ready.enums
  unfold Index.count Index.closureBase Index.enumBase Index.structBase
  omega

private theorem reserved_closure (index : Index) (ready : IndexReady index) (mode : Mode)
    (row : ClosureTy) (position : Nat) (member : (row, position) ∈ numbered index.source.closures) :
    index.node mode (index.closureBase + position) < globalClosures index + 1 := by
  apply reserved_node
  have bound := numbered_bound _ _ _ member
  have exactCount := ready.closures
  unfold Index.count Index.closureBase Index.enumBase Index.structBase
  omega

private theorem put_reserved (reserved node : Nat) (inside : node < reserved) (equation : Equation) :
    PreservesState (fun graph => graph.Bounded ∧ reserved ≤ graph.count) (put node equation) := by
  intro graph initial
  exact ⟨initial.1.put node (Nat.lt_of_lt_of_le inside initial.2) equation, initial.2⟩

/-- A shape root either names a reserved shape row or carries an exact
local shape guard. Dynamic execution nodes need not be shape-bounded. -/
def ShapeRoot (index : Index) (graph : Graph) (root : Nat) : Prop :=
  root < index.count ∨ ∃ equation, graph.nodes.find root = some equation ∧ equation.ModeGuarded .shape

theorem ShapeRoot.weaken {index : Index} {before after : Graph} {root : Nat}
    (safe : ShapeRoot index before root) (growth : before.Extends after) :
    ShapeRoot index after root := by
  rcases safe with reserved | ⟨equation, found, guarded⟩
  · exact .inl reserved
  · exact .inr ⟨equation, growth root equation found, guarded⟩

theorem ShapeRoot.copy_rule {index : Index} {graph : Graph} {root owner : Nat}
    (safe : ShapeRoot index graph root) (valid : graph.ModeInvariant index.nodeMode)
    (assigned : index.nodeMode owner = .shape) :
    ((graph.nodes.find root).getD (Equation.alias root)).IndexedRule
      (fun node value => FinishBounds (index.nodeMode node) value) owner := by
  rcases safe with reserved | ⟨equation, found, guarded⟩
  · apply valid.copy_same root owner
    rw [assigned]
    exact (if_pos reserved : index.nodeMode root = .shape).symm
  · rw [found]
    exact guarded.indexed index.nodeMode owner assigned

theorem ShapeRoot.derivation_bounds {index : Index} {graph : Graph} {root : Nat} {value : Summary}
    (safe : ShapeRoot index graph root) (valid : graph.ModeInvariant index.nodeMode)
    (derived : NodeDerivation graph root value) : FinishBounds .shape value := by
  rcases safe with reserved | ⟨equation, found, guarded⟩
  · have bounds := derived.satisfies_at valid
    change FinishBounds (if root < index.count then Mode.shape else .execution) value at bounds
    simpa only [if_pos reserved] using bounds
  · exact NodeDerivation.mode_guarded found guarded derived

private structure ShapeReady (index : Index) : Prop where
  structs : ∀ key position, index.structShapePositions.find key = some position → position < index.structCount
  enums : ∀ key position, index.enumShapePositions.find key = some position → position < index.enumCount

private theorem firstPosition_bound {α : Type} (rows : List α) (id : α → Nat)
    (key position : Nat) (found : (firstPositionIndex rows id).find key = some position) :
    position < rows.length := by
  have bound : ∀ entries : List (α × Nat),
      (∀ row pos, (row, pos) ∈ entries → pos < rows.length) →
      ∀ key pos, (entries.foldr (fun (row, pos) tree => tree.insert (id row) pos)
        (NatIndexTree.empty : NatIndexTree Nat)).find key = some pos → pos < rows.length := by
    intro entries
    induction entries with
    | nil => intro bounded key pos impossible; cases impossible
    | cons first rest ih =>
      rcases first with ⟨row, pos⟩
      intro bounded key result found
      rw [List.foldr_cons, NatIndexTree.find_insert] at found
      split at found
      · cases found
        exact bounded row pos ((trustIrListMemConsSelf _ _))
      · exact ih (fun row pos member => bounded row pos (List.mem_cons_of_mem _ member)) key result found
  exact bound (numbered rows) (fun row pos member => numbered_bound rows row pos member) key position found

private theorem shapeReady (source : Environment) : ShapeReady (Index.ofEnvironment source) := by
  constructor
  · intro key position found
    exact firstPosition_bound source.structs (·.id.index) key position found
  · intro key position found
    exact firstPosition_bound source.enums (·.id.index) key position found

private theorem array_present_bound {α : Type} (rows : Array α) (position : Nat)
    (present : ((trustIrArrayGet? rows position)).isSome = true) : position < rows.size := by
  trustIrCompilerProof {
    unfold Array.get? at present
    split at present
    · assumption
    · cases present
  } {
    by_cases inside : position < rows.size
    · exact inside
    · have absent := Array.getElem?_eq_none (xs := rows) (Nat.le_of_not_lt inside)
      rw [absent] at present
      cases present
  }

private theorem positionIndex_bound {α : Type} (rows : List α) (id : α → Nat)
    (key position : Nat) (found : (positionIndex rows id).find key = some position) :
    position < rows.length := by
  have walk : ∀ entries : List (α × Nat),
      (∀ row pos, (row,pos) ∈ entries → pos < rows.length) →
      ∀ tree : NatIndexTree Nat, (∀ key pos, tree.find key = some pos → pos < rows.length) →
      ∀ key pos, (entries.foldl (fun tree (row,pos) =>
        if id row == pos then tree.insert pos pos else tree) tree).find key = some pos → pos < rows.length := by
    intro entries
    induction entries with
    | nil => intro _ tree valid key pos found; exact valid key pos found
    | cons entry rest ih =>
      rcases entry with ⟨row,pos⟩
      intro bounded tree valid key result found
      rw [List.foldl_cons] at found
      dsimp only at found
      apply ih (fun row pos member => bounded row pos (List.mem_cons_of_mem _ member)) _ _ key result found
      intro query value lookup
      try dsimp only at lookup
      split at lookup
      · rw [NatIndexTree.find_insert] at lookup
        split at lookup
        · cases lookup; exact bounded row pos ((trustIrListMemConsSelf _ _))
        · exact valid query value lookup
      · exact valid query value lookup
  exact walk (numbered rows) (fun row pos member => numbered_bound rows row pos member)
    (firstPositionIndex rows id) (fun key pos found => firstPosition_bound rows id key pos found) key position found

private structure RootReady (index : Index) : Prop where
  structs : ∀ mode key position,
    (if mode == Mode.shape then index.structShapePositions else index.structPositions).find key = some position →
      position < index.structCount
  enums : ∀ mode key position,
    (if mode == Mode.shape then index.enumShapePositions else index.enumPositions).find key = some position →
      position < index.enumCount

private theorem rootReady (source : Environment) : RootReady (Index.ofEnvironment source) := by
  constructor
  · intro mode key position found
    cases mode with
    | shape => exact firstPosition_bound source.structs (·.id.index) key position found
    | execution => exact positionIndex_bound source.structs (·.id.index) key position found
  · intro mode key position found
    cases mode with
    | shape => exact firstPosition_bound source.enums (·.id.index) key position found
    | execution => exact positionIndex_bound source.enums (·.id.index) key position found

private def OriginalPairs (index : Index) (relation : Nat → Nat → Prop) : Prop :=
  ∀ node, node < 2 * index.count + 2 → relation node node

private def RelatedResults {α : Type} (values : (Nat → Nat → Prop) → α → α → Prop)
    (relation : Nat → Nat → Prop) (left right : α × Graph) : Prop :=
  ∃ next, (∀ a b, relation a b → next a b) ∧
    left.2.Correspondence right.2 next ∧ values next left.1 right.1

/-- Compilation may precede installation of original reserved equations.
Correspondence is established in supplied later graphs retaining its output. -/
private def RelatedBuild {α : Type} (index : Index) (values : (Nat → Nat → Prop) → α → α → Prop)
    (action : Build α) : Prop :=
  ∀ left right leftAmbient rightAmbient relation,
    ScalarState (2 * index.count + 2) index.source.model.pointerBytes left →
    ScalarState (2 * index.count + 2) index.source.model.pointerBytes right →
    (action left).2.Extends leftAmbient → (action right).2.Extends rightAmbient →
    leftAmbient.Correspondence rightAmbient relation → OriginalPairs index relation →
    RelatedResults values relation ((action left).1,leftAmbient) ((action right).1,rightAmbient)

private abbrev PairsNode (index : Index) (action : Build Nat) : Prop :=
  RelatedBuild index (fun relation a b => relation a b) action

private abbrev PairsTypes (index : Index) (action : Build (List Nat)) : Prop :=
  RelatedBuild index (fun relation left right => RowsCorrespond relation left right) action

private theorem add_lookup (graph : Graph) (equation : Equation) :
    (SourceLayout.add equation graph).2.nodes.find graph.count = some equation := by
  change (graph.nodes.insert graph.count equation).find graph.count = some equation
  simp [NatIndexTree.find_insert]

private theorem PairsNode.original (index : Index) (root : Nat) (inside : root < 2 * index.count + 2) :
    PairsNode index (pure root) := by
  intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
  exact ⟨relation,(fun _ _ member => member),paired,original root inside⟩

private theorem PairsTypes.nil (index : Index) : PairsTypes index (pure []) := by
  intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
  exact ⟨relation,(fun _ _ member => member),paired,RowsCorrespond.nil⟩

private theorem PairsNode.add (index : Index) (equation : Equation)
    (equations : ∀ relation, OriginalPairs index relation → equation.Corresponds relation equation) :
    PairsNode index (SourceLayout.add equation) := by
  intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
  refine ⟨fun a b => relation a b ∨ a = left.count ∧ b = right.count,
    (fun _ _ member => Or.inl member),?_,Or.inr ⟨rfl,rfl⟩⟩
  exact paired.adjoin (leftGrowth _ _ (add_lookup left equation)) (rightGrowth _ _ (add_lookup right equation))
    ((equations relation original).mono (fun _ _ member => Or.inl member))

private theorem PairsNode.failed (index : Index) (error : Error) : PairsNode index (failed error) :=
  PairsNode.add index _ (fun relation _ => Equation.Corresponds.done relation (.error error))

private theorem PairsNode.scalar (index : Index) (result : Result Summary)
    (admissible : ∀ value, result = .ok value → ScalarSummary index.source.model.pointerBytes value) :
    PairsNode index (addScalar result) := by
  cases result with
  | error error => exact PairsNode.failed index error
  | ok value =>
    intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
    have leftExact := addScalar_exact (2 * index.count + 2) index.source.model.pointerBytes left
      leftValid.1 leftValid.2.1 leftValid.2.2 value (admissible value rfl) _ _ rfl
    have rightExact := addScalar_exact (2 * index.count + 2) index.source.model.pointerBytes right
      rightValid.1 rightValid.2.1 rightValid.2.2 value (admissible value rfl) _ _ rfl
    refine ⟨fun a b => relation a b ∨ a = (addScalar (.ok value) left).1 ∧ b = (addScalar (.ok value) right).1,
      (fun _ _ member => Or.inl member),?_,Or.inr ⟨rfl,rfl⟩⟩
    exact paired.adjoin (leftGrowth _ _ leftExact.2.2) (rightGrowth _ _ rightExact.2.2)
      (Equation.Corresponds.done _ (.ok value))

private theorem PairsNode.from_child (index : Index) (action : Build Nat) (make : Nat → Equation)
    (preserves : PreservesState (ScalarState (2 * index.count + 2) index.source.model.pointerBytes) action)
    (children : PairsNode index action)
    (equations : ∀ relation, OriginalPairs index relation → ∀ a b, relation a b → (make a).Corresponds relation (make b)) :
    PairsNode index (action >>= fun child => SourceLayout.add (make child)) := by
  intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
  have leftNext := preserves left leftValid
  have rightNext := preserves right rightValid
  have leftRetained := (Graph.Extends.allocate leftNext.1 (make (action left).1)).trans leftGrowth
  have rightRetained := (Graph.Extends.allocate rightNext.1 (make (action right).1)).trans rightGrowth
  obtain ⟨middle,included,childGraphs,childPair⟩ := children left right leftAmbient rightAmbient relation
    leftValid rightValid leftRetained rightRetained paired original
  have middleOriginal : OriginalPairs index middle := fun node inside => included _ _ (original node inside)
  refine ⟨fun a b => middle a b ∨ a = (action left).2.count ∧ b = (action right).2.count,
    (fun _ _ member => Or.inl (included _ _ member)),?_,Or.inr ⟨rfl,rfl⟩⟩
  exact childGraphs.adjoin
    (leftGrowth _ _ (add_lookup (action left).2 (make (action left).1)))
    (rightGrowth _ _ (add_lookup (action right).2 (make (action right).1)))
    ((equations middle middleOriginal _ _ childPair).mono (fun _ _ member => Or.inl member))

private theorem PairsNode.from_types (index : Index) (action : Build (List Nat)) (make : List Nat → Equation)
    (preserves : PreservesState (ScalarState (2 * index.count + 2) index.source.model.pointerBytes) action)
    (children : PairsTypes index action)
    (equations : ∀ relation, OriginalPairs index relation → ∀ a b, RowsCorrespond relation a b →
      (make a).Corresponds relation (make b)) :
    PairsNode index (action >>= fun child => SourceLayout.add (make child)) := by
  intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
  have leftNext := preserves left leftValid
  have rightNext := preserves right rightValid
  have leftRetained := (Graph.Extends.allocate leftNext.1 (make (action left).1)).trans leftGrowth
  have rightRetained := (Graph.Extends.allocate rightNext.1 (make (action right).1)).trans rightGrowth
  obtain ⟨middle,included,childGraphs,childPair⟩ := children left right leftAmbient rightAmbient relation
    leftValid rightValid leftRetained rightRetained paired original
  have middleOriginal : OriginalPairs index middle := fun node inside => included _ _ (original node inside)
  refine ⟨fun a b => middle a b ∨ a = (action left).2.count ∧ b = (action right).2.count,
    (fun _ _ member => Or.inl (included _ _ member)),?_,Or.inr ⟨rfl,rfl⟩⟩
  exact childGraphs.adjoin
    (leftGrowth _ _ (add_lookup (action left).2 (make (action left).1)))
    (rightGrowth _ _ (add_lookup (action right).2 (make (action right).1)))
    ((equations middle middleOriginal _ _ childPair).mono (fun _ _ member => Or.inl member))

private theorem PairsTypes.cons (index : Index) (first : Build Nat) (rest : Build (List Nat))
    (preserves : PreservesState (ScalarState (2 * index.count + 2) index.source.model.pointerBytes) first)
    (restGrowth : PreservesGraph rest) (headPair : PairsNode index first) (tailPair : PairsTypes index rest) :
    PairsTypes index (do let head ← first; let tail ← rest; pure (head :: tail)) := by
  intro left right leftAmbient rightAmbient relation leftValid rightValid leftGrowth rightGrowth paired original
  have leftNext := preserves left leftValid
  have rightNext := preserves right rightValid
  have leftRetained := ((restGrowth (first left).2 leftNext.1).equations).trans leftGrowth
  have rightRetained := ((restGrowth (first right).2 rightNext.1).equations).trans rightGrowth
  obtain ⟨middle,included,headGraphs,heads⟩ := headPair left right leftAmbient rightAmbient relation
    leftValid rightValid leftRetained rightRetained paired original
  have middleOriginal : OriginalPairs index middle := fun node inside => included _ _ (original node inside)
  obtain ⟨last,later,tailGraphs,tails⟩ := tailPair (first left).2 (first right).2 leftAmbient rightAmbient middle
    leftNext rightNext leftGrowth rightGrowth headGraphs middleOriginal
  exact ⟨last,(fun _ _ member => later _ _ (included _ _ member)),tailGraphs,
    RowsCorrespond.cons (later _ _ heads) tails⟩

private theorem tuple_sequence_corresponds (index : Index) (mode : Mode) {relation : Nat → Nat → Prop}
    (original : OriginalPairs index relation) {first second : Equation} (paired : first.Corresponds relation second) :
    (if mode == .execution then Equation.sequence [globalTuples index] first else first).Corresponds relation
      (if mode == .execution then Equation.sequence [globalTuples index] second else second) := by
  cases mode with
  | shape => exact paired
  | execution =>
    apply Equation.Corresponds.sequence _ paired
    exact .cons (original _ (by unfold globalTuples; omega)) .nil

private theorem PairsNode.tuple_failed (index : Index) (mode : Mode) (error : Error) :
    PairsNode index (SourceLayout.add (if mode == .execution then Equation.sequence [globalTuples index] (.done (.error error))
      else .done (.error error))) :=
  PairsNode.add index _ (fun relation original =>
    tuple_sequence_corresponds index mode original (Equation.Corresponds.done relation (.error error)))

private theorem PairsNode.original_scaled (index : Index) (mode : Mode) (count child : Nat)
    (inside : child < 2 * index.count + 2) : PairsNode index (SourceLayout.add (scaled mode count child)) :=
  PairsNode.add index _ (fun relation original => Equation.Corresponds.scaled mode count (original child inside))


set_option maxHeartbeats 1000000 in
mutual
  private theorem compileTy_related (index : Index) (ready : RootReady index) (mode : Mode) (ty : Ty) :
      PairsNode index (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact PairsNode.failed index _
    · split
      · rename_i result found
        exact PairsNode.scalar index result (fun value success =>
          scalar_admissible mode index.source ty result value found success)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind,bind_pure]
        case Vector =>
          rename_i count element scalarNone
          repeat first
            | exact PairsNode.failed index _
            | (apply PairsNode.from_child index _ _ (compileTy_scalar_state _ index mode element)
                 (compileTy_related index ready mode element)
               intro relation original a b related
               exact Equation.Corresponds.scaled mode count related)
            | split
        case Tuple =>
          rename_i fields scalarNone
          repeat first
            | exact PairsNode.failed index _
            | exact PairsNode.tuple_failed index mode _
            | (apply PairsNode.from_types index _ _ (compileTypes_scalar_state _ index mode fields)
                 (compileTypes_related index ready mode fields)
               intro relation original a b related
               exact tuple_sequence_corresponds index mode original
                 (Equation.Corresponds.canonicalZip mode "tuple" 0 fields related))
            | (apply PairsNode.from_types index _ _ (compileTypes_scalar_state _ index .shape fields)
                 (compileTypes_related index ready .shape fields)
               intro relation original a b related
               exact tuple_sequence_corresponds index mode original
                 (Equation.Corresponds.declaredMapZip mode "tuple" _ _ _ word64Max false fields _ related))
            | (simp only [pure_bind,bind_pure])
            | split
        case Array =>
          rename_i id count scalarNone
          repeat first
            | exact PairsNode.failed index _
            | split
          apply PairsNode.original_scaled
          have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
            cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
          have inside := array_present_bound index.typeRows id.index present
          unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
          split <;> omega
        all_goals repeat first
          | exact PairsNode.failed index _
          | split
        all_goals try exact PairsNode.failed index _
        trustIrCompilerProof {
          case Struct.h_1 =>
            rename_i position found
            have inside := ready.structs mode _ position found
            apply PairsNode.original
            unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
            split <;> omega
          case Enum.h_1 =>
            rename_i position found
            have inside := ready.enums mode _ position found
            apply PairsNode.original
            unfold Index.node Index.count Index.closureBase Index.enumBase
            split <;> omega
          case Closure.inr.inr =>
            rename_i id scalarNone shape accepted
            have present : ((trustIrArrayGet? index.closureRows id.index)).isSome = true := by
              cases h : ((trustIrArrayGet? index.closureRows id.index)).isSome <;> simp_all
            have inside := array_present_bound index.closureRows id.index present
            apply PairsNode.original
            unfold Index.node Index.count
            split <;> omega
          case Refine.inr.inr =>
            rename_i id predicate scalarNone shape accepted
            have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
              cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
            have inside := array_present_bound index.typeRows id.index present
            apply PairsNode.original
            unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
            split <;> omega
        } {
          case h_1 =>
            rename_i position found
            have inside := ready.structs mode _ position found
            apply PairsNode.original
            unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
            split <;> omega
          case h_1 =>
            rename_i position found
            have inside := ready.enums mode _ position found
            apply PairsNode.original
            unfold Index.node Index.count Index.closureBase Index.enumBase
            split <;> omega
          case h_2.Closure.isFalse.isFalse =>
            rename_i id scalarNone shape accepted
            have present : ((trustIrArrayGet? index.closureRows id.index)).isSome = true := by
              cases h : ((trustIrArrayGet? index.closureRows id.index)).isSome <;> simp_all
            have inside := array_present_bound index.closureRows id.index present
            apply PairsNode.original
            unfold Index.node Index.count
            split <;> omega
          case h_2.Refine.isFalse.isFalse =>
            rename_i id predicate scalarNone shape accepted
            have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
              cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
            have inside := array_present_bound index.typeRows id.index present
            apply PairsNode.original
            unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
            split <;> omega
        }

  private theorem compileTypes_related (index : Index) (ready : RootReady index) (mode : Mode) (types : List Ty) :
      PairsTypes index (compileTypes index mode types) := by
    cases types with
    | nil => rw [compileTypes.eq_def]; exact PairsTypes.nil index
    | cons first rest =>
      rw [compileTypes.eq_def]
      exact PairsTypes.cons index (compileTy index mode first) (compileTypes index mode rest)
        (compileTy_scalar_state _ index mode first) (compileTypes_preserves index mode rest)
        (compileTy_related index ready mode first) (compileTypes_related index ready mode rest)
end


private def BuildsRootBound (index : Index) (action : Build Nat) : Prop :=
  ∀ graph, ScalarState (2 * index.count + 2) index.source.model.pointerBytes graph →
    (action graph).1 < (action graph).2.count

private theorem BuildsRootBound.reserved (index : Index) (root : Nat)
    (inside : root < 2 * index.count + 2) : BuildsRootBound index (pure root) := by
  intro graph valid
  exact Nat.lt_of_lt_of_le inside valid.2.1

private theorem BuildsRootBound.add (index : Index) (equation : Equation) :
    BuildsRootBound index (add equation) := fun _ _ => Nat.lt_succ_self _

private theorem BuildsRootBound.failed (index : Index) (error : Error) :
    BuildsRootBound index (failed error) := BuildsRootBound.add index _

private theorem BuildsRootBound.bind {α : Type} (index : Index) (action : Build α)
    {next : α → Build Nat}
    (preserved : PreservesState (ScalarState (2 * index.count + 2) index.source.model.pointerBytes) action)
    (later : ∀ value, BuildsRootBound index (next value)) : BuildsRootBound index (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (preserved graph valid)

private theorem BuildsRootBound.scalar (index : Index) (result : Result Summary)
    (admissible : ∀ value, result = .ok value → ScalarSummary index.source.model.pointerBytes value) :
    BuildsRootBound index (addScalar result) := by
  cases result with
  | error error => exact BuildsRootBound.failed index error
  | ok value =>
    intro graph valid
    have exactValue := addScalar_exact (2 * index.count + 2) index.source.model.pointerBytes graph
      valid.1 valid.2.1 valid.2.2 value (admissible value rfl) _ _ rfl
    have bounded := (addScalar_preserves (.ok value) graph valid.1).bounded
    by_cases inside : (addScalar (.ok value) graph).1 < (addScalar (.ok value) graph).2.count
    · exact inside
    · have absent := bounded (addScalar (.ok value) graph).1 (by omega)
      have present : (addScalar (.ok value) graph).2.nodes.find (addScalar (.ok value) graph).1 =
          some (.done (.ok value)) := exactValue.2.2
      have impossible := absent.symm.trans present
      cases impossible

private theorem compileTy_root_bound (index : Index) (ready : RootReady index) (mode : Mode) (ty : Ty) :
    BuildsRootBound index (compileTy index mode ty) := by
  rw [compileTy.eq_def]
  dsimp only
  split
  · exact BuildsRootBound.failed index _
  · split
    · rename_i result found
      exact BuildsRootBound.scalar index result (fun value success =>
        scalar_admissible mode index.source ty result value found success)
    · cases ty
      all_goals dsimp only
      all_goals simp only [pure_bind,bind_pure]
      all_goals repeat first
        | exact BuildsRootBound.failed index _
        | exact BuildsRootBound.add index _
        | (apply BuildsRootBound.bind index _ (compileTy_scalar_state _ index mode _); intro child)
        | (apply BuildsRootBound.bind index _ (compileTypes_scalar_state _ index mode _); intro children)
        | (apply BuildsRootBound.bind index _ (compileTypes_scalar_state _ index .shape _); intro children)
        | split
      all_goals try exact BuildsRootBound.failed index _
      trustIrCompilerProof {
        case Struct.h_1 =>
          rename_i position found
          have inside := ready.structs mode _ position found
          apply BuildsRootBound.reserved
          unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
          split <;> omega
        case Enum.h_1 =>
          rename_i position found
          have inside := ready.enums mode _ position found
          apply BuildsRootBound.reserved
          unfold Index.node Index.count Index.closureBase Index.enumBase
          split <;> omega
        case Closure.inr.inr =>
          rename_i id scalarNone shape accepted
          have present : ((trustIrArrayGet? index.closureRows id.index)).isSome = true := by
            cases h : ((trustIrArrayGet? index.closureRows id.index)).isSome <;> simp_all
          have inside := array_present_bound index.closureRows id.index present
          apply BuildsRootBound.reserved
          unfold Index.node Index.count
          split <;> omega
        case Refine.inr.inr =>
          rename_i id predicate scalarNone shape accepted
          have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
            cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
          have inside := array_present_bound index.typeRows id.index present
          apply BuildsRootBound.reserved
          unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
          split <;> omega
      } {
        case h_1 =>
          rename_i position found
          have inside := ready.structs mode _ position found
          apply BuildsRootBound.reserved
          unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
          split <;> omega
        case h_1 =>
          rename_i position found
          have inside := ready.enums mode _ position found
          apply BuildsRootBound.reserved
          unfold Index.node Index.count Index.closureBase Index.enumBase
          split <;> omega
        case h_2.Closure.isFalse.isFalse =>
          rename_i id scalarNone shape accepted
          have present : ((trustIrArrayGet? index.closureRows id.index)).isSome = true := by
            cases h : ((trustIrArrayGet? index.closureRows id.index)).isSome <;> simp_all
          have inside := array_present_bound index.closureRows id.index present
          apply BuildsRootBound.reserved
          unfold Index.node Index.count
          split <;> omega
        case h_2.Refine.isFalse.isFalse =>
          rename_i id predicate scalarNone shape accepted
          have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
            cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
          have inside := array_present_bound index.typeRows id.index present
          apply BuildsRootBound.reserved
          unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase
          split <;> omega
      }

private theorem compileTypes_roots_bound (index : Index) (ready : RootReady index) (mode : Mode) (types : List Ty) :
    ∀ graph, ScalarState (2 * index.count + 2) index.source.model.pointerBytes graph →
      ∀ root ∈ (compileTypes index mode types graph).1, root < (compileTypes index mode types graph).2.count := by
  induction types with
  | nil => intro graph valid root member; cases member
  | cons first rest ih =>
    intro graph valid root member
    let child := compileTy index mode first graph
    let later := compileTypes index mode rest child.2
    have childState := compileTy_scalar_state (2 * index.count + 2) index mode first graph valid
    have childBound := compileTy_root_bound index ready mode first graph valid
    have laterBounds := ih child.2 childState
    have laterGrowth := compileTypes_preserves index mode rest child.2 childState.1
    rw [compileTypes.eq_def] at member ⊢
    change root ∈ child.1 :: later.1 at member
    change root < later.2.count
    rcases List.mem_cons.mp member with same | present
    · subst root
      exact Nat.lt_of_lt_of_le childBound laterGrowth.count_mono
    · exact laterBounds root present

private def ReferenceState (index : Index) (graph : Graph) : Prop :=
  ScalarState (2 * index.count + 2) index.source.model.pointerBytes graph ∧ graph.ReferenceBounds

private theorem add_reference_state (index : Index) (equation : Equation) (graph : Graph)
    (valid : ReferenceState index graph)
    (safe : StepsIn (fun child => child < graph.count + 1) equation.steps) :
    ReferenceState index (add equation graph).2 :=
  ⟨add_scalar_state _ _ equation graph valid.1,
   valid.2.insert (graph.count + 1) (Nat.le_succ _) graph.count equation safe⟩

private theorem failed_reference_state (index : Index) (error : Error) :
    PreservesState (ReferenceState index) (failed error) :=
  fun graph valid => add_reference_state index _ graph valid (Equation.references_done _ _)

private theorem addScalar_reference_bounds (result : Result Summary) :
    PreservesState Graph.ReferenceBounds (addScalar result) := by
  unfold addScalar
  cases result with
  | error error =>
    intro graph valid
    exact valid.insert (graph.count + 1) (Nat.le_succ _) graph.count _ (Equation.references_done _ _)
  | ok value =>
    apply PreservesState.bind (PreservesState.get Graph.ReferenceBounds)
    intro snapshot
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind
      · intro graph valid
        exact valid.insert (graph.count + 1) (Nat.le_succ _) graph.count _ (Equation.references_done _ _)
      · intro node
        apply PreservesState.bind
        · intro graph valid
          exact valid
        · intro unit
          exact PreservesState.pure _ _

private theorem addScalar_reference_state (index : Index) (result : Result Summary)
    (admissible : ∀ value, result = .ok value → ScalarSummary index.source.model.pointerBytes value) :
    PreservesState (ReferenceState index) (addScalar result) := by
  intro graph valid
  exact ⟨addScalar_scalar_state _ _ result admissible graph valid.1,
    addScalar_reference_bounds result graph valid.2⟩

private theorem bind_ty_references {α : Type} (index : Index) (ready : RootReady index)
    (mode : Mode) (ty : Ty) (next : Nat → Build α)
    (preserved : PreservesState (ReferenceState index) (compileTy index mode ty))
    (later : ∀ graph child, child < graph.count → ReferenceState index graph → ReferenceState index (next child graph).2) :
    PreservesState (ReferenceState index) (compileTy index mode ty >>= next) := by
  intro graph valid
  exact later (compileTy index mode ty graph).2 (compileTy index mode ty graph).1
    (compileTy_root_bound index ready mode ty graph valid.1) (preserved graph valid)

private theorem bind_types_references {α : Type} (index : Index) (ready : RootReady index)
    (mode : Mode) (types : List Ty) (next : List Nat → Build α)
    (preserved : PreservesState (ReferenceState index) (compileTypes index mode types))
    (later : ∀ graph children, (∀ child ∈ children, child < graph.count) →
      ReferenceState index graph → ReferenceState index (next children graph).2) :
    PreservesState (ReferenceState index) (compileTypes index mode types >>= next) := by
  intro graph valid
  exact later (compileTypes index mode types graph).2 (compileTypes index mode types graph).1
    (compileTypes_roots_bound index ready mode types graph valid.1) (preserved graph valid)

private theorem add_tuple_reference_state (index : Index) (mode : Mode) (equation : Equation)
    (graph : Graph) (valid : ReferenceState index graph)
    (safe : StepsIn (fun child => child < graph.count) equation.steps) :
    ReferenceState index (add (if mode == .execution then sequence [globalTuples index] equation else equation) graph).2 := by
  apply add_reference_state index _ graph valid
  by_cases executing : (mode == Mode.execution) = true
  · rw [if_pos executing]
    apply Equation.references_sequence
    · intro node member
      have same : node = globalTuples index := by
        rcases List.mem_cons.mp member with same | absent
        · exact same
        · cases absent
      subst node
      have frontier := valid.1.2.1
      unfold globalTuples
      omega
    · exact safe.mono (fun _ inside => Nat.lt_succ_of_lt inside)
  · rw [if_neg executing]
    exact safe.mono (fun _ inside => Nat.lt_succ_of_lt inside)

private theorem compileTuple_reference_state (index : Index) (ready : RootReady index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState (ReferenceState index) (compileTypes index mode fields))
    (shapeSafe : PreservesState (ReferenceState index) (compileTypes index .shape fields)) :
    PreservesState (ReferenceState index) (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind,bind_pure]
  split
  · exact failed_reference_state index _
  · split
    · exact failed_reference_state index _
    · split
      · split
        · intro graph valid
          exact add_tuple_reference_state index mode _ graph valid (Equation.references_done _ _)
        · apply bind_types_references index ready mode fields _ modeSafe
          intro graph children bounded valid
          exact add_tuple_reference_state index mode _ graph valid
            (Equation.references_canonicalZip mode "tuple" 0 fields children bounded)
      · split
        · intro graph valid
          exact add_tuple_reference_state index mode _ graph valid (Equation.references_done _ _)
        · split
          · intro graph valid
            exact add_tuple_reference_state index mode _ graph valid (Equation.references_done _ _)
          · apply bind_types_references index ready .shape fields _ shapeSafe
            intro graph children bounded valid
            exact add_tuple_reference_state index mode _ graph valid
              (Equation.references_declaredZip mode "tuple" _ _ _ _ _ fields children _ bounded)

mutual
  private theorem compileTy_reference_state (index : Index) (ready : RootReady index) (mode : Mode) (ty : Ty) :
      PreservesState (ReferenceState index) (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_reference_state index _
    · split
      · rename_i result found
        exact addScalar_reference_state index result (fun value success =>
          scalar_admissible mode index.source ty result value found success)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind,bind_pure]
        all_goals try exact failed_reference_state index _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_reference_state index _
            | (apply bind_ty_references index ready mode element _ (compileTy_reference_state index ready mode element)
               intro graph child bounded valid
               exact add_reference_state index _ graph valid
                 (Equation.references_scaled mode count child (Nat.lt_succ_of_lt bounded)))
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_reference_state index ready mode fields
            (compileTypes_reference_state index ready mode fields) (compileTypes_reference_state index ready .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true,ite_false,pure_bind,bind_pure]
        case Array id count scalarNone =>
          repeat first
            | exact failed_reference_state index _
            | split
          intro graph valid
          have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
            cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
          have inside := array_present_bound index.typeRows id.index present
          apply add_reference_state index _ graph valid
          apply Equation.references_scaled
          have frontier := valid.1.2.1
          unfold Index.node Index.count Index.closureBase Index.enumBase Index.structBase at *
          split <;> omega
        all_goals repeat first
          | exact failed_reference_state index _
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_reference_state (index : Index) (ready : RootReady index) (mode : Mode) (types : List Ty) :
      PreservesState (ReferenceState index) (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_reference_state index ready mode first)
      intro child
      apply PreservesState.bind (compileTypes_reference_state index ready mode rest)
      intro children
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def BuildsReferenceEquation (index : Index) (action : Build Equation) : Prop :=
  ∀ graph, ReferenceState index graph →
    ReferenceState index (action graph).2 ∧ StepsIn (fun child => child < (action graph).2.count) (action graph).1.steps

private theorem BuildsReferenceEquation.pure (index : Index) (equation : Equation)
    (safe : ∀ graph, ReferenceState index graph → StepsIn (fun child => child < graph.count) equation.steps) :
    BuildsReferenceEquation index (pure equation) := fun graph valid => ⟨valid,safe graph valid⟩

private theorem BuildsReferenceEquation.from_types (index : Index) (ready : RootReady index)
    (mode : Mode) (types : List Ty) (make : List Nat → Equation)
    (safe : ∀ (graph : Graph) (children : List Nat), (∀ child ∈ children, child < graph.count) →
      StepsIn (fun child => child < graph.count) (make children).steps) :
    BuildsReferenceEquation index (do let children ← compileTypes index mode types; Pure.pure (make children)) := by
  intro graph valid
  exact ⟨compileTypes_reference_state index ready mode types graph valid,
    safe _ _ (compileTypes_roots_bound index ready mode types graph valid.1)⟩

private theorem structEquation_reference (index : Index) (ready : RootReady index) (mode : Mode) (definition : StructDef) :
    BuildsReferenceEquation index (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind,bind_pure]
  repeat first
    | (apply BuildsReferenceEquation.pure index; intro graph valid; exact Equation.references_done _ _)
    | (apply BuildsReferenceEquation.from_types index ready mode _ _
       intro graph children bounded
       first
       | exact Equation.references_canonicalZip mode "struct" _ _ children bounded
       | exact Equation.references_declaredMapZip mode "struct" _ _ _ _ _ definition.fields (·.ty) (·.offset) children bounded)
    | split

private theorem closureEquation_reference (index : Index) (ready : RootReady index) (position : Nat) (definition : ClosureTy) :
    BuildsReferenceEquation index (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind,bind_pure]
  repeat first
    | (apply BuildsReferenceEquation.pure index; intro graph valid; exact Equation.references_done _ _)
    | (apply BuildsReferenceEquation.from_types index ready .shape _ _
       intro graph children bounded
       exact Equation.references_declaredZip .shape "closure" position _ _ _ _ definition.captures children _ bounded)
    | split

private def ReferenceNodeAction (index : Index) (action : Build Nat) : Prop :=
  ∀ graph, ReferenceState index graph → ReferenceState index (action graph).2 ∧ (action graph).1 < (action graph).2.count

private theorem ReferenceNodeAction.typed (index : Index) (ready : RootReady index) (mode : Mode) (ty : Ty) :
    ReferenceNodeAction index (compileTy index mode ty) := fun graph valid =>
  ⟨compileTy_reference_state index ready mode ty graph valid,compileTy_root_bound index ready mode ty graph valid.1⟩

private theorem ReferenceNodeAction.leaf (index : Index) (value : Summary) :
    ReferenceNodeAction index (add (.done (.ok value))) := fun graph valid =>
  ⟨add_reference_state index _ graph valid (Equation.references_done _ _),Nat.lt_succ_self _⟩

private theorem enumChild_reference (index : Index) (ready : RootReady index) (mode : Mode)
    (descriptor : Bool) (ty : Ty) :
    ReferenceNodeAction index (match ty with
      | .Never => if descriptor then add (.done (.ok { size := 0, align := some 1 })) else compileTy index mode ty
      | _ => compileTy index mode ty) := by
  cases ty <;> repeat first
    | exact ReferenceNodeAction.typed index ready mode _
    | exact ReferenceNodeAction.leaf index _
    | split

private theorem enumNodes_reference (index : Index) (ready : RootReady index) (mode : Mode)
    (descriptor : Bool) (types : List Ty) :
    ∀ graph, ReferenceState index graph →
      ReferenceState index (enumNodes index mode descriptor types graph).2 ∧
      ∀ child ∈ (enumNodes index mode descriptor types graph).1, child.2 < (enumNodes index mode descriptor types graph).2.count := by
  induction types with
  | nil =>
    rw [enumNodes.eq_def]
    intro graph valid
    exact ⟨valid,fun _ member => by cases member⟩
  | cons first rest ih =>
    intro graph valid
    let action : Build Nat := match first with
      | .Never => if descriptor then add (.done (.ok { size := 0, align := some 1 })) else compileTy index mode first
      | _ => compileTy index mode first
    let child := action graph
    let later := enumNodes index mode descriptor rest child.2
    have childSafe := enumChild_reference index ready mode descriptor first graph valid
    have tailSafe := ih child.2 childSafe.1
    have growth := enumNodes_preserves index mode descriptor rest child.2 childSafe.1.1.1
    have executed : enumNodes index mode descriptor (first :: rest) graph =
        ((first,child.1) :: later.1,later.2) := by
      rw [enumNodes.eq_def]
      cases first <;> try rfl
      cases descriptor <;> rfl
    rw [executed]
    change ReferenceState index later.2 ∧ ∀ entry ∈ (first,child.1) :: later.1, entry.2 < later.2.count
    refine ⟨tailSafe.1,?_⟩
    intro entry member
    cases member with
    | head => exact Nat.lt_of_lt_of_le childSafe.2 growth.count_mono
    | tail _ member => exact tailSafe.2 entry member

private theorem variantEquation_reference {region : Nat → Prop} (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) (safe : ∀ child ∈ children, region child.2) :
    StepsIn region (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets => if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty,child),offset) => (ty,some offset,child)))).steps := by
  cases layout : definition.layout with
  | none => exact Equation.references_canonicalFields mode "enum" definition.id.index children safe
  | some descriptor =>
    dsimp only
    cases row : (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
    | none => exact True.intro
    | some offsets =>
      dsimp only
      by_cases mismatch : (offsets.length != children.length) = true
      · rw [if_pos mismatch]; exact True.intro
      · rw [if_neg mismatch]; exact Equation.references_variantFields mode definition.id.index _ _ children offsets safe

private theorem add_covers (equation : Equation) : CoversGraph (add equation) :=
  fun graph => Graph.DomainCovers.allocate graph equation

private theorem put_covers (node : Nat) (equation : Equation) : CoversGraph (put node equation) :=
  fun graph => Graph.DomainCovers.write graph node equation

private theorem failed_covers (error : Error) : CoversGraph (failed error) := add_covers _

private theorem leaves_covers (update : NatIndexTree Nat → NatIndexTree Nat) :
    CoversGraph (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) := by
  intro graph
  exact ⟨Nat.le_refl _,fun _ found => found,fun node lower upper => by
    change node < graph.count at upper
    omega⟩

private theorem addScalar_covers (result : Result Summary) : CoversGraph (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_covers error
  | ok value =>
    apply CoversGraph.bind CoversGraph.get
    intro graph
    split
    · exact CoversGraph.pure _
    · apply CoversGraph.bind (add_covers _)
      intro node
      apply CoversGraph.bind (leaves_covers (fun leaves => leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact CoversGraph.pure _

mutual
  private theorem compileTy_covers (index : Index) (mode : Mode) (ty : Ty) :
      CoversGraph (compileTy index mode ty) := by
    cases hty : ty
    all_goals rw [compileTy.eq_def]
    all_goals dsimp only [scalar]
    all_goals simp only [pure_bind, bind_pure]
    case Vector count element =>
      repeat first
        | exact failed_covers _
        | (apply CoversGraph.bind (compileTy_covers index mode element)
           intro child
           exact add_covers _)
        | split
    case Tuple fields =>
      repeat first
        | exact failed_covers _
        | exact add_covers _
        | (apply CoversGraph.bind (compileTypes_covers index mode fields)
           intro children
           exact add_covers _)
        | (apply CoversGraph.bind (compileTypes_covers index .shape fields)
           intro children
           exact add_covers _)
        | split
    all_goals repeat first
      | exact addScalar_covers _
      | exact add_covers _
      | exact CoversGraph.pure _
      | split
  termination_by sizeOf ty
  private theorem compileTypes_covers (index : Index) (mode : Mode) (types : List Ty) :
      CoversGraph (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases htypes : types with
    | nil => exact CoversGraph.pure _
    | cons first rest =>
      apply CoversGraph.bind (compileTy_covers index mode first)
      intro child
      apply CoversGraph.bind (compileTypes_covers index mode rest)
      intro later
      exact CoversGraph.pure _
  termination_by sizeOf types
end

private theorem structEquation_covers (index : Index) (mode : Mode) (definition : StructDef) :
    CoversGraph (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact CoversGraph.pure _
    | (apply CoversGraph.bind (compileTypes_covers _ _ _)
       intro children
       exact CoversGraph.pure _)
    | split

private theorem closureEquation_covers (index : Index) (position : Nat) (definition : ClosureTy) :
    CoversGraph (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact CoversGraph.pure _
    | (apply CoversGraph.bind (compileTypes_covers _ _ _)
       intro children
       exact CoversGraph.pure _)
    | split

private theorem enumNodes_covers (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    CoversGraph (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact CoversGraph.pure _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply CoversGraph.bind (compileTy_covers _ _ _)
         intro child
         apply CoversGraph.bind ih
         intro later
         exact CoversGraph.pure _)
      | (apply CoversGraph.bind (add_covers _)
         intro child
         apply CoversGraph.bind ih
         intro later
         exact CoversGraph.pure _)
      | split

private def BuildsShapeRoot (lower : Nat) (index : Index) (action : Build Nat) : Prop :=
  ∀ graph, ScalarState lower index.source.model.pointerBytes graph →
    ShapeRoot index (action graph).2 (action graph).1

private theorem BuildsShapeRoot.reserved (lower : Nat) (index : Index) (root : Nat)
    (inside : root < index.count) : BuildsShapeRoot lower index (pure root) :=
  fun _ _ => .inl inside

private theorem BuildsShapeRoot.add (lower : Nat) (index : Index) (equation : Equation)
    (safe : equation.ModeGuarded .shape) : BuildsShapeRoot lower index (add equation) := by
  intro graph valid
  apply Or.inr
  refine ⟨equation, ?_, safe⟩
  change (graph.nodes.insert graph.count equation).find graph.count = some equation
  rw [NatIndexTree.find_insert, if_pos rfl]

private theorem BuildsShapeRoot.failed (lower : Nat) (index : Index) (error : Error) :
    BuildsShapeRoot lower index (failed error) :=
  BuildsShapeRoot.add lower index _ (Equation.ModeGuarded.failed .shape error)

private theorem BuildsShapeRoot.bind {α : Type} (lower : Nat) (index : Index) (action : Build α)
    {next : α → Build Nat} (preserved : PreservesState (ScalarState lower index.source.model.pointerBytes) action)
    (later : ∀ value, BuildsShapeRoot lower index (next value)) :
    BuildsShapeRoot lower index (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (preserved graph valid)

private theorem BuildsShapeRoot.scalar (lower : Nat) (index : Index) (result : Result Summary)
    (admissible : ∀ value, result = .ok value → ScalarSummary index.source.model.pointerBytes value) :
    BuildsShapeRoot lower index (addScalar result) := by
  cases result with
  | error error => exact BuildsShapeRoot.failed lower index error
  | ok value =>
    intro graph valid
    have scalarValue := admissible value rfl
    have exactValue := addScalar_exact lower index.source.model.pointerBytes graph
      valid.1 valid.2.1 valid.2.2 value scalarValue _ _ rfl
    exact Or.inr ⟨Equation.done (.ok value), exactValue.2.2,
      Equation.ModeGuarded.done .shape _ (by
        intro result same
        cases same
        exact scalarValue.finish_bounds index.source.model .shape)⟩

private theorem compileTy_shape_root (lower : Nat) (index : Index) (ready : ShapeReady index) (ty : Ty) :
    BuildsShapeRoot lower index (compileTy index .shape ty) := by
  rw [compileTy.eq_def]
  dsimp only
  simp only [show (Mode.shape == Mode.execution) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ite_false]
  split
  · rename_i result found
    exact BuildsShapeRoot.scalar lower index result (fun value success =>
      scalar_admissible .shape index.source ty result value found success)
  · cases ty
    all_goals dsimp only
    all_goals simp only [pure_bind, bind_pure]
    all_goals repeat first
      | exact BuildsShapeRoot.failed lower index _
      | (apply BuildsShapeRoot.add; exact Equation.ModeGuarded.scaled _ _ _)
      | (apply BuildsShapeRoot.bind lower index _ (compileTy_scalar_state lower index .shape _); intro child)
      | (apply BuildsShapeRoot.bind lower index _ (compileTypes_scalar_state lower index .shape _); intro children)
      | (apply BuildsShapeRoot.add
         repeat first
           | exact Equation.ModeGuarded.failed _ _
           | exact Equation.ModeGuarded.canonicalFields _ _ _ _
           | exact Equation.ModeGuarded.declaredFields _ _ _ _ _ _ _ _
           | apply Equation.ModeGuarded.sequence
           | split)
      | split

    all_goals try exact BuildsShapeRoot.failed lower index _
    trustIrCompilerProof {
      case Struct.h_1 =>
        rename_i position found
        have inside := ready.structs _ position (by
          simpa only [show (Mode.shape == Mode.shape) = true from rfl, ite_true] using found)
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count Index.closureBase Index.enumBase
        omega
      case Enum.h_1 =>
        rename_i position found
        have inside := ready.enums _ position (by
          simpa only [show (Mode.shape == Mode.shape) = true from rfl, ite_true] using found)
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count Index.closureBase
        omega
      case Closure.inr =>
        rename_i id scalarNone accepted
        have present : ((trustIrArrayGet? index.closureRows id.index)).isSome = true := by
          cases h : ((trustIrArrayGet? index.closureRows id.index)).isSome <;> simp_all
        have inside := array_present_bound index.closureRows id.index present
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count
        omega
      case Refine.inr =>
        rename_i id predicate scalarNone accepted
        have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
          cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
        have inside := array_present_bound index.typeRows id.index present
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count Index.closureBase Index.enumBase Index.structBase
        omega
    } {
      case h_1 =>
        rename_i position found
        have inside := ready.structs _ position (by
          simpa only [show (Mode.shape == Mode.shape) = true from rfl, ite_true] using found)
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count Index.closureBase Index.enumBase
        omega
      case h_1 =>
        rename_i position found
        have inside := ready.enums _ position (by
          simpa only [show (Mode.shape == Mode.shape) = true from rfl, ite_true] using found)
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count Index.closureBase
        omega
      case h_2.Closure.isFalse =>
        rename_i id scalarNone accepted
        have present : ((trustIrArrayGet? index.closureRows id.index)).isSome = true := by
          cases h : ((trustIrArrayGet? index.closureRows id.index)).isSome <;> simp_all
        have inside := array_present_bound index.closureRows id.index present
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count
        omega
      case h_2.Refine.isFalse =>
        rename_i id predicate scalarNone accepted
        have present : ((trustIrArrayGet? index.typeRows id.index)).isSome = true := by
          cases h : ((trustIrArrayGet? index.typeRows id.index)).isSome <;> simp_all
        have inside := array_present_bound index.typeRows id.index present
        apply BuildsShapeRoot.reserved
        simp only [Index.node, show (Mode.shape == Mode.shape) = true from rfl, ite_true, Nat.zero_add]
        unfold Index.count Index.closureBase Index.enumBase Index.structBase
        omega
    }

private def ModeState (index : Index) (graph : Graph) : Prop :=
  ScalarState (2 * index.count + 2) index.source.model.pointerBytes graph ∧
    graph.ModeInvariant index.nodeMode

private theorem add_mode_state (index : Index) (equation : Equation)
    (safe : equation.ModeGuarded .execution) : PreservesState (ModeState index) (add equation) := by
  intro graph state
  refine ⟨add_scalar_state _ _ equation graph state.1, ?_⟩
  exact state.2.insert graph.count equation (safe.indexed index.nodeMode graph.count
    (index.nodeMode_dynamic graph.count (by have frontier := state.1.2.1; omega)))

private theorem failed_mode_state (index : Index) (error : Error) :
    PreservesState (ModeState index) (failed error) :=
  add_mode_state index _ (Equation.ModeGuarded.failed .execution error)

private def ModeGraph (index : Index) (graph : Graph) : Prop :=
  index.count ≤ graph.count ∧ graph.ModeInvariant index.nodeMode

private theorem add_mode_graph (index : Index) (equation : Equation)
    (safe : equation.ModeGuarded .execution) : PreservesState (ModeGraph index) (add equation) := by
  intro graph state
  exact ⟨Nat.le_step state.1, state.2.insert graph.count equation
    (safe.indexed index.nodeMode graph.count (index.nodeMode_dynamic graph.count state.1))⟩

private theorem leaves_mode_graph (index : Index) (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState (ModeGraph index)
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun _ state => state

private theorem addScalar_mode_graph (index : Index) (result : Result Summary)
    (admissible : ∀ value, result = .ok value → ScalarSummary index.source.model.pointerBytes value) :
    PreservesState (ModeGraph index) (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact add_mode_graph index _ (Equation.ModeGuarded.failed .execution error)
  | ok value =>
    apply PreservesState.bind (PreservesState.get (ModeGraph index))
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_mode_graph index _
        (Equation.ModeGuarded.done .execution _ (by
          intro result same
          cases same
          exact (admissible value rfl).finish_bounds index.source.model .execution)))
      intro node
      apply PreservesState.bind (leaves_mode_graph index (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _

private theorem addScalar_mode_state (index : Index) (result : Result Summary)
    (admissible : ∀ value, result = .ok value → ScalarSummary index.source.model.pointerBytes value) :
    PreservesState (ModeState index) (addScalar result) := by
  intro graph state
  exact ⟨addScalar_scalar_state _ index.source.model.pointerBytes result admissible graph state.1,
    (addScalar_mode_graph index result admissible graph
      ⟨by have frontier := state.1.2.1; omega, state.2⟩).2⟩

set_option maxHeartbeats 1000000 in
private theorem compileTuple_mode_state (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState (ModeState index) (compileTypes index mode fields))
    (shapeSafe : PreservesState (ModeState index) (compileTypes index .shape fields)) :
    PreservesState (ModeState index) (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_mode_state index _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_mode_state
       apply Equation.ModeGuarded.execution (mode := mode)
       repeat first
         | exact Equation.ModeGuarded.failed _ _
         | exact Equation.ModeGuarded.canonicalFields _ _ _ _
         | exact Equation.ModeGuarded.declaredFields _ _ _ _ _ _ _ _
         | apply Equation.ModeGuarded.sequence
         | split)
    | split

mutual
  private theorem compileTy_mode_state (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState (ModeState index) (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_mode_state index _
    · split
      · rename_i result found
        exact addScalar_mode_state index result (fun value success =>
          scalar_admissible mode index.source ty result value found success)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        case Vector count element scalarNone =>
          repeat first
            | exact failed_mode_state index _
            | (apply PreservesState.bind (compileTy_mode_state index mode element)
               intro child
               exact add_mode_state index _ (Equation.ModeGuarded.scaled mode _ _).execution)
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_mode_state index mode fields
            (compileTypes_mode_state index mode fields) (compileTypes_mode_state index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_mode_state index _
          | exact add_mode_state index _ (Equation.ModeGuarded.scaled mode _ _).execution
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_mode_state (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState (ModeState index) (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_mode_state index mode first)
      intro child
      apply PreservesState.bind (compileTypes_mode_state index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private theorem structEquation_mode_state (index : Index) (mode : Mode) (definition : StructDef) :
    PreservesState (ModeState index) (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (compileTypes_mode_state index mode _)
       intro children
       exact PreservesState.pure _ _)
    | split

private theorem closureEquation_mode_state (index : Index) (position : Nat) (definition : ClosureTy) :
    PreservesState (ModeState index) (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (compileTypes_mode_state index .shape _)
       intro children
       exact PreservesState.pure _ _)
    | split

private theorem enumNodes_mode_state (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState (ModeState index) (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_mode_state index mode _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_mode_state index _
           (Equation.ModeGuarded.done .execution _ (by
             intro value same; cases same; exact FinishBounds.unit .execution)))
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private theorem put_mode_state (index : Index) (node : Nat) (inside : node < 2 * index.count + 2)
    (equation : Equation)
    (safe : equation.IndexedRule (fun node value => FinishBounds (index.nodeMode node) value) node) :
    PreservesState (ModeState index) (put node equation) := by
  intro graph state
  exact ⟨put_scalar_state _ _ node inside equation graph state.1, state.2.insert node equation safe⟩

private def BuildsIndexedEquation (index : Index) (owner : Nat) (action : Build Equation) : Prop :=
  ∀ graph, ModeState index graph → ModeState index (action graph).2 ∧
    (action graph).1.IndexedRule (fun node value => FinishBounds (index.nodeMode node) value) owner

private theorem BuildsIndexedEquation.guarded (index : Index) (owner : Nat) (mode : Mode)
    (action : Build Equation) (preserved : PreservesState (ModeState index) action)
    (guarded : BuildsModeEquation mode action) (assigned : index.nodeMode owner = mode) :
    BuildsIndexedEquation index owner action :=
  fun graph state => ⟨preserved graph state, (guarded graph).indexed index.nodeMode owner assigned⟩

private theorem BuildsIndexedEquation.install_yield {α : Type} (index : Index) (owner : Nat)
    (inside : owner < 2 * index.count + 2) (result : α) {action : Build Equation}
    (safe : BuildsIndexedEquation index owner action) :
    PreservesState (ModeState index) (do put owner (← action); Pure.pure result) := by
  intro graph state
  have built := safe graph state
  exact put_mode_state index owner inside (action graph).1 built.2 (action graph).2 built.1

private theorem compileCopy_mode (index : Index) (ready : ShapeReady index) (mode : Mode) (ty : Ty)
    (owner : Nat) (assigned : index.nodeMode owner = mode) :
    BuildsIndexedEquation index owner (do
      let child ← compileTy index mode ty
      let graph ← get
      pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph state
  have preserved := compileTy_mode_state index mode ty graph state
  refine ⟨preserved, ?_⟩
  change (((compileTy index mode ty graph).2.nodes.find (compileTy index mode ty graph).1).getD
    (alias (compileTy index mode ty graph).1)).IndexedRule _ owner
  cases mode with
  | shape => exact (compileTy_shape_root _ index ready ty graph state.1).copy_rule preserved.2 assigned
  | execution => exact preserved.2.copy_execution _ owner assigned

private theorem type_mode (index : Index) (ready : IndexReady index) (mode : Mode)
    (entry : Option Ty) (position : Nat) (member : (entry, position) ∈ numbered index.source.types) :
    index.nodeMode (index.node mode position) = mode := by
  apply index.nodeMode_node
  have bound := numbered_bound _ _ _ member
  have size := ready.types
  unfold Index.count Index.closureBase Index.enumBase Index.structBase
  omega

private theorem struct_mode (index : Index) (ready : IndexReady index) (mode : Mode)
    (entry : StructDef) (position : Nat) (member : (entry, position) ∈ numbered index.source.structs) :
    index.nodeMode (index.node mode (index.structBase + position)) = mode := by
  apply index.nodeMode_node
  have bound := numbered_bound _ _ _ member
  have size := ready.structs
  unfold Index.count Index.closureBase Index.enumBase
  omega

private theorem enum_mode (index : Index) (ready : IndexReady index) (mode : Mode)
    (entry : EnumDef) (position : Nat) (member : (entry, position) ∈ numbered index.source.enums) :
    index.nodeMode (index.node mode (index.enumBase + position)) = mode := by
  apply index.nodeMode_node
  have bound := numbered_bound _ _ _ member
  have size := ready.enums
  unfold Index.count Index.closureBase
  omega

private theorem closure_mode (index : Index) (ready : IndexReady index) (mode : Mode)
    (entry : ClosureTy) (position : Nat) (member : (entry, position) ∈ numbered index.source.closures) :
    index.nodeMode (index.node mode (index.closureBase + position)) = mode := by
  apply index.nodeMode_node
  have bound := numbered_bound _ _ _ member
  have size := ready.closures
  unfold Index.count
  omega

/-- Empty reserved slots at or beyond the next preparation destination. -/
private def PreparationState (lower pointerBytes filled : Nat) (graph : Graph) : Prop :=
  ScalarState lower pointerBytes graph ∧
    ∀ node, filled ≤ node → node < lower → graph.nodes.find node = none

/-- A real state action advances the reserved prefix and retains every old equation. -/
private def PreparationStep {α : Type} (lower pointerBytes first last : Nat) (action : Build α) : Prop :=
  ∀ graph, PreparationState lower pointerBytes first graph →
    PreparationState lower pointerBytes last (action graph).2 ∧ graph.Extends (action graph).2

private theorem PreparationStep.pure {α : Type} (lower pointerBytes filled : Nat) (value : α) :
    PreparationStep lower pointerBytes filled filled (pure value : Build α) :=
  fun graph state => ⟨state,Graph.Extends.refl graph⟩

private theorem PreparationStep.get (lower pointerBytes filled : Nat) :
    PreparationStep lower pointerBytes filled filled (get : Build Graph) :=
  fun graph state => ⟨state,Graph.Extends.refl graph⟩

private theorem PreparationStep.bind {α β : Type} {lower pointerBytes first middle last : Nat}
    {action : Build α} {next : α → Build β}
    (before : PreparationStep lower pointerBytes first middle action)
    (after : ∀ value, PreparationStep lower pointerBytes middle last (next value)) :
    PreparationStep lower pointerBytes first last (action >>= next) := by
  intro graph state
  have head := before graph state
  have tail := after (action graph).1 (action graph).2 head.1
  exact ⟨tail.1,head.2.trans tail.2⟩

private theorem PreparationStep.preserving {α : Type} (lower pointerBytes filled : Nat) (action : Build α)
    (safe : PreservesState (ScalarState lower pointerBytes) action)
    (growth : PreservesGraph action) (reserved : KeepsPrefix lower action) :
    PreparationStep lower pointerBytes filled filled action := by
  intro graph state
  refine ⟨⟨safe graph state.1,?_⟩,(growth graph state.1.1).equations⟩
  intro node after inside
  exact (reserved graph state.1.1 state.1.2.1 node inside).trans (state.2 node after inside)

private theorem PreparationStep.put (lower pointerBytes filled : Nat) (inside : filled < lower)
    (equation : Equation) : PreparationStep lower pointerBytes filled (filled + 1) (put filled equation) := by
  intro graph state
  have empty := state.2 filled (Nat.le_refl _) inside
  refine ⟨⟨put_scalar_state lower pointerBytes filled inside equation graph state.1,?_⟩,
    Graph.Extends.insert_fresh graph filled equation empty⟩
  intro node later bound
  change (graph.nodes.insert filled equation).find node = none
  rw [NatIndexTree.find_insert,if_neg (by omega : node ≠ filled)]
  exact state.2 node (by omega) bound

/-- The induction index is the position in the actual list, not merely a
member's declared numeric field. This preserves order through numbered loops. -/
private theorem PreparationStep.forIn_ordered {α : Type} (lower pointerBytes start : Nat)
    (rows : List α) (body : α → Unit → Build (ForInStep Unit))
    (yields : ∀ row graph, (body row () graph).1 = .yield ())
    (step : ∀ position row, (trustIrListGet? rows position) = some row →
      PreparationStep lower pointerBytes (start + position) (start + position + 1) (body row ())) :
    PreparationStep lower pointerBytes start (start + rows.length) (ForIn.forIn rows () body) := by
  induction rows generalizing start with
  | nil =>
    rw [List.forIn_nil]
    exact PreparationStep.pure lower pointerBytes start ()
  | cons first rest ih =>
    intro graph state
    have head := step 0 first rfl graph (by simpa only [Nat.add_zero] using state)
    have tail := ih (start + 1) (fun position row found => by
      have later := step (position + 1) row (by simpa only [trustIrListGetConsSucc] using found)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later)
      (body first () graph).2 head.1
    have outcome := yields first graph
    cases executed : body first () graph with
    | mk selected after =>
      rw [executed] at outcome
      cases outcome
      simpa only [List.forIn_cons,Bind.bind,StateT.bind,executed,List.length_cons,Nat.succ_eq_add_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        And.intro tail.1 (head.2.trans tail.2)

private theorem PreparationStep.forIn {α β : Type} (lower pointerBytes filled : Nat)
    (rows : List α) (initial : β) (body : α → β → Build (ForInStep β))
    (step : ∀ row, row ∈ rows → ∀ acc, PreparationStep lower pointerBytes filled filled (body row acc)) :
    PreparationStep lower pointerBytes filled filled (ForIn.forIn rows initial body) := by
  induction rows generalizing initial with
  | nil => rw [List.forIn_nil]; exact PreparationStep.pure lower pointerBytes filled _
  | cons first rest ih =>
    rw [List.forIn_cons]
    apply PreparationStep.bind (step first ((trustIrListMemConsSelf _ _)) initial)
    intro next
    cases next with
    | done value => exact PreparationStep.pure lower pointerBytes filled _
    | yield value => exact ih value (fun row member => step row (List.mem_cons_of_mem _ member))

/-- Recover the actual state at a selected source occurrence, with its output
retained by the remainder of the ordered loop. -/
private theorem PreparationStep.forIn_visit {α : Type} (lower pointerBytes start : Nat)
    (rows : List α) (body : α → Unit → Build (ForInStep Unit))
    (yields : ∀ row graph, (body row () graph).1 = .yield ())
    (step : ∀ position row, (trustIrListGet? rows position) = some row →
      PreparationStep lower pointerBytes (start + position) (start + position + 1) (body row ()))
    (position : Nat) (row : α) (found : (trustIrListGet? rows position) = some row)
    (graph : Graph) (state : PreparationState lower pointerBytes start graph) :
    ∃ before after, PreparationState lower pointerBytes (start + position) before ∧
      body row () before = (.yield (),after) ∧ after.Extends (ForIn.forIn rows () body graph).2 := by
  induction rows generalizing start position graph with
  | nil => cases found
  | cons first rest ih =>
    have head := step 0 first rfl graph (by simpa only [Nat.add_zero] using state)
    have nextStep : ∀ position row, (trustIrListGet? rest position) = some row →
        PreparationStep lower pointerBytes (start + 1 + position) (start + 1 + position + 1) (body row ()) := by
      intro position row found
      have later := step (position + 1) row (by simpa only [trustIrListGetConsSucc] using found)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using later
    have outcome := yields first graph
    cases executed : body first () graph with
    | mk selected after =>
      rw [executed] at outcome
      cases outcome
      rw [executed] at head
      cases position with
      | zero =>
        cases found
        have tail := PreparationStep.forIn_ordered lower pointerBytes (start + 1) rest body yields nextStep after head.1
        refine ⟨graph,after,?_,executed,?_⟩
        · simpa only [Nat.add_zero] using state
        · simpa only [List.forIn_cons,Bind.bind,StateT.bind,executed] using tail.2
      | succ position =>
        obtain ⟨before,last,valid,ran,retained⟩ := ih (start + 1) nextStep position found after head.1
        refine ⟨before,last,?_,ran,?_⟩
        · simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using valid
        · simpa only [List.forIn_cons,Bind.bind,StateT.bind,executed] using retained

private theorem structEquation_keeps_prefix (lower : Nat) (index : Index) (mode : Mode) (definition : StructDef) :
    KeepsPrefix lower (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  try simp only [pure_bind,bind_pure]
  repeat first
    | exact fun _ _ _ _ _ => rfl
    | (apply KeepsPrefix.bind lower (compileTypes_preserves index mode _) (compileTypes_keeps_prefix lower index mode _)
       intro children
       exact fun _ _ _ _ _ => rfl)
    | split

private theorem closureEquation_keeps_prefix (lower : Nat) (index : Index) (position : Nat) (definition : ClosureTy) :
    KeepsPrefix lower (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind,bind_pure]
  repeat first
    | exact fun _ _ _ _ _ => rfl
    | (apply KeepsPrefix.bind lower (compileTypes_preserves index .shape _) (compileTypes_keeps_prefix lower index .shape _)
       intro children
       exact fun _ _ _ _ _ => rfl)
    | split

private theorem enumNodes_keeps_prefix (lower : Nat) (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    KeepsPrefix lower (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact fun _ _ _ _ _ => rfl
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply KeepsPrefix.bind lower (compileTy_preserves index mode _) (compileTy_keeps_prefix lower index mode _)
         intro child
         apply KeepsPrefix.bind lower (enumNodes_preserves index mode descriptor rest) ih
         intro later
         exact fun _ _ _ _ _ => rfl)
      | (apply KeepsPrefix.bind lower (add_preserves _) (KeepsPrefix.add lower _)
         intro child
         apply KeepsPrefix.bind lower (enumNodes_preserves index mode descriptor rest) ih
         intro later
         exact fun _ _ _ _ _ => rfl)
      | split

private def buildProgram (index : Index) (facts : NatIndexTree Unit) : Build Unit := do
  for mode in [Mode.shape, Mode.execution] do
    for (entry, position) in numbered index.source.types do
      let equation ← match entry with
        | none => pure (.done (.error (.missingType position)))
        | some ty => do
          let child ← compileTy index mode ty
          let graph ← get
          -- Copy a compiled root equation rather than adding an alias
          -- frame for each type-table link. Forward nominal references
          -- remain aliases until their actual source rows are compiled.
          pure ((graph.nodes.find child).getD (alias child))
      put (index.node mode position) equation
    for (definition, position) in numbered index.source.structs do
      put (index.node mode (index.structBase + position)) (← structEquation index mode definition)
    for (definition, position) in numbered index.source.enums do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := enumPhysicalSelection definition uninhabited
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      put (index.node mode (index.enumBase + position)) equation
    for (definition, position) in numbered index.source.closures do
      let equation ← if mode == .shape then closureEquation index position definition
        else pure (Equation.done (.error (.unsupported (.Closure ⟨position⟩))))
      put (index.node mode (index.closureBase + position)) equation
  let tupleSteps : List (Step Unit) := index.source.tupleLayouts.map (fun row =>
    match ((trustIrArrayGet? index.typeRows row.tupleType.index)).join with
    | none => .check fun _ => .error (.missingType row.tupleType.index)
    | some (.Tuple _) => .child (index.node .shape row.tupleType.index) fun _ state => .ok state
    | some _ => .check fun _ => .error (.incoherent "tuple" row.tupleType.index))
  put (globalTuples index) { kind := .unit, initial := .ok (), steps := tupleSteps, finish := fun _ => .ok { size := 0, align := some 1 } }
  let closureSteps : List (Step Unit) := index.source.closureLayouts.map (fun row =>
    if !((trustIrArrayGet? index.closureRows row.closure.index)).isSome then
      .check fun _ => .error (.incoherent "closure" row.closure.index)
    else .child (index.node .shape (index.closureBase + row.closure.index)) fun _ state => .ok state)
  put (globalClosures index) { kind := .unit, initial := .ok (), steps := closureSteps, finish := fun _ => .ok { size := 0, align := some 1 } }

private def TypeRowHistory (index : Index) (mode : Mode) (position : Nat) (ty : Ty) (graph : Graph) : Prop :=
  ∃ before compiled root, ScalarState (globalClosures index + 1) index.source.model.pointerBytes before ∧
    compileTy index mode ty before = (root,compiled) ∧ compiled.Extends graph ∧
    graph.nodes.find (index.node mode position) = some ((compiled.nodes.find root).getD (alias root))

private theorem TypeRowHistory.weaken {index : Index} {mode : Mode} {position : Nat} {ty : Ty}
    {before after : Graph} (history : TypeRowHistory index mode position ty before)
    (retained : before.Extends after) : TypeRowHistory index mode position ty after := by
  obtain ⟨input,compiled,root,valid,run,growth,found⟩ := history
  exact ⟨input,compiled,root,valid,run,growth.trans retained,retained _ _ found⟩

private theorem numbered_at {α : Type} (rows : List α) (position : Nat) (row : α) (declared : Nat)
    (found : (trustIrListGet? (numbered rows) position) = some (row,declared)) :
    (trustIrListGet? rows position) = some row ∧ declared = position := by
  rw [numbered_lookup] at found
  cases original : (trustIrListGet? rows position) with
  | none => rw [original] at found; cases found
  | some value =>
    rw [original] at found
    change some (value,position) = some (row,declared) at found
    cases found
    exact ⟨rfl,rfl⟩

private theorem buildProgram_history (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index)
    (graph : Graph) (state : PreparationState (globalClosures index + 1) index.source.model.pointerBytes 0 graph) :
    PreparationState (globalClosures index + 1) index.source.model.pointerBytes
      (globalClosures index + 1) (buildProgram index facts graph).2 ∧ graph.Extends (buildProgram index facts graph).2 ∧
    ∀ mode position ty, (trustIrListGet? index.source.types position) = some (some ty) →
      TypeRowHistory index mode position ty (buildProgram index facts graph).2 := by
  let lower := globalClosures index + 1
  let pointerBytes := index.source.model.pointerBytes
  let typeBody (mode : Mode) (row : Option Ty × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (entry, position) := row
    let equation ← match entry with
      | none => pure (.done (.error (.missingType position)))
      | some ty => do
        let child ← compileTy index mode ty
        let graph ← get
        pure ((graph.nodes.find child).getD (alias child))
    put (index.node mode position) equation
    pure (.yield ())
  let structBody (mode : Mode) (row : StructDef × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (definition, position) := row
    put (index.node mode (index.structBase + position)) (← structEquation index mode definition)
    pure (.yield ())
  let enumBody (mode : Mode) (row : EnumDef × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (definition, position) := row
    let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
    let selected := enumPhysicalSelection definition uninhabited
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    let equation := enumEquation mode definition uninhabited variants.reverse
    let equation := if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
          Equation.done (.error Error.scalarTarget) else equation
    put (index.node mode (index.enumBase + position)) equation
    pure (.yield ())
  let closureBody (mode : Mode) (row : ClosureTy × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (definition, position) := row
    let equation ← if mode == .shape then closureEquation index position definition
      else pure (Equation.done (.error (.unsupported (.Closure ⟨position⟩))))
    put (index.node mode (index.closureBase + position)) equation
    pure (.yield ())
  let modeBody (mode : Mode) (_ : Unit) : Build (ForInStep Unit) := do
    forIn (numbered index.source.types) () (typeBody mode)
    forIn (numbered index.source.structs) () (structBody mode)
    forIn (numbered index.source.enums) () (enumBody mode)
    forIn (numbered index.source.closures) () (closureBody mode)
    pure (.yield ())
  have node_add : ∀ mode base position, index.node mode base + position = index.node mode (base + position) := by
    intro mode base position
    unfold Index.node
    omega
  have typeStep : ∀ mode position entry, (trustIrListGet? index.source.types position) = some entry →
      PreparationStep lower pointerBytes (index.node mode position) (index.node mode position + 1)
        (typeBody mode (entry,position) ()) := by
    intro mode position entry found
    have inside := reserved_type index ready mode entry position ((numbered_member_iff_get _ _ _).mpr found)
    dsimp only [typeBody]
    cases entry with
    | none =>
      simp only [pure_bind,bind_pure]
      apply PreparationStep.bind (PreparationStep.put lower pointerBytes _ inside _)
      intro unit
      exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
    | some ty =>
      apply PreparationStep.bind (PreparationStep.preserving lower pointerBytes _ _
        (compileTy_scalar_state lower index mode ty) (compileTy_preserves index mode ty)
        (compileTy_keeps_prefix lower index mode ty))
      intro child
      apply PreparationStep.bind (PreparationStep.get lower pointerBytes _)
      intro compiled
      simp only [pure_bind,bind_pure]
      apply PreparationStep.bind (PreparationStep.put lower pointerBytes _ inside _)
      intro unit
      exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
  have structStep : ∀ mode position entry, (trustIrListGet? index.source.structs position) = some entry →
      PreparationStep lower pointerBytes (index.node mode (index.structBase + position))
        (index.node mode (index.structBase + position) + 1) (structBody mode (entry,position) ()) := by
    intro mode position entry found
    have inside := reserved_struct index ready mode entry position ((numbered_member_iff_get _ _ _).mpr found)
    dsimp only [structBody]
    apply PreparationStep.bind (PreparationStep.preserving lower pointerBytes _ _
      (structEquation_scalar_state lower index mode entry) (structEquation_preserves index mode entry)
      (structEquation_keeps_prefix lower index mode entry))
    intro equation
    apply PreparationStep.bind (PreparationStep.put lower pointerBytes _ inside equation)
    intro unit
    exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
  have enumStep : ∀ mode position entry, (trustIrListGet? index.source.enums position) = some entry →
      PreparationStep lower pointerBytes (index.node mode (index.enumBase + position))
        (index.node mode (index.enumBase + position) + 1) (enumBody mode (entry,position) ()) := by
    intro mode position entry found
    have inside := reserved_enum index ready mode entry position ((numbered_member_iff_get _ _ _).mpr found)
    dsimp only [enumBody]
    apply PreparationStep.bind
    · apply PreparationStep.forIn
      intro row member variants
      rcases row with ⟨variant,variantIndex⟩
      repeat first
        | exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
        | (apply PreparationStep.bind (PreparationStep.preserving lower pointerBytes _ _
             (enumNodes_scalar_state lower index mode _ _) (enumNodes_preserves index mode _ _)
             (enumNodes_keeps_prefix lower index mode _ _))
           intro children)
        | (apply PreparationStep.bind (PreparationStep.preserving lower pointerBytes _ _
             (add_scalar_state lower pointerBytes _) (add_preserves _) (KeepsPrefix.add lower _))
           intro child)
        | (simp only [pure_bind,bind_pure])
        | split
    · intro variants
      apply PreparationStep.bind (PreparationStep.put lower pointerBytes _ inside _)
      intro unit
      exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
  have closureStep : ∀ mode position entry, (trustIrListGet? index.source.closures position) = some entry →
      PreparationStep lower pointerBytes (index.node mode (index.closureBase + position))
        (index.node mode (index.closureBase + position) + 1) (closureBody mode (entry,position) ()) := by
    intro mode position entry found
    have inside := reserved_closure index ready mode entry position ((numbered_member_iff_get _ _ _).mpr found)
    dsimp only [closureBody]
    split
    · apply PreparationStep.bind (PreparationStep.preserving lower pointerBytes _ _
        (closureEquation_scalar_state lower index position entry) (closureEquation_preserves index position entry)
        (closureEquation_keeps_prefix lower index position entry))
      intro equation
      apply PreparationStep.bind (PreparationStep.put lower pointerBytes _ inside equation)
      intro unit
      exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
    · simp only [pure_bind,bind_pure]
      apply PreparationStep.bind (PreparationStep.put lower pointerBytes _ inside _)
      intro unit
      exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
  have typeYields : ∀ mode row graph, (typeBody mode row () graph).1 = .yield () := by
    intro mode row graph
    rcases row with ⟨entry,position⟩
    cases entry <;> rfl
  have structYields : ∀ mode row graph, (structBody mode row () graph).1 = .yield () := by
    intro mode row graph
    rcases row with ⟨entry,position⟩
    rfl
  have enumYields : ∀ mode row graph, (enumBody mode row () graph).1 = .yield () := by
    intro mode row graph
    rcases row with ⟨entry,position⟩
    rfl
  have closureYields : ∀ mode row graph, (closureBody mode row () graph).1 = .yield () := by
    intro mode row graph
    rcases row with ⟨entry,position⟩
    dsimp only [closureBody]
    split <;> rfl
  have typeLoop : ∀ mode, PreparationStep lower pointerBytes (index.node mode 0)
      (index.node mode index.structBase) (forIn (numbered index.source.types) () (typeBody mode)) := by
    intro mode
    have stop : index.node mode index.structBase = index.node mode 0 + (numbered index.source.types).length := by
      rw [numbered_metadata_length]
      simp only [Index.node,Index.structBase,Index.enumBase,Index.closureBase,Index.count]
      have size := ready.types
      omega
    rw [stop]
    apply PreparationStep.forIn_ordered lower pointerBytes _ _ _ (typeYields mode)
    intro position row found
    rcases row with ⟨entry,declared⟩
    obtain ⟨original,same⟩ := numbered_at index.source.types position entry declared found
    subst declared
    have atRow := typeStep mode position entry original
    simpa only [node_add,Nat.zero_add] using atRow
  have structLoop : ∀ mode, PreparationStep lower pointerBytes (index.node mode index.structBase)
      (index.node mode index.enumBase) (forIn (numbered index.source.structs) () (structBody mode)) := by
    intro mode
    have stop : index.node mode index.enumBase = index.node mode index.structBase + (numbered index.source.structs).length := by
      rw [numbered_metadata_length]
      simp only [Index.node,Index.structBase,Index.enumBase,Index.closureBase,Index.count]
      have size := ready.structs
      omega
    rw [stop]
    apply PreparationStep.forIn_ordered lower pointerBytes _ _ _ (structYields mode)
    intro position row found
    rcases row with ⟨entry,declared⟩
    obtain ⟨original,same⟩ := numbered_at index.source.structs position entry declared found
    subst declared
    have atRow := structStep mode position entry original
    simpa only [node_add,Nat.zero_add] using atRow
  have enumLoop : ∀ mode, PreparationStep lower pointerBytes (index.node mode index.enumBase)
      (index.node mode index.closureBase) (forIn (numbered index.source.enums) () (enumBody mode)) := by
    intro mode
    have stop : index.node mode index.closureBase = index.node mode index.enumBase + (numbered index.source.enums).length := by
      rw [numbered_metadata_length]
      simp only [Index.node,Index.structBase,Index.enumBase,Index.closureBase,Index.count]
      have size := ready.enums
      omega
    rw [stop]
    apply PreparationStep.forIn_ordered lower pointerBytes _ _ _ (enumYields mode)
    intro position row found
    rcases row with ⟨entry,declared⟩
    obtain ⟨original,same⟩ := numbered_at index.source.enums position entry declared found
    subst declared
    have atRow := enumStep mode position entry original
    simpa only [node_add,Nat.zero_add] using atRow
  have closureLoop : ∀ mode, PreparationStep lower pointerBytes (index.node mode index.closureBase)
      (index.node mode index.count) (forIn (numbered index.source.closures) () (closureBody mode)) := by
    intro mode
    have stop : index.node mode index.count = index.node mode index.closureBase + (numbered index.source.closures).length := by
      rw [numbered_metadata_length]
      simp only [Index.node,Index.structBase,Index.enumBase,Index.closureBase,Index.count]
      have size := ready.closures
      omega
    rw [stop]
    apply PreparationStep.forIn_ordered lower pointerBytes _ _ _ (closureYields mode)
    intro position row found
    rcases row with ⟨entry,declared⟩
    obtain ⟨original,same⟩ := numbered_at index.source.closures position entry declared found
    subst declared
    have atRow := closureStep mode position entry original
    simpa only [node_add,Nat.zero_add] using atRow
  have modeStep : ∀ mode, PreparationStep lower pointerBytes (index.node mode 0)
      (index.node mode index.count) (modeBody mode ()) := by
    intro mode
    dsimp only [modeBody]
    apply PreparationStep.bind (typeLoop mode)
    intro unit
    apply PreparationStep.bind (structLoop mode)
    intro unit
    apply PreparationStep.bind (enumLoop mode)
    intro unit
    apply PreparationStep.bind (closureLoop mode)
    intro unit
    exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
  have typeOrigin : ∀ mode position ty, (trustIrListGet? index.source.types position) = some (some ty) →
      ∀ input, PreparationState lower pointerBytes (index.node mode position) input →
      TypeRowHistory index mode position ty (typeBody mode (some ty,position) () input).2 := by
    intro mode position ty found input valid
    have inside := reserved_type index ready mode (some ty) position ((numbered_member_iff_get _ _ _).mpr found)
    have compiledState := PreparationStep.preserving lower pointerBytes (index.node mode position) _
      (compileTy_scalar_state lower index mode ty) (compileTy_preserves index mode ty)
      (compileTy_keeps_prefix lower index mode ty) input valid
    cases run : compileTy index mode ty input with
    | mk root compiled =>
      rw [run] at compiledState
      let equation := (compiled.nodes.find root).getD (alias root)
      have installed := PreparationStep.put lower pointerBytes (index.node mode position) inside equation compiled compiledState.1
      refine ⟨input,compiled,root,valid.1,run,?_,?_⟩
      · simpa only [typeBody,Bind.bind,StateT.bind,Pure.pure,StateT.pure,run] using installed.2
      · simp only [typeBody,Bind.bind,StateT.bind,Pure.pure,StateT.pure,run]
        change (compiled.nodes.insert (index.node mode position) equation).find (index.node mode position) = some equation
        rw [NatIndexTree.find_insert,if_pos rfl]
  have modeOrigin : ∀ mode input, PreparationState lower pointerBytes (index.node mode 0) input →
      ∀ position ty, (trustIrListGet? index.source.types position) = some (some ty) →
      TypeRowHistory index mode position ty (modeBody mode () input).2 := by
    intro mode input valid position ty found
    let suffix : Build (ForInStep Unit) := do
      forIn (numbered index.source.structs) () (structBody mode)
      forIn (numbered index.source.enums) () (enumBody mode)
      forIn (numbered index.source.closures) () (closureBody mode)
      pure (.yield ())
    have suffixStep : PreparationStep lower pointerBytes (index.node mode index.structBase)
        (index.node mode index.count) suffix := by
      apply PreparationStep.bind (structLoop mode)
      intro unit
      apply PreparationStep.bind (enumLoop mode)
      intro unit
      apply PreparationStep.bind (closureLoop mode)
      intro unit
      exact fun graph state => ⟨state,Graph.Extends.refl graph⟩
    have numberedFound : (trustIrListGet? (numbered index.source.types) position) = some (some ty,position) := by
      rw [numbered_lookup,found]
      rfl
    have rowSteps : ∀ i row, (trustIrListGet? (numbered index.source.types) i) = some row →
        PreparationStep lower pointerBytes (index.node mode 0 + i) (index.node mode 0 + i + 1) (typeBody mode row ()) := by
      intro i row original
      rcases row with ⟨entry,declared⟩
      obtain ⟨atSource,same⟩ := numbered_at index.source.types i entry declared original
      subst declared
      simpa only [node_add,Nat.zero_add] using typeStep mode i entry atSource
    obtain ⟨before,after,atRow,ran,retained⟩ := PreparationStep.forIn_visit lower pointerBytes (index.node mode 0)
      (numbered index.source.types) (typeBody mode) (typeYields mode) rowSteps position (some ty,position) numberedFound input valid
    have origin := typeOrigin mode position ty found before (by simpa only [node_add,Nat.zero_add] using atRow)
    rw [ran] at origin
    have typeState := typeLoop mode input valid
    have later := suffixStep _ typeState.1
    have finalOrigin := origin.weaken (retained.trans later.2)
    simpa only [modeBody,suffix,Bind.bind,StateT.bind,Pure.pure,StateT.pure] using finalOrigin
  have modeYields : ∀ mode input, (modeBody mode () input).1 = .yield () := by
    intro mode input
    rfl
  have shapeStep : PreparationStep lower pointerBytes 0 index.count (modeBody .shape ()) := by
    simpa only [Index.node,show (Mode.shape == Mode.shape) = true from rfl,ite_true,Nat.zero_add,Nat.add_zero] using modeStep .shape
  have executionStep : PreparationStep lower pointerBytes index.count (2 * index.count) (modeBody .execution ()) := by
    simpa only [Index.node,Bool.false_eq_true,ite_false,Nat.add_zero,Nat.two_mul] using modeStep .execution
  have modesStep : PreparationStep lower pointerBytes 0 (2 * index.count)
      (forIn [Mode.shape,Mode.execution] () modeBody) := by
    intro input valid
    have first := shapeStep input valid
    have second := executionStep _ first.1
    have y1 := modeYields .shape input
    cases r1 : modeBody .shape () input with
    | mk out1 after1 =>
      rw [r1] at y1
      cases y1
      rw [r1] at second first
      have y2 := modeYields .execution after1
      cases r2 : modeBody .execution () after1 with
      | mk out2 after2 =>
        rw [r2] at y2
        cases y2
        simpa only [List.forIn_cons,List.forIn_nil,Bind.bind,StateT.bind,Pure.pure,StateT.pure,r1,r2] using
          And.intro second.1 (first.2.trans second.2)
  let tupleSteps : List (Step Unit) := index.source.tupleLayouts.map (fun row =>
    match ((trustIrArrayGet? index.typeRows row.tupleType.index)).join with
    | none => .check fun _ => .error (.missingType row.tupleType.index)
    | some (.Tuple _) => .child (index.node .shape row.tupleType.index) fun _ state => .ok state
    | some _ => .check fun _ => .error (.incoherent "tuple" row.tupleType.index))
  let closureSteps : List (Step Unit) := index.source.closureLayouts.map (fun row =>
    if !((trustIrArrayGet? index.closureRows row.closure.index)).isSome then
      .check fun _ => .error (.incoherent "closure" row.closure.index)
    else .child (index.node .shape (index.closureBase + row.closure.index)) fun _ state => .ok state)
  let validators : Build Unit := do
    put (globalTuples index) { kind := .unit, initial := .ok (), steps := tupleSteps, finish := fun _ => .ok { size := 0, align := some 1 } }
    put (globalClosures index) { kind := .unit, initial := .ok (), steps := closureSteps, finish := fun _ => .ok { size := 0, align := some 1 } }
  have validatorStep : PreparationStep lower pointerBytes (2 * index.count) lower validators := by
    apply PreparationStep.bind (PreparationStep.put lower pointerBytes (globalTuples index) (by dsimp [lower,globalTuples,globalClosures]; omega) _)
    intro unit
    exact PreparationStep.put lower pointerBytes (globalClosures index) (by dsimp [lower]; omega) _
  have assembled : buildProgram index facts = (do
      forIn [Mode.shape,Mode.execution] () modeBody
      validators) := rfl
  have whole : PreparationStep lower pointerBytes 0 lower (buildProgram index facts) := by
    rw [assembled]
    apply PreparationStep.bind modesStep
    intro unit
    exact validatorStep
  have finished := whole graph state
  refine ⟨finished.1,finished.2,?_⟩
  intro mode position ty found
  have modes := modesStep graph state
  have later := validatorStep _ modes.1
  have origin : TypeRowHistory index mode position ty (forIn [Mode.shape,Mode.execution] () modeBody graph).2 := by
    cases mode with
    | shape =>
      have first := shapeStep graph state
      have second := executionStep _ first.1
      have raw := modeOrigin .shape graph (by simpa only [Index.node,show (Mode.shape == Mode.shape) = true from rfl,ite_true,Nat.zero_add,Nat.add_zero] using state) position ty found
      have transported := raw.weaken second.2
      simpa only [List.forIn_cons,List.forIn_nil,Bind.bind,StateT.bind,Pure.pure,StateT.pure,modeYields] using transported
    | execution =>
      have first := shapeStep graph state
      have raw := modeOrigin .execution _ (by simpa only [Index.node,Bool.false_eq_true,ite_false,Nat.add_zero] using first.1) position ty found
      simpa only [List.forIn_cons,List.forIn_nil,Bind.bind,StateT.bind,Pure.pure,StateT.pure,modeYields] using raw
  have transported := origin.weaken later.2
  simpa only [assembled,Bind.bind,StateT.bind] using transported

private def build (index : Index) (facts : NatIndexTree Unit) : Graph :=
  (buildProgram index facts { count := globalClosures index + 1 }).2

private theorem build_eq_original (index : Index) (facts : NatIndexTree Unit) :
    build index facts = Id.run do
  let initial : Graph := { count := globalClosures index + 1 }
  let program : Build Unit := do
    for mode in [Mode.shape, Mode.execution] do
      for (entry, position) in numbered index.source.types do
        let equation ← match entry with
          | none => pure (.done (.error (.missingType position)))
          | some ty => do
            let child ← compileTy index mode ty
            let graph ← get
            -- Copy a compiled root equation rather than adding an alias
            -- frame for each type-table link. Forward nominal references
            -- remain aliases until their actual source rows are compiled.
            pure ((graph.nodes.find child).getD (alias child))
        put (index.node mode position) equation
      for (definition, position) in numbered index.source.structs do
        put (index.node mode (index.structBase + position)) (← structEquation index mode definition)
      for (definition, position) in numbered index.source.enums do
        let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
        let selected := match definition.layout with
          | some descriptor => match descriptor.encoding with
            | .singleInhabited selected =>
              if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
            | _ => none
          | none => none
        let mut variants := []
        for (variant, variantIndex) in numbered definition.variants do
          -- Skip physical children only after checking the actual structural
          -- facts and all inactive offset rows. Logical rows retain their IDs.
          let children ← if selected.any (fun active => variantIndex != active) then pure []
            else enumNodes index mode definition.layout.isSome variant.fields
          let equation := match definition.layout with
            | none => canonicalFields mode "enum" definition.id.index children
            | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
              | none => Equation.done (.error (.incoherent "enum" definition.id.index))
              | some offsets =>
                if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
                else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                  (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
          variants := (← add equation) :: variants
        let equation := enumEquation mode definition uninhabited variants.reverse
        let equation := if mode == .shape && !index.source.canonicalScalars &&
            (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
              Equation.done (.error Error.scalarTarget) else equation
        put (index.node mode (index.enumBase + position)) equation
      for (definition, position) in numbered index.source.closures do
        let equation ← if mode == .shape then closureEquation index position definition
          else pure (Equation.done (.error (.unsupported (.Closure ⟨position⟩))))
        put (index.node mode (index.closureBase + position)) equation
    let tupleSteps : List (Step Unit) := index.source.tupleLayouts.map (fun row =>
      match ((trustIrArrayGet? index.typeRows row.tupleType.index)).join with
      | none => .check fun _ => .error (.missingType row.tupleType.index)
      | some (.Tuple _) => .child (index.node .shape row.tupleType.index) fun _ state => .ok state
      | some _ => .check fun _ => .error (.incoherent "tuple" row.tupleType.index))
    put (globalTuples index) { kind := .unit, initial := .ok (), steps := tupleSteps, finish := fun _ => .ok { size := 0, align := some 1 } }
    let closureSteps : List (Step Unit) := index.source.closureLayouts.map (fun row =>
      if !((trustIrArrayGet? index.closureRows row.closure.index)).isSome then
        .check fun _ => .error (.incoherent "closure" row.closure.index)
      else .child (index.node .shape (index.closureBase + row.closure.index)) fun _ state => .ok state)
    put (globalClosures index) { kind := .unit, initial := .ok (), steps := closureSteps, finish := fun _ => .ok { size := 0, align := some 1 } }
  let (_, graph) := program initial
  return graph := by
  unfold build buildProgram
  rfl


private theorem build_reserved (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    (build index facts).Bounded ∧ globalClosures index + 1 ≤ (build index facts).count := by
  let reserved := globalClosures index + 1
  have program : PreservesState (fun graph => graph.Bounded ∧ reserved ≤ graph.count)
      (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        have inside := reserved_type index ready mode entry position member
        cases entry with
        | none =>
          apply PreservesState.bind (put_reserved reserved _ inside _)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          apply PreservesState.bind ((compileTy_preserves index mode ty).reserved reserved)
          intro child
          apply PreservesState.bind (PreservesState.get (fun graph => graph.Bounded ∧ reserved ≤ graph.count))
          intro graph
          apply PreservesState.bind (put_reserved reserved _ inside _)
          intro unit
          exact PreservesState.pure _ _
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          have inside := reserved_struct index ready mode definition position member
          apply PreservesState.bind ((structEquation_preserves index mode definition).reserved reserved)
          intro equation
          apply PreservesState.bind (put_reserved reserved _ inside equation)
          intro unit
          exact PreservesState.pure _ _
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            have inside := reserved_enum index ready mode definition position member
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row variantMember variants
              rcases row with ⟨variant, variantIndex⟩
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind ((enumNodes_preserves _ _ _ _).reserved reserved)
                   intro children)
                | (apply PreservesState.bind ((add_preserves _).reserved reserved)
                   intro node)
                | (simp only [pure_bind])
                | split
            · intro variants
              apply PreservesState.bind (put_reserved reserved _ inside _)
              intro unit
              exact PreservesState.pure _ _
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              have inside := reserved_closure index ready mode definition position member
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind ((closureEquation_preserves _ _ _).reserved reserved)
                   intro equation)
                | (apply PreservesState.bind (put_reserved reserved _ inside _)
                   intro unit)
                | split
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      have tupleInside : globalTuples index < reserved := by
        dsimp [reserved, globalClosures, globalTuples]
        omega
      have closureInside : globalClosures index < reserved := Nat.lt_succ_self _
      apply PreservesState.bind (put_reserved reserved _ tupleInside _)
      intro unit
      exact put_reserved reserved _ closureInside _
  exact program { count := reserved } ⟨Graph.Bounded.empty reserved, Nat.le_refl _⟩

private theorem build_scalars (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    (build index facts).ScalarInvariant (globalClosures index + 1) index.source.model.pointerBytes := by
  let reserved := globalClosures index + 1
  have program : PreservesState (ScalarState reserved index.source.model.pointerBytes)
      (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        have inside := reserved_type index ready mode entry position member
        cases entry with
        | none =>
          apply PreservesState.bind (put_scalar_state reserved index.source.model.pointerBytes _ inside _)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          apply PreservesState.bind (compileTy_scalar_state reserved index mode ty)
          intro child
          apply PreservesState.bind (PreservesState.get (ScalarState reserved index.source.model.pointerBytes))
          intro graph
          apply PreservesState.bind (put_scalar_state reserved index.source.model.pointerBytes _ inside _)
          intro unit
          exact PreservesState.pure _ _
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          have inside := reserved_struct index ready mode definition position member
          apply PreservesState.bind (structEquation_scalar_state reserved index mode definition)
          intro equation
          apply PreservesState.bind (put_scalar_state reserved index.source.model.pointerBytes _ inside equation)
          intro unit
          exact PreservesState.pure _ _
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            have inside := reserved_enum index ready mode definition position member
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row variantMember variants
              rcases row with ⟨variant, variantIndex⟩
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind (enumNodes_scalar_state reserved _ _ _ _)
                   intro children)
                | (apply PreservesState.bind (add_scalar_state reserved _ _)
                   intro node)
                | (simp only [pure_bind])
                | split
            · intro variants
              apply PreservesState.bind (put_scalar_state reserved index.source.model.pointerBytes _ inside _)
              intro unit
              exact PreservesState.pure _ _
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              have inside := reserved_closure index ready mode definition position member
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind (closureEquation_scalar_state reserved _ _ _)
                   intro equation)
                | (apply PreservesState.bind (put_scalar_state reserved index.source.model.pointerBytes _ inside _)
                   intro unit)
                | split
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      have tupleInside : globalTuples index < reserved := by
        dsimp [reserved, globalClosures, globalTuples]
        omega
      have closureInside : globalClosures index < reserved := Nat.lt_succ_self _
      apply PreservesState.bind (put_scalar_state reserved index.source.model.pointerBytes _ tupleInside _)
      intro unit
      exact put_scalar_state reserved index.source.model.pointerBytes _ closureInside _
  exact (program { count := reserved }
    ⟨Graph.Bounded.empty reserved, Nat.le_refl _, Graph.ScalarInvariant.empty _ _ _⟩).2.2

private theorem build_word (index : Index) (facts : NatIndexTree Unit) :
    (build index facts).WordInvariant := by
  have program : PreservesState Graph.WordInvariant (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_word _ _ (Equation.WordGuarded.failed _).rule)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsEquation.install_yield (index.node mode position) _
            (BuildsEquation.bind (compileTy_word index mode ty) (fun child => copyRoot_word child))
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          exact BuildsEquation.install_yield (index.node mode (index.structBase + position)) _
            (structEquation_word index mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row variantMember variants
              rcases row with ⟨variant, variantIndex⟩
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind (enumNodes_word _ _ _ _); intro children)
                | (apply PreservesState.bind
                     (add_word _ (variantEquation_word mode definition _ variantIndex).rule); intro node)
                | (simp only [pure_bind])
                | split
            · intro variants
              apply PreservesState.bind (put_word (index.node mode (index.enumBase + position)) _
                (enumRoot_word index mode definition _ _).rule)
              intro unit
              exact PreservesState.pure _ _
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              split
              · exact BuildsEquation.install_yield (index.node mode (index.closureBase + position)) _
                  (closureEquation_word index position definition)
              · apply PreservesState.bind (put_word _ _ (Equation.WordGuarded.failed _).rule)
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      apply PreservesState.bind (put_word _ _ (Equation.WordGuarded.unit _).rule)
      intro unit
      exact put_word _ _ (Equation.WordGuarded.unit _).rule
  exact program _ (Graph.SummaryInvariant.empty _ _)

private theorem build_modes (index : Index) (facts : NatIndexTree Unit)
    (ready : IndexReady index) (shape : ShapeReady index) : ModeState index (build index facts) := by
  have program : PreservesState (ModeState index) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        have inside := reserved_type index ready mode entry position member
        have assigned := type_mode index ready mode entry position member
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_mode_state index _ inside _
            ((Equation.ModeGuarded.failed (index.nodeMode _) _).indexed index.nodeMode _ rfl))
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsIndexedEquation.install_yield index _ inside _
            (compileCopy_mode index shape mode ty _ assigned)
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          have inside := reserved_struct index ready mode definition position member
          have assigned := struct_mode index ready mode definition position member
          exact BuildsIndexedEquation.install_yield index _ inside _
            (BuildsIndexedEquation.guarded index _ mode _ (structEquation_mode_state index mode definition)
              (structEquation_mode index mode definition) assigned)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            have inside := reserved_enum index ready mode definition position member
            have assigned := enum_mode index ready mode definition position member
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row variantMember variants
              rcases row with ⟨variant, variantIndex⟩
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind (enumNodes_mode_state index mode _ _); intro children)
                | (apply PreservesState.bind
                     (add_mode_state index _ (variantEquation_mode mode definition _ variantIndex).execution); intro node)
                | (simp only [pure_bind])
                | split
            · intro variants
              apply PreservesState.bind (put_mode_state index _ inside _
                ((enumRoot_mode index mode definition _ _).indexed index.nodeMode _ assigned))
              intro unit
              exact PreservesState.pure _ _
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              have inside := reserved_closure index ready mode definition position member
              have assigned := closure_mode index ready mode definition position member
              split
              · rename_i selected
                have sameMode : mode = .shape := by
                  cases mode with
                  | shape => rfl
                  | execution => cases selected
                have assignedShape := assigned.trans sameMode
                exact BuildsIndexedEquation.install_yield index _ inside _
                  (BuildsIndexedEquation.guarded index _ .shape _
                    (closureEquation_mode_state index position definition)
                    (closureEquation_mode index position definition) assignedShape)
              · apply PreservesState.bind (put_mode_state index _ inside _
                  ((Equation.ModeGuarded.failed (index.nodeMode _) _).indexed index.nodeMode _ rfl))
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      have tupleInside : globalTuples index < 2 * index.count + 2 := by unfold globalTuples; omega
      have closureInside : globalClosures index < 2 * index.count + 2 := by
        unfold globalClosures globalTuples; omega
      apply PreservesState.bind (put_mode_state index _ tupleInside _
        ((Equation.ModeGuarded.unit (index.nodeMode _) _).indexed index.nodeMode _ rfl))
      intro unit
      exact put_mode_state index _ closureInside _
        ((Equation.ModeGuarded.unit (index.nodeMode _) _).indexed index.nodeMode _ rfl)
  exact program { count := globalClosures index + 1 }
    ⟨⟨Graph.Bounded.empty _, Nat.le_refl _, Graph.ScalarInvariant.empty _ _ _⟩,
      Graph.IndexedInvariant.empty _ _⟩

/-- A prepared service shares source equations and successful query results.
    Neither preparing nor querying reads any executable program context. -/
structure Session where
  index : Index
  graph : Graph
  memo : Memo := .empty
  /-- Only checked successful roots enter this cache. Exact type equality is
      checked after the bounded bucket lookup, in both layout modes. -/
  roots : NatIndexTree (List (Ty × Mode × Nat)) := .empty

/-- The production bucket is only an index; full type/mode equality still
controls reuse within its collision list. -/
def rootBucket (mode : Mode) (ty : Ty) : Nat :=
  2 * typeBucket ty + (if mode == .shape then 0 else 1)

/-- A logical witness of the actual structural compiler run. -/
def RootCompilation (index : Index) (mode : Mode) (ty : Ty)
    (before : Graph) (root : Nat) (after : Graph) : Prop :=
  compileTy index mode ty before = (root, after)

/-- The exact ordered child-list compilation used by fields and tuples.
Repeated roots are allowed because scalar interning does not preserve type identity. -/
def TypesCompilation (index : Index) (mode : Mode) (types : List Ty)
    (before : Graph) (roots : List Nat) (after : Graph) : Prop :=
  compileTypes index mode types before = (roots,after)

/-- Compare actual compiler outputs inside later graphs that retain their
original equations. Reserved forward references may be filled in those graphs. -/
theorem RootCompilation.corresponds_in_extensions {source : Environment} {mode : Mode} {ty : Ty}
    {left right leftAfter rightAfter leftAmbient rightAmbient : Graph} {first second : Nat}
    {relation : Nat → Nat → Prop}
    (leftRun : RootCompilation (Index.ofEnvironment source) mode ty left first leftAfter)
    (rightRun : RootCompilation (Index.ofEnvironment source) mode ty right second rightAfter)
    (leftBounded : left.Bounded) (leftFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ left.count)
    (leftScalars : left.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (rightBounded : right.Bounded) (rightFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ right.count)
    (rightScalars : right.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (leftRetained : leftAfter.Extends leftAmbient) (rightRetained : rightAfter.Extends rightAmbient)
    (paired : leftAmbient.Correspondence rightAmbient relation)
    (original : ∀ node, node < 2 * (Index.ofEnvironment source).count + 2 → relation node node) :
    ∃ next, (∀ a b, relation a b → next a b) ∧ leftAmbient.Correspondence rightAmbient next ∧ next first second := by
  change compileTy (Index.ofEnvironment source) mode ty left = (first,leftAfter) at leftRun
  change compileTy (Index.ofEnvironment source) mode ty right = (second,rightAfter) at rightRun
  have leftGrowth : (compileTy (Index.ofEnvironment source) mode ty left).2.Extends leftAmbient := by
    rw [leftRun]; exact leftRetained
  have rightGrowth : (compileTy (Index.ofEnvironment source) mode ty right).2.Extends rightAmbient := by
    rw [rightRun]; exact rightRetained
  have result := compileTy_related (Index.ofEnvironment source) (rootReady source) mode ty
    left right leftAmbient rightAmbient relation
    ⟨leftBounded,leftFrontier,leftScalars⟩ ⟨rightBounded,rightFrontier,rightScalars⟩
    leftGrowth rightGrowth paired original
  rw [leftRun,rightRun] at result
  exact result

/-- Ordinary output correspondence is the special case with no later fills. -/
theorem RootCompilation.corresponds {source : Environment} {mode : Mode} {ty : Ty}
    {left right leftAfter rightAfter : Graph} {first second : Nat} {relation : Nat → Nat → Prop}
    (leftRun : RootCompilation (Index.ofEnvironment source) mode ty left first leftAfter)
    (rightRun : RootCompilation (Index.ofEnvironment source) mode ty right second rightAfter)
    (leftBounded : left.Bounded) (leftFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ left.count)
    (leftScalars : left.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (rightBounded : right.Bounded) (rightFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ right.count)
    (rightScalars : right.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (paired : left.Correspondence right relation)
    (original : ∀ node, node < 2 * (Index.ofEnvironment source).count + 2 → relation node node) :
    ∃ next, (∀ a b, relation a b → next a b) ∧ leftAfter.Correspondence rightAfter next ∧ next first second := by
  have leftGrowth := (compileTy_preserves (Index.ofEnvironment source) mode ty left leftBounded).equations
  have rightGrowth := (compileTy_preserves (Index.ofEnvironment source) mode ty right rightBounded).equations
  rw [show compileTy (Index.ofEnvironment source) mode ty left = (first,leftAfter) from leftRun] at leftGrowth
  rw [show compileTy (Index.ofEnvironment source) mode ty right = (second,rightAfter) from rightRun] at rightGrowth
  exact leftRun.corresponds_in_extensions rightRun leftBounded leftFrontier leftScalars
    rightBounded rightFrontier rightScalars (Graph.Extends.refl leftAfter) (Graph.Extends.refl rightAfter)
    (paired.grow leftGrowth rightGrowth) original

/-- Compare actual compiler outputs inside later graphs that retain their
original equations. Reserved forward references may be filled in those graphs. -/
theorem TypesCompilation.corresponds_in_extensions {source : Environment} {mode : Mode} {types : List Ty}
    {left right leftAfter rightAfter leftAmbient rightAmbient : Graph} {first second : List Nat}
    {relation : Nat → Nat → Prop}
    (leftRun : TypesCompilation (Index.ofEnvironment source) mode types left first leftAfter)
    (rightRun : TypesCompilation (Index.ofEnvironment source) mode types right second rightAfter)
    (leftBounded : left.Bounded) (leftFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ left.count)
    (leftScalars : left.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (rightBounded : right.Bounded) (rightFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ right.count)
    (rightScalars : right.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (leftRetained : leftAfter.Extends leftAmbient) (rightRetained : rightAfter.Extends rightAmbient)
    (paired : leftAmbient.Correspondence rightAmbient relation)
    (original : ∀ node, node < 2 * (Index.ofEnvironment source).count + 2 → relation node node) :
    ∃ next, (∀ a b, relation a b → next a b) ∧ leftAmbient.Correspondence rightAmbient next ∧ RowsCorrespond next first second := by
  change compileTypes (Index.ofEnvironment source) mode types left = (first,leftAfter) at leftRun
  change compileTypes (Index.ofEnvironment source) mode types right = (second,rightAfter) at rightRun
  have leftGrowth : (compileTypes (Index.ofEnvironment source) mode types left).2.Extends leftAmbient := by
    rw [leftRun]; exact leftRetained
  have rightGrowth : (compileTypes (Index.ofEnvironment source) mode types right).2.Extends rightAmbient := by
    rw [rightRun]; exact rightRetained
  have result := compileTypes_related (Index.ofEnvironment source) (rootReady source) mode types
    left right leftAmbient rightAmbient relation
    ⟨leftBounded,leftFrontier,leftScalars⟩ ⟨rightBounded,rightFrontier,rightScalars⟩
    leftGrowth rightGrowth paired original
  rw [leftRun,rightRun] at result
  exact result

/-- Ordinary output correspondence is the special case with no later fills. -/
theorem TypesCompilation.corresponds {source : Environment} {mode : Mode} {types : List Ty}
    {left right leftAfter rightAfter : Graph} {first second : List Nat} {relation : Nat → Nat → Prop}
    (leftRun : TypesCompilation (Index.ofEnvironment source) mode types left first leftAfter)
    (rightRun : TypesCompilation (Index.ofEnvironment source) mode types right second rightAfter)
    (leftBounded : left.Bounded) (leftFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ left.count)
    (leftScalars : left.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (rightBounded : right.Bounded) (rightFrontier : 2 * (Index.ofEnvironment source).count + 2 ≤ right.count)
    (rightScalars : right.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (paired : left.Correspondence right relation)
    (original : ∀ node, node < 2 * (Index.ofEnvironment source).count + 2 → relation node node) :
    ∃ next, (∀ a b, relation a b → next a b) ∧ leftAfter.Correspondence rightAfter next ∧ RowsCorrespond next first second := by
  have leftGrowth := (compileTypes_preserves (Index.ofEnvironment source) mode types left leftBounded).equations
  have rightGrowth := (compileTypes_preserves (Index.ofEnvironment source) mode types right rightBounded).equations
  rw [show compileTypes (Index.ofEnvironment source) mode types left = (first,leftAfter) from leftRun] at leftGrowth
  rw [show compileTypes (Index.ofEnvironment source) mode types right = (second,rightAfter) from rightRun] at rightGrowth
  exact leftRun.corresponds_in_extensions rightRun leftBounded leftFrontier leftScalars
    rightBounded rightFrontier rightScalars (Graph.Extends.refl leftAfter) (Graph.Extends.refl rightAfter)
    (paired.grow leftGrowth rightGrowth) original

/-- Reserved lookup values, including missing forward-reference holes, are
unchanged by the actual typed compiler. -/
theorem RootCompilation.preserves_reserved {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root lower : Nat} (compiled : RootCompilation index mode ty before root after)
    (bounded : before.Bounded) (frontier : lower ≤ before.count) :
    ∀ node, node < lower → after.nodes.find node = before.nodes.find node := by
  have result := compileTy_keeps_prefix lower index mode ty before bounded frontier
  change compileTy index mode ty before = (root,after) at compiled
  rw [compiled] at result
  exact result

theorem TypesCompilation.preserves_reserved {index : Index} {mode : Mode} {types : List Ty}
    {before after : Graph} {roots : List Nat} {lower : Nat}
    (compiled : TypesCompilation index mode types before roots after)
    (bounded : before.Bounded) (frontier : lower ≤ before.count) :
    ∀ node, node < lower → after.nodes.find node = before.nodes.find node := by
  have result := compileTypes_keeps_prefix lower index mode types before bounded frontier
  change compileTypes index mode types before = (roots,after) at compiled
  rw [compiled] at result
  exact result

/-- Compilation retains installed nodes and fills every newly allocated slot;
this assertion concerns presence and makes no claim about equation equality. -/
theorem RootCompilation.domain_covers {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat}
    (compiled : RootCompilation index mode ty before root after) : before.DomainCovers after := by
  have covered := compileTy_covers index mode ty before
  change compileTy index mode ty before = (root,after) at compiled
  rw [compiled] at covered
  exact covered

theorem TypesCompilation.domain_covers {index : Index} {mode : Mode} {types : List Ty}
    {before after : Graph} {roots : List Nat}
    (compiled : TypesCompilation index mode types before roots after) : before.DomainCovers after := by
  have covered := compileTypes_covers index mode types before
  change compileTypes index mode types before = (roots,after) at compiled
  rw [compiled] at covered
  exact covered

theorem RootCompilation.preserves_complete {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat}
    (compiled : RootCompilation index mode ty before root after) (complete : before.Complete) : after.Complete :=
  compiled.domain_covers.complete complete

theorem TypesCompilation.preserves_complete {index : Index} {mode : Mode} {types : List Ty}
    {before after : Graph} {roots : List Nat}
    (compiled : TypesCompilation index mode types before roots after) (complete : before.Complete) : after.Complete :=
  compiled.domain_covers.complete complete

/-- Earlier compiled children remain below the final frontier after every
later child compilation, including repeated cache hits and checked failures. -/
theorem TypesCompilation.roots_bound {source : Environment} {mode : Mode} {types : List Ty}
    {before after : Graph} {roots : List Nat}
    (compiled : TypesCompilation (Index.ofEnvironment source) mode types before roots after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes) :
    ∀ root ∈ roots, root < after.count := by
  have result := compileTypes_roots_bound (Index.ofEnvironment source) (rootReady source) mode types before
    ⟨bounded,frontier,scalars⟩
  change compileTypes (Index.ofEnvironment source) mode types before = (roots,after) at compiled
  rw [compiled] at result
  exact result

/-- Typed compilation preserves reference bounds for every installed
old and new equation, including reserved references to not-yet-installed rows. -/
theorem RootCompilation.preserves_references {source : Environment} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat}
    (compiled : RootCompilation (Index.ofEnvironment source) mode ty before root after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (references : before.ReferenceBounds) : after.ReferenceBounds := by
  have result := compileTy_reference_state (Index.ofEnvironment source) (rootReady source) mode ty before
    ⟨⟨bounded,frontier,scalars⟩,references⟩
  change compileTy (Index.ofEnvironment source) mode ty before = (root,after) at compiled
  rw [compiled] at result
  exact result.2

theorem TypesCompilation.preserves_references {source : Environment} {mode : Mode} {types : List Ty}
    {before after : Graph} {roots : List Nat}
    (compiled : TypesCompilation (Index.ofEnvironment source) mode types before roots after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (references : before.ReferenceBounds) : after.ReferenceBounds := by
  have result := compileTypes_reference_state (Index.ofEnvironment source) (rootReady source) mode types before
    ⟨⟨bounded,frontier,scalars⟩,references⟩
  change compileTypes (Index.ofEnvironment source) mode types before = (roots,after) at compiled
  rw [compiled] at result
  exact result.2

theorem StructCompilation.references {source : Environment} {mode : Mode} {definition : StructDef}
    {before after : Graph} {equation : Equation}
    (compiled : StructCompilation (Index.ofEnvironment source) mode definition before equation after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (references : before.ReferenceBounds) :
    after.ReferenceBounds ∧ StepsIn (fun child => child < after.count) equation.steps := by
  have result := structEquation_reference (Index.ofEnvironment source) (rootReady source) mode definition before
    ⟨⟨bounded,frontier,scalars⟩,references⟩
  change structEquation (Index.ofEnvironment source) mode definition before = (equation,after) at compiled
  rw [compiled] at result
  exact ⟨result.1.2,result.2⟩

theorem ClosureCompilation.references {source : Environment} {position : Nat} {definition : ClosureTy}
    {before after : Graph} {equation : Equation}
    (compiled : ClosureCompilation (Index.ofEnvironment source) position definition before equation after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (references : before.ReferenceBounds) :
    after.ReferenceBounds ∧ StepsIn (fun child => child < after.count) equation.steps := by
  have result := closureEquation_reference (Index.ofEnvironment source) (rootReady source) position definition before
    ⟨⟨bounded,frontier,scalars⟩,references⟩
  change closureEquation (Index.ofEnvironment source) position definition before = (equation,after) at compiled
  rw [compiled] at result
  exact ⟨result.1.2,result.2⟩

/-- Exact enum-field compilation, including descriptor-owned Never placeholders. -/
def EnumNodesCompilation (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty)
    (before : Graph) (children : List (Ty × Nat)) (after : Graph) : Prop :=
  enumNodes index mode descriptor types before = (children,after)

theorem EnumNodesCompilation.references {source : Environment} {mode : Mode} {descriptor : Bool} {types : List Ty}
    {before after : Graph} {children : List (Ty × Nat)}
    (compiled : EnumNodesCompilation (Index.ofEnvironment source) mode descriptor types before children after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes)
    (references : before.ReferenceBounds) : after.ReferenceBounds ∧ ∀ child ∈ children, child.2 < after.count := by
  have result := enumNodes_reference (Index.ofEnvironment source) (rootReady source) mode descriptor types before
    ⟨⟨bounded,frontier,scalars⟩,references⟩
  change enumNodes (Index.ofEnvironment source) mode descriptor types before = (children,after) at compiled
  rw [compiled] at result
  exact ⟨result.1.2,result.2⟩

/-- Every actual typed compilation returns a root below its resulting
allocation frontier, including scalar interning, nominal references and checked
failure equations. This does not assert that every reserved row is installed. -/
theorem RootCompilation.root_bound {source : Environment} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat}
    (compiled : RootCompilation (Index.ofEnvironment source) mode ty before root after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes) :
    root < after.count := by
  have result := compileTy_root_bound (Index.ofEnvironment source) (rootReady source) mode ty before
    ⟨bounded,frontier,scalars⟩
  change compileTy (Index.ofEnvironment source) mode ty before = (root,after) at compiled
  rw [compiled] at result
  exact result

/-- Actual array-root compilation installs either its exact scaling equation
or a checked failure. The root witness alone cannot substitute a scalar layout. -/
theorem RootCompilation.array_equation_source {index : Index} {mode : Mode} {id : TyId} {count : Nat}
    {before after : Graph} {root : Nat}
    (compiled : RootCompilation index mode (.Array id count) before root after) :
    ∃ equation, after.nodes.find root = some equation ∧
      ((equation = scaled mode count (index.node mode id.index) ∧
          id.index < index.typeRows.size ∧ count ≤ word64Max) ∨
        ∃ error, equation = .done (.error error)) := by
  change compileTy index mode (.Array id count) before = (root,after) at compiled
  rw [compileTy.eq_def] at compiled
  dsimp only [scalar] at compiled
  let allocated := fun equation => (before.count,
    { before with nodes := before.nodes.insert before.count equation, count := before.count + 1 })
  simp only [pure_bind,bind_pure] at compiled
  split at compiled
  · change allocated (.done (.error .scalarTarget)) = (root,after) at compiled
    cases compiled
    exact ⟨.done (.error .scalarTarget),by simp [NatIndexTree.find_insert],.inr ⟨.scalarTarget,rfl⟩⟩
  · split at compiled
    · change allocated (.done (.error (.missingType id.index))) = (root,after) at compiled
      cases compiled
      exact ⟨.done (.error (.missingType id.index)),by simp [NatIndexTree.find_insert],.inr ⟨(.missingType id.index),rfl⟩⟩
    · split at compiled
      · change allocated (.done (.error .sizeOverflow)) = (root,after) at compiled
        cases compiled
        exact ⟨.done (.error .sizeOverflow),by simp [NatIndexTree.find_insert],.inr ⟨.sizeOverflow,rfl⟩⟩
      · change allocated (scaled mode count (index.node mode id.index)) = (root,after) at compiled
        have inside : id.index < index.typeRows.size := by
          by_cases present : id.index < index.typeRows.size
          · exact present
          trustIrCompilerProof {
            have absent : index.typeRows[id.index]? = none :=
              Array.getElem?_len_le _ (Nat.le_of_not_lt present)
            simp only [Array.get?_eq_getElem?,absent,Option.isSome, Bool.not_false,not_true_eq_false] at *
          } {
            have absent := Array.getElem?_eq_none (xs := index.typeRows) (Nat.le_of_not_lt present)
            simp only [absent,Option.isSome, Bool.not_false,not_true_eq_false] at *
          }
        have countBound : count ≤ word64Max := by omega
        cases compiled
        exact ⟨scaled mode count (index.node mode id.index),by simp [NatIndexTree.find_insert],.inl ⟨rfl,inside,countBound⟩⟩


/-- The existing equation-only interface follows from the source-bound witness. -/
theorem RootCompilation.array_equation {index : Index} {mode : Mode} {id : TyId} {count : Nat}
    {before after : Graph} {root : Nat}
    (compiled : RootCompilation index mode (.Array id count) before root after) :
    ∃ equation, after.nodes.find root = some equation ∧
      (equation = scaled mode count (index.node mode id.index) ∨
        ∃ error, equation = .done (.error error)) := by
  obtain ⟨equation,found,kind⟩ := compiled.array_equation_source
  refine ⟨equation,found,?_⟩
  rcases kind with ⟨same,_,_⟩ | failure
  · exact .inl same
  · exact .inr failure

/-- Actual shape compilation yields either a reserved shape root or an exact
locally guarded equation, including successful scalar cache hits. -/
theorem RootCompilation.shape_root {source : Environment} {ty : Ty} {before after : Graph} {root : Nat}
    (compiled : RootCompilation (Index.ofEnvironment source) .shape ty before root after)
    (bounded : before.Bounded) (frontier : 2 * (Index.ofEnvironment source).count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes) :
    ShapeRoot (Index.ofEnvironment source) after root := by
  have safe := compileTy_shape_root _ (Index.ofEnvironment source) (shapeReady source) ty before
    ⟨bounded, frontier, scalars⟩
  change compileTy (Index.ofEnvironment source) .shape ty before = (root, after) at compiled
  rw [compiled] at safe
  exact safe

theorem RootCompilation.preserves_modes {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (bounded : before.Bounded) (frontier : 2 * index.count + 2 ≤ before.count)
    (scalars : before.ScalarInvariant (2 * index.count + 2) index.source.model.pointerBytes)
    (modes : before.ModeInvariant index.nodeMode) : after.ModeInvariant index.nodeMode := by
  have safe := compileTy_mode_state index mode ty before ⟨⟨bounded, frontier, scalars⟩, modes⟩
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at safe
  exact safe.2

/-- Exact root selection by the actual query. A reused entry is identified
by full type and mode equality, not merely by its bucket. -/
inductive Session.RootSelection (session : Session) (mode : Mode) (ty : Ty) :
    Nat → Graph → Bool → Prop where
  | cached (root : Nat)
      (member : (ty, mode, root) ∈ (session.roots.find (rootBucket mode ty)).getD []) :
      RootSelection session mode ty root session.graph true
  | compiled (root : Nat) (graph : Graph)
      (run : RootCompilation session.index mode ty session.graph root graph) :
      RootSelection session mode ty root graph false

/-- The allocation frontier is fresh, covers all reserved source nodes, and every memo value is derived in
    the session's exact graph. Root/type correspondence is a separate claim. -/
def Session.DerivationInvariant (session : Session) : Prop :=
  (session.graph.Bounded ∧ 2 * session.index.count + 2 ≤ session.graph.count) ∧
    MemoDerivation session.graph session.memo

def prepare (source : Environment) : Session :=
  let index := Index.ofEnvironment source
  { index, graph := build index (uninhabitedFacts index) }

/-- Every installed source type row comes from its actual compilation during
preparation. All emitted equations are retained, whether the source row copied
an existing body or used an alias for a then-missing original reference. -/
theorem prepare_type_compilation (source : Environment) (mode : Mode) (position : Nat) (ty : Ty)
    (found : (trustIrListGet? source.types position) = some (some ty)) :
    ∃ before compiled root, before.Bounded ∧
      2 * (Index.ofEnvironment source).count + 2 ≤ before.count ∧
      before.ScalarInvariant (2 * (Index.ofEnvironment source).count + 2) source.model.pointerBytes ∧
      RootCompilation (Index.ofEnvironment source) mode ty before root compiled ∧
      compiled.Extends (prepare source).graph ∧
      (prepare source).graph.nodes.find ((Index.ofEnvironment source).node mode position) =
        some ((compiled.nodes.find root).getD (alias root)) := by
  let index := Index.ofEnvironment source
  let lower := globalClosures index + 1
  have initial : PreparationState lower source.model.pointerBytes 0 ({ count := lower } : Graph) :=
    ⟨⟨Graph.Bounded.empty lower,Nat.le_refl _,Graph.ScalarInvariant.empty _ _ _⟩,fun _ _ _ => rfl⟩
  obtain ⟨_,_,histories⟩ := buildProgram_history index (uninhabitedFacts index) (indexReady source) _ initial
  obtain ⟨before,compiled,root,valid,run,retained,installed⟩ := histories mode position ty found
  exact ⟨before,compiled,root,valid.1,valid.2.1,valid.2.2,run,retained,installed⟩

/-- Preparation establishes the real session invariant for every source,
    including malformed declarations whose equations will later refuse. -/
theorem prepare_derivation (source : Environment) : (prepare source).DerivationInvariant := by
  have ready := build_reserved (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
    (indexReady source)
  exact ⟨ready, MemoDerivation.empty _⟩

/-- Preparation installs only locally guarded equations and exact aliases,
for arbitrary source tables, including malformed rows that will later refuse. -/
theorem prepare_word (source : Environment) : (prepare source).graph.WordInvariant :=
  build_word (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))

/-- Every scalar key in a prepared graph names its exact target-specific
summary, outside all replaceable reserved source slots. -/
theorem prepare_scalars (source : Environment) :
    (prepare source).graph.ScalarInvariant (2 * (prepare source).index.count + 2)
      source.model.pointerBytes :=
  build_scalars (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
    (indexReady source)

/-- The source graph is finite by structural compilation of every literal
    type and original table row. Query recursion is solely Graph.solve.
    Repeated named questions reuse the same checked memo, across roots. -/
def Session.query (session : Session) (mode : Mode) (ty : Ty) : Result (Summary × Session) := do
  let bucket := 2 * typeBucket ty + (if mode == .shape then 0 else 1)
  let entries := (session.roots.find bucket).getD []
  let found := entries.find? (fun (original, originalMode, _) =>
    mode == originalMode && closureTyEq original ty)
  let (root, graph) := match found with
    | some (_, _, root) => (root, session.graph)
    | none => compileTy session.index mode ty session.graph
  let (value, memo) ← match session.memo.find root with
    | some value => pure (value, session.memo)
    | none => solve graph (Available.domain graph.nodes) root session.memo
  let roots := if found.isSome then session.roots
    else session.roots.insert bucket ((ty, mode, root) :: entries)
  pure (value, { session with graph, memo, roots })

private theorem session_complete_derivation (session : Session) (graph : Graph) (root : Nat)
    (roots : NatIndexTree (List (Ty × Mode × Nat))) (value : Summary) (next : Session)
    (bounded : graph.Bounded) (reserved : 2 * session.index.count + 2 ≤ graph.count)
    (cached : MemoDerivation graph session.memo)
    (run : (do
      let (value, memo) ← match session.memo.find root with
        | some value => pure (value, session.memo)
        | none => solve graph (Available.domain graph.nodes) root session.memo
      pure (value, { session with graph, memo, roots })) = .ok (value, next)) :
    next.DerivationInvariant ∧ next.index = session.index ∧ next.graph = graph ∧
      ∃ node, NodeDerivation next.graph node value := by
  cases hm : session.memo.find root with
  | some result =>
    simp only [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
    cases run
    exact ⟨⟨⟨bounded, reserved⟩, cached⟩, rfl, rfl, root, cached root value hm⟩
  | none =>
    simp only [hm] at run
    cases solved : solve graph (Available.domain graph.nodes) root session.memo with
    | error error =>
      simp only [solved, Bind.bind, Except.bind] at run <;> cases run
    | ok pair =>
      rcases pair with ⟨result, memo⟩
      have derived := solve_derivation graph (Available.domain graph.nodes) root session.memo
        result memo cached solved
      simp only [solved, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      exact ⟨⟨⟨bounded, reserved⟩, derived.2⟩, rfl, rfl, root, derived.1⟩

private theorem find_root_hit (predicate : Ty × Mode × Nat → Bool)
    (entries : List (Ty × Mode × Nat)) (entry : Ty × Mode × Nat)
    (found : entries.find? predicate = some entry) : entry ∈ entries ∧ predicate entry = true := by
  induction entries with
  | nil => cases found
  | cons head tail ih =>
    rw [List.find?_cons] at found
    cases accepted : predicate head with
    | false =>
      rw [accepted] at found
      have later := ih found
      exact ⟨List.mem_cons_of_mem _ later.1, later.2⟩
    | true =>
      rw [accepted] at found
      cases found
      exact ⟨(trustIrListMemConsSelf _ _), accepted⟩

private theorem session_complete_selected (session : Session) (graph : Graph) (root : Nat)
    (roots : NatIndexTree (List (Ty × Mode × Nat))) (value : Summary) (next : Session)
    (cached : MemoDerivation graph session.memo)
    (run : (do
      let (value, memo) ← match session.memo.find root with
        | some value => pure (value, session.memo)
        | none => solve graph (Available.domain graph.nodes) root session.memo
      pure (value, { session with graph, memo, roots })) = .ok (value, next)) :
    next.index = session.index ∧ next.graph = graph ∧ next.roots = roots ∧
      NodeDerivation graph root value := by
  cases hm : session.memo.find root with
  | some result =>
    simp only [hm, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
    cases run
    exact ⟨rfl, rfl, rfl, cached root value hm⟩
  | none =>
    simp only [hm] at run
    cases solved : solve graph (Available.domain graph.nodes) root session.memo with
    | error error => simp only [solved, Bind.bind, Except.bind] at run <;> cases run
    | ok pair =>
      rcases pair with ⟨result, memo⟩
      have derived := solve_derivation graph (Available.domain graph.nodes) root session.memo
        result memo cached solved
      simp only [solved, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      exact ⟨rfl, rfl, rfl, derived.1⟩

/-- Successful queries expose the exact selected root and its derivation,
including both root-cache hits and memo hits. A bucket collision cannot replace
full type or mode equality. -/
theorem Session.query_selection (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (run : session.query mode ty = .ok (value, next)) :
    ∃ root graph reused, session.RootSelection mode ty root graph reused ∧
      next.index = session.index ∧ next.graph = graph ∧
      next.roots = (if reused then session.roots else session.roots.insert (rootBucket mode ty)
        ((ty, mode, root) :: (session.roots.find (rootBucket mode ty)).getD [])) ∧
      NodeDerivation graph root value := by
  let bucket := rootBucket mode ty
  let entries := (session.roots.find bucket).getD []
  let found := entries.find? (fun (original, originalMode, _) =>
    mode == originalMode && closureTyEq original ty)
  let selection := match found with
    | some (_, _, root) => (root, session.graph)
    | none => compileTy session.index mode ty session.graph
  have growth : session.graph.Growth selection.2 := by
    cases hf : found with
    | none => simpa only [selection, hf] using compileTy_preserves session.index mode ty session.graph valid.1.1
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      simpa only [selection, hf] using Graph.Growth.refl valid.1.1
  have chosen : session.RootSelection mode ty selection.1 selection.2 found.isSome := by
    cases hf : found with
    | none =>
      simp only [selection, hf]
      exact .compiled _ _ rfl
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      have hit := find_root_hit _ entries (original, originalMode, root) hf
      have accepted : (mode == originalMode) = true ∧ closureTyEq original ty = true :=
        (@Bool.and_eq_true_iff _ _).mp hit.2
      have sameMode : mode = originalMode := by
        cases mode <;> cases originalMode
        all_goals first | rfl | (have impossible : false = true := accepted.1; cases impossible)
      have sameType := closureTyEq_sound original ty accepted.2
      subst original
      subst originalMode
      simpa only [selection, hf] using (Session.RootSelection.cached (session := session) root hit.1)
  change (match selection with
    | (root, graph) => do
      let (value, memo) ← match session.memo.find root with
        | some value => pure (value, session.memo)
        | none => solve graph (Available.domain graph.nodes) root session.memo
      let roots := if found.isSome then session.roots
        else session.roots.insert bucket ((ty, mode, root) :: entries)
      pure (value, { session with graph, memo, roots })) = .ok (value, next) at run
  cases selected : selection with
  | mk root graph =>
    simp only [selection] at selected
    simp only [selection, selected] at growth chosen run
    have completed := session_complete_selected session graph root _ value next
      (valid.2.weaken growth.equations) run
    exact ⟨root, graph, found.isSome, chosen, completed⟩

/-- Persistent query execution preserves derivation-backed cached values in
    the extended graph and never changes the source index. Every returned
    summary has a derivation in that actual output graph. -/
theorem Session.query_preserves_derivation (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (run : session.query mode ty = .ok (value, next)) :
    next.DerivationInvariant ∧ next.index = session.index ∧ session.graph.Growth next.graph ∧
      ∃ node, NodeDerivation next.graph node value := by
  let bucket := 2 * typeBucket ty + (if mode == .shape then 0 else 1)
  let entries := (session.roots.find bucket).getD []
  let found := entries.find? (fun (original, originalMode, _) =>
    mode == originalMode && closureTyEq original ty)
  let selection := match found with
    | some (_, _, root) => (root, session.graph)
    | none => compileTy session.index mode ty session.graph
  have growth : session.graph.Growth selection.2 := by
    cases hf : found with
    | none =>
      simpa only [selection, hf] using compileTy_preserves session.index mode ty session.graph valid.1.1
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      simpa only [selection, hf] using Graph.Growth.refl valid.1.1
  change (match selection with
    | (root, graph) => do
      let (value, memo) ← match session.memo.find root with
        | some value => pure (value, session.memo)
        | none => solve graph (Available.domain graph.nodes) root session.memo
      let roots := if found.isSome then session.roots
        else session.roots.insert bucket ((ty, mode, root) :: entries)
      pure (value, { session with graph, memo, roots })) = .ok (value, next) at run
  cases selected : selection with
  | mk root graph =>
    simp only [selection] at selected
    simp only [selection, selected] at growth run
    have completed := session_complete_derivation session graph root _ value next growth.bounded
      (Nat.le_trans valid.1.2 growth.count_mono) (valid.2.weaken growth.equations) run
    refine ⟨completed.1, completed.2.1, ?_, completed.2.2.2⟩
    rw [completed.2.2.1]
    exact growth

/-- Successful persistent queries preserve the compiler's byte-bound rules.
Combined with the real lifecycle's memo derivations, returned geometry is bounded. -/
theorem Session.query_preserves_word (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (word : session.graph.WordInvariant)
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.WordInvariant ∧ WordBounds 1 value := by
  let bucket := 2 * typeBucket ty + (if mode == .shape then 0 else 1)
  let entries := (session.roots.find bucket).getD []
  let found := entries.find? (fun (original, originalMode, _) =>
    mode == originalMode && closureTyEq original ty)
  let selection := match found with
    | some (_, _, root) => (root, session.graph)
    | none => compileTy session.index mode ty session.graph
  have growth : session.graph.Growth selection.2 := by
    cases hf : found with
    | none =>
      simpa only [selection, hf] using compileTy_preserves session.index mode ty session.graph valid.1.1
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      simpa only [selection, hf] using Graph.Growth.refl valid.1.1
  have wordSafe : selection.2.WordInvariant := by
    cases hf : found with
    | none => simpa only [selection, hf] using compileTy_word session.index mode ty session.graph word
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      simpa only [selection, hf] using word
  change (match selection with
    | (root, graph) => do
      let (value, memo) ← match session.memo.find root with
        | some value => pure (value, session.memo)
        | none => solve graph (Available.domain graph.nodes) root session.memo
      let roots := if found.isSome then session.roots
        else session.roots.insert bucket ((ty, mode, root) :: entries)
      pure (value, { session with graph, memo, roots })) = .ok (value, next) at run
  cases selected : selection with
  | mk root graph =>
    simp only [selection] at selected
    simp only [selection, selected] at growth wordSafe run
    have completed := session_complete_derivation session graph root _ value next growth.bounded
      (Nat.le_trans valid.1.2 growth.count_mono) (valid.2.weaken growth.equations) run
    have outputWord : next.graph.WordInvariant := by
      rw [completed.2.2.1]
      exact wordSafe
    rcases completed.2.2.2 with ⟨node, derived⟩
    exact ⟨outputWord, derived.satisfies outputWord⟩

/-- Successful real queries preserve target-specific scalar interning facts,
including their allocation boundary and exact installed equations. -/
theorem Session.query_preserves_scalars (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (scalars : session.graph.ScalarInvariant (2 * session.index.count + 2) session.index.source.model.pointerBytes)
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.ScalarInvariant (2 * next.index.count + 2) next.index.source.model.pointerBytes := by
  let bucket := 2 * typeBucket ty + (if mode == .shape then 0 else 1)
  let entries := (session.roots.find bucket).getD []
  let found := entries.find? (fun (original, originalMode, _) =>
    mode == originalMode && closureTyEq original ty)
  let selection := match found with
    | some (_, _, root) => (root, session.graph)
    | none => compileTy session.index mode ty session.graph
  have growth : session.graph.Growth selection.2 := by
    cases hf : found with
    | none =>
      simpa only [selection, hf] using compileTy_preserves session.index mode ty session.graph valid.1.1
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      simpa only [selection, hf] using Graph.Growth.refl valid.1.1
  have scalarSafe : selection.2.ScalarInvariant (2 * session.index.count + 2) session.index.source.model.pointerBytes := by
    cases hf : found with
    | none =>
      have kept := compileTy_scalar_state (2 * session.index.count + 2) session.index mode ty
        session.graph ⟨valid.1.1, valid.1.2, scalars⟩
      simpa only [selection, hf] using kept.2.2
    | some entry =>
      rcases entry with ⟨original, originalMode, root⟩
      simpa only [selection, hf] using scalars
  change (match selection with
    | (root, graph) => do
      let (value, memo) ← match session.memo.find root with
        | some value => pure (value, session.memo)
        | none => solve graph (Available.domain graph.nodes) root session.memo
      let roots := if found.isSome then session.roots
        else session.roots.insert bucket ((ty, mode, root) :: entries)
      pure (value, { session with graph, memo, roots })) = .ok (value, next) at run
  cases selected : selection with
  | mk root graph =>
    simp only [selection] at selected
    simp only [selection, selected] at growth scalarSafe run
    have completed := session_complete_derivation session graph root _ value next growth.bounded
      (Nat.le_trans valid.1.2 growth.count_mono) (valid.2.weaken growth.equations) run
    rw [completed.2.1, completed.2.2.1]
    exact scalarSafe

def query (source : Environment) (mode : Mode) (ty : Ty) : Result Summary := do
  pure (← (prepare source).query mode ty).1

/-- Every successful public layout result fits the byte geometry carrier.
No cache-validity, source-table well-formedness or equation oracle is assumed. -/
theorem query_word_bounds (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : WordBounds 1 value := by
  cases event : (prepare source).query mode ty with
  | error error => simp [query, event, Bind.bind, Except.bind] at run
  | ok pair =>
    rcases pair with ⟨result, next⟩
    have safe := Session.query_preserves_word (prepare source) mode ty result next
      (prepare_derivation source) (prepare_word source) event
    have same : result = value := by
      simpa [query, event, Bind.bind, Except.bind, Pure.pure, Except.pure] using run
    exact same ▸ safe.2

/-- Validate all actual tuple declarations, including unused rows and their
    reachable closure/refinement dependencies. No executable image is admitted. -/
def validateTupleRows (source : Environment) : Result Unit := do
  let session := prepare source
  let _ ← session.graph.query (globalTuples session.index)
  pure ()

/-- Independently validate every actual closure frame. Tuple validation asks
    only for the closure frames it reaches, as the reference implementation. -/
def validateClosureRows (source : Environment) : Result Unit := do
  let session := prepare source
  let _ ← session.graph.query (globalClosures session.index)
  pure ()

/-- Preparation assigns the exact shape and execution obligations even for
malformed source rows whose actual equations refuse. -/
theorem prepare_modes (source : Environment) :
    (prepare source).graph.ModeInvariant (prepare source).index.nodeMode :=
  (build_modes (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
    (indexReady source) (shapeReady source)).2

theorem Session.query_preserves_modes (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (scalars : session.graph.ScalarInvariant (2 * session.index.count + 2) session.index.source.model.pointerBytes)
    (modes : session.graph.ModeInvariant session.index.nodeMode)
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.ModeInvariant next.index.nodeMode := by
  rcases Session.query_selection session mode ty value next valid run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have selected : graph.ModeInvariant session.index.nodeMode := by
    cases chosen with
    | cached hit => exact modes
    | compiled graph compiled =>
      exact compiled.preserves_modes valid.1.1 valid.1.2 scalars modes
  rw [indexSame, graphSame]
  exact selected

private def StorageState (lower : Nat) (graph : Graph) : Prop :=
  graph.Bounded ∧ lower ≤ graph.count ∧ graph.StorageInvariant lower

private theorem add_storage (lower : Nat) (equation : Equation)
    (guarded : ∀ graph, StorageState lower graph → equation.StorageRule lower graph) :
    PreservesState (StorageState lower) (add equation) := by
  intro graph state
  exact ⟨state.1.allocate equation, Nat.le_trans state.2.1 (Nat.le_succ _),
    state.2.2.allocate state.1 equation (guarded graph state)⟩

private theorem add_storage_guarded (lower : Nat) (equation : Equation) (guarded : equation.StorageGuarded) :
    PreservesState (StorageState lower) (add equation) :=
  add_storage lower equation (fun graph state => guarded.rule lower graph)

private theorem failed_storage (lower : Nat) (error : Error) :
    PreservesState (StorageState lower) (failed error) :=
  add_storage_guarded lower _ (Equation.StorageGuarded.failed error)

private theorem put_storage (lower node : Nat) (inside : node < lower) (equation : Equation)
    (guarded : ∀ graph, StorageState lower graph → equation.StorageRule lower graph) :
    PreservesState (StorageState lower) (put node equation) := by
  intro graph state
  exact ⟨state.1.put node (Nat.lt_of_lt_of_le inside state.2.1) equation, state.2.1,
    state.2.2.put_below node inside equation (guarded graph state)⟩

private theorem leaves_storage (lower : Nat) (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState (StorageState lower)
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun graph state => ⟨state.1, state.2.1, state.2.2.leaves _⟩

private theorem addScalar_storage (lower : Nat) (result : Result Summary)
    (safe : ∀ value, result = .ok value → StorageGeometry value) :
    PreservesState (StorageState lower) (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_storage lower error
  | ok value =>
    apply PreservesState.bind (PreservesState.get (StorageState lower))
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_storage_guarded lower _ (Equation.StorageGuarded.done _ safe))
      intro node
      apply PreservesState.bind (leaves_storage lower (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _

set_option maxHeartbeats 1000000 in
private theorem compileTuple_storage (lower : Nat) (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState (StorageState lower) (compileTypes index mode fields))
    (shapeSafe : PreservesState (StorageState lower) (compileTypes index .shape fields)) :
    PreservesState (StorageState lower) (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_storage lower _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_storage_guarded lower
       repeat first
         | exact Equation.StorageGuarded.failed _
         | exact Equation.StorageGuarded.canonicalFields _ _ _ _
         | exact Equation.StorageGuarded.declaredFields _ _ _ _ _ _ _ _
         | apply Equation.StorageGuarded.sequence
         | split)
    | split

mutual
  private theorem compileTy_storage (lower : Nat) (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState (StorageState lower) (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_storage lower _
    · split
      · rename_i result found
        exact addScalar_storage lower result (fun value success =>
          (scalar_admissible mode index.source ty result value found success).storage_geometry)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact failed_storage lower _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_storage lower _
            | (apply PreservesState.bind (compileTy_storage lower index mode element)
               intro child
               exact add_storage_guarded lower _ (Equation.StorageGuarded.scaled mode count child))
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_storage lower index mode fields
            (compileTypes_storage lower index mode fields) (compileTypes_storage lower index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_storage lower _
          | exact add_storage_guarded lower _ (Equation.StorageGuarded.scaled _ _ _)
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_storage (lower : Nat) (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState (StorageState lower) (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_storage lower index mode first)
      intro child
      apply PreservesState.bind (compileTypes_storage lower index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def BuildsStorageEquation (lower : Nat) (action : Build Equation) : Prop :=
  ∀ graph, StorageState lower graph →
    StorageState lower (action graph).2 ∧ (action graph).1.StorageRule lower (action graph).2

private theorem BuildsStorageEquation.pure (lower : Nat) (equation : Equation)
    (safe : ∀ graph, equation.StorageRule lower graph) :
    BuildsStorageEquation lower (pure equation) := fun graph valid => ⟨valid, safe graph⟩

private theorem BuildsStorageEquation.bind {lower : Nat} {α : Type} {action : Build α} {next : α → Build Equation}
    (first : PreservesState (StorageState lower) action)
    (later : ∀ value, BuildsStorageEquation lower (next value)) : BuildsStorageEquation lower (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (first graph valid)

private theorem BuildsStorageEquation.install_yield {lower : Nat} {α : Type} {action : Build Equation}
    (node : Nat) (inside : node < lower) (result : α) (safe : BuildsStorageEquation lower action) :
    PreservesState (StorageState lower) (do put node (← action); Pure.pure result) := by
  intro graph valid
  have built := safe graph valid
  exact ⟨built.1.1.put node (Nat.lt_of_lt_of_le inside built.1.2.1) _, built.1.2.1,
    built.1.2.2.put_below node inside _ built.2⟩

private theorem copyRoot_storage (lower child : Nat) : BuildsStorageEquation lower (do
    let graph ← get
    pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  refine ⟨valid, ?_⟩
  change ((graph.nodes.find child).getD (alias child)).StorageRule lower graph
  cases found : graph.nodes.find child with
  | none => exact Equation.StorageRule.alias lower graph child
  | some equation => exact valid.2.2 child equation found

private theorem structEquation_storage (lower : Nat) (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsStorageEquation lower (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsStorageEquation.pure; intro graph; exact (Equation.StorageGuarded.failed _).rule _ _)
    | (apply BuildsStorageEquation.pure; intro graph; exact (Equation.StorageGuarded.canonicalFields _ _ _ _).rule _ _)
    | (apply BuildsStorageEquation.pure; intro graph; exact (Equation.StorageGuarded.declaredFields _ _ _ _ _ _ _ _).rule _ _)
    | (apply BuildsStorageEquation.bind (compileTypes_storage lower _ _ _); intro children)
    | split

private theorem closureEquation_storage (lower : Nat) (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsStorageEquation lower (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsStorageEquation.pure; intro graph; exact (Equation.StorageGuarded.failed _).rule _ _)
    | (apply BuildsStorageEquation.pure; intro graph; exact (Equation.StorageGuarded.declaredFields _ _ _ _ _ _ _ _).rule _ _)
    | (apply BuildsStorageEquation.bind (compileTypes_storage lower _ _ _); intro children)
    | split

private theorem enumNodes_storage (lower : Nat) (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState (StorageState lower) (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_storage lower _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_storage_guarded lower _ (Equation.StorageGuarded.done _
           (by intro value same; cases same; exact StorageGeometry.empty_fields rfl rfl)))
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private def VariantCertificates (lower : Nat) (definition : EnumDef) (nodes : List Nat) (graph : Graph) : Prop :=
  ∀ descriptor, definition.layout = some descriptor →
    graph.ParentFieldCertificates descriptor.size nodes ∧ ∀ child, child ∈ nodes → lower ≤ child

private theorem VariantCertificates.empty (lower : Nat) (definition : EnumDef) (graph : Graph) :
    VariantCertificates lower definition [] graph := by
  intro descriptor authored
  constructor
  · intro child impossible; cases impossible
  · intro child impossible; cases impossible

private theorem VariantCertificates.weaken {lower : Nat} {definition : EnumDef} {nodes : List Nat}
    {before after : Graph} (safe : VariantCertificates lower definition nodes before)
    (extended : before.Extends after) : VariantCertificates lower definition nodes after := by
  intro descriptor authored
  have old := safe descriptor authored
  exact ⟨old.1.weaken extended, old.2⟩

private theorem variantEquation_storage (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).StorageGuarded := by
  repeat first
    | exact Equation.StorageGuarded.failed _
    | exact Equation.StorageGuarded.canonicalFields _ _ _ _
    | exact Equation.StorageGuarded.declaredFields _ _ _ _ _ _ _ _
    | split

private theorem forIn_accumulator {α β : Type} (invariant : β → Graph → Prop)
    (rows : List α) (initial : β) (body : α → β → Build (ForInStep β))
    (preserved : ∀ row, row ∈ rows → ∀ acc graph, invariant acc graph →
      invariant (match (body row acc graph).1 with | .done value | .yield value => value) (body row acc graph).2)
    (graph : Graph) (valid : invariant initial graph) :
    invariant (forIn rows initial body graph).1 (forIn rows initial body graph).2 := by
  induction rows generalizing initial graph with
  | nil => rw [List.forIn_nil]; exact valid
  | cons first rest ih =>
    have step := preserved first ((trustIrListMemConsSelf _ _)) initial graph valid
    rw [List.forIn_cons]
    cases outcome : body first initial graph with
    | mk selected after =>
      rw [outcome] at step
      cases selected with
      | done value =>
        simpa only [Bind.bind, StateT.bind, outcome, Pure.pure, StateT.pure] using step
      | yield value =>
        have later := ih value (fun row member => preserved row (List.mem_cons_of_mem _ member)) after step
        simpa only [Bind.bind, StateT.bind, outcome] using later

private theorem variantEquation_parent_storage (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) (descriptor : EnumLayoutDescriptor)
    (authored : definition.layout = some descriptor) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).ParentFieldGuarded descriptor.size := by
  rw [authored]
  exact Equation.ParentFieldGuarded.descriptorVariant mode definition.id.index descriptor children variantIndex

private theorem variantStep_storage (lower : Nat) (definition : EnumDef)
    (action : Build (List (Ty × Nat))) (equations : List (Ty × Nat) → Equation)
    (preserved : PreservesState (StorageState lower) action) (grows : PreservesGraph action)
    (guarded : ∀ children, (equations children).StorageGuarded)
    (parents : ∀ descriptor, definition.layout = some descriptor → ∀ children,
      (equations children).ParentFieldGuarded descriptor.size)
    (nodes : List Nat) (graph : Graph)
    (valid : StorageState lower graph ∧ VariantCertificates lower definition nodes graph) :
    let result := (do
      let children ← action
      let node ← add (equations children)
      pure (ForInStep.yield (node :: nodes))) graph
    StorageState lower result.2 ∧ VariantCertificates lower definition
      (match result.1 with | .done value | .yield value => value) result.2 := by
  let before := (action graph).2
  let equation := equations (action graph).1
  let after : Graph := { before with nodes := before.nodes.insert before.count equation, count := before.count + 1 }
  have state : StorageState lower before := preserved graph valid.1
  have certificates : VariantCertificates lower definition nodes before :=
    valid.2.weaken (grows graph valid.1.1).equations
  have added : StorageState lower after := add_storage_guarded lower equation (guarded _) before state
  change StorageState lower after ∧ VariantCertificates lower definition (before.count :: nodes) after
  refine ⟨added, ?_⟩
  intro descriptor authored
  have old := certificates descriptor authored
  refine ⟨old.1.allocate state.1 equation (parents descriptor authored _), ?_⟩
  intro child member
  cases member with
  | head => exact state.2.1
  | tail _ member => exact old.2 child member

private theorem enumVariants_storage (lower : Nat) (index : Index) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat))
    (nodes : List Nat) (graph : Graph)
    (valid : StorageState lower graph ∧ VariantCertificates lower definition nodes graph) :
    let result := (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) graph
    StorageState lower result.2 ∧ VariantCertificates lower definition result.1 result.2 := by
  apply forIn_accumulator (fun nodes graph => StorageState lower graph ∧ VariantCertificates lower definition nodes graph)
    rows nodes _ ?_ graph valid
  intro row member acc before state
  rcases row with ⟨variant, variantIndex⟩
  dsimp only
  by_cases skipped : selected.any (fun active => variantIndex != active) = true
  all_goals simp only [skipped, ite_true, ite_false]
  · apply variantStep_storage lower definition _ _
    · exact PreservesState.pure _ _
    · exact PreservesGraph.pure _
    · intro children
      exact variantEquation_storage mode definition children variantIndex
    · intro descriptor authored children
      exact variantEquation_parent_storage mode definition children variantIndex descriptor authored
    · exact state
  · apply variantStep_storage lower definition _ _
    · exact enumNodes_storage lower index mode definition.layout.isSome variant.fields
    · exact enumNodes_preserves index mode definition.layout.isSome variant.fields
    · intro children
      exact variantEquation_storage mode definition children variantIndex
    · intro descriptor authored children
      exact variantEquation_parent_storage mode definition children variantIndex descriptor authored
    · exact state


private theorem storage_member_append {α : Type} (value : α) (left right : List α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons first rest ih => simp [List.cons_append, ih, or_assoc]

private theorem storage_member_reverse {α : Type} (value : α) (values : List α) :
    value ∈ values.reverse ↔ value ∈ values := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.reverse_cons, storage_member_append, ih, or_comm]

private theorem enumEquation_storage (lower : Nat) (index : Index) (mode : Mode)
    (definition : EnumDef) (facts : NatIndexTree Unit) :
    BuildsStorageEquation lower (do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := match definition.layout with
        | some descriptor => match descriptor.encoding with
          | .singleInhabited selected =>
            if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
          | _ => none
        | none => none
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      pure equation) := by
  intro graph valid
  let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
  let selected := match definition.layout with
    | some descriptor => match descriptor.encoding with
      | .singleInhabited selected =>
        if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
      | _ => none
    | none => none
  let variantsAction : Build (List Nat) := do
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      -- Skip physical children only after checking the actual structural
      -- facts and all inactive offset rows. Logical rows retain their IDs.
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    pure variants
  have built := enumVariants_storage lower index mode definition selected
    (numbered definition.variants) [] graph ⟨valid, VariantCertificates.empty lower definition graph⟩
  change StorageState lower (variantsAction graph).2 ∧
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)
      then Equation.done (.error Error.scalarTarget)
      else enumEquation mode definition uninhabited (variantsAction graph).1.reverse).StorageRule lower (variantsAction graph).2
  refine ⟨built.1, ?_⟩
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact (Equation.StorageGuarded.failed _).rule _ _
  · cases authored : definition.layout with
    | none => exact Equation.StorageRule.canonicalEnum lower _ mode definition uninhabited _ authored
    | some descriptor =>
      have certificates := built.2 descriptor authored
      apply Equation.StorageRule.descriptorEnum lower _ mode definition uninhabited _ descriptor authored
        certificates.1.reverse
      intro child member
      exact certificates.2 child ((storage_member_reverse child (variantsAction graph).1).mp member)

private def VariantReferenceState (index : Index) (nodes : List Nat) (graph : Graph) : Prop :=
  ReferenceState index graph ∧ ∀ node ∈ nodes, node < graph.count

private theorem variantStep_reference (index : Index)
    (action : Build (List (Ty × Nat))) (equations : List (Ty × Nat) → Equation)
    (certified : ∀ graph, ReferenceState index graph → ReferenceState index (action graph).2 ∧
      ∀ child ∈ (action graph).1, child.2 < (action graph).2.count)
    (grows : PreservesGraph action)
    (guarded : ∀ (bound : Nat) (children : List (Ty × Nat)), (∀ child ∈ children, child.2 < bound) → StepsIn (fun child => child < bound) (equations children).steps)
    (nodes : List Nat) (graph : Graph) (valid : VariantReferenceState index nodes graph) :
    let result := (do
      let children ← action
      let node ← add (equations children)
      pure (ForInStep.yield (node :: nodes))) graph
    VariantReferenceState index (match result.1 with | .done value | .yield value => value) result.2 := by
  let before := (action graph).2
  let equation := equations (action graph).1
  let after : Graph := { before with nodes := before.nodes.insert before.count equation, count := before.count + 1 }
  have children := certified graph valid.1
  have growth := grows graph valid.1.1.1
  have safe := guarded before.count (action graph).1 children.2
  change VariantReferenceState index (before.count :: nodes) after
  refine ⟨add_reference_state index equation before children.1
    (safe.mono (fun _ inside => Nat.lt_succ_of_lt inside)),?_⟩
  intro node member
  cases member with
  | head => exact Nat.lt_succ_self _
  | tail _ member => exact Nat.lt_of_lt_of_le (valid.2 node member) (Nat.le_trans growth.count_mono (Nat.le_succ _))

private theorem enumVariants_reference (index : Index) (ready : RootReady index) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat))
    (nodes : List Nat) (graph : Graph) (valid : VariantReferenceState index nodes graph) :
    let result := (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) graph
    VariantReferenceState index result.1 result.2 := by
  apply forIn_accumulator (VariantReferenceState index) rows nodes _ ?_ graph valid
  intro row member acc before state
  rcases row with ⟨variant,variantIndex⟩
  dsimp only
  by_cases skipped : selected.any (fun active => variantIndex != active) = true
  all_goals simp only [skipped,ite_true,ite_false]
  · apply variantStep_reference index _ _
    · intro graph valid
      exact ⟨valid,fun child member => by cases member⟩
    · exact PreservesGraph.pure _
    · intro bound children safe
      exact variantEquation_reference mode definition children variantIndex safe
    · exact state
  · apply variantStep_reference index _ _
    · exact enumNodes_reference index ready mode definition.layout.isSome variant.fields
    · exact enumNodes_preserves index mode definition.layout.isSome variant.fields
    · intro bound children safe
      exact variantEquation_reference mode definition children variantIndex safe
    · exact state

private theorem enumEquation_reference (index : Index) (ready : RootReady index) (mode : Mode)
    (definition : EnumDef) (facts : NatIndexTree Unit) :
    BuildsReferenceEquation index (do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := match definition.layout with
        | some descriptor => match descriptor.encoding with
          | .singleInhabited selected =>
            if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
          | _ => none
        | none => none
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      pure equation) := by
  intro graph valid
  let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
  let selected := match definition.layout with
    | some descriptor => match descriptor.encoding with
      | .singleInhabited selected =>
        if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
      | _ => none
    | none => none
  let variantsAction : Build (List Nat) := do
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      -- Skip physical children only after checking the actual structural
      -- facts and all inactive offset rows. Logical rows retain their IDs.
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    pure variants
  have built := enumVariants_reference index ready mode definition selected
    (numbered definition.variants) [] graph ⟨valid,fun node member => by cases member⟩
  change ReferenceState index (variantsAction graph).2 ∧
    StepsIn (fun child => child < (variantsAction graph).2.count)
      (if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
          | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)
        then Equation.done (.error Error.scalarTarget)
        else enumEquation mode definition uninhabited (variantsAction graph).1.reverse).steps
  refine ⟨built.1,?_⟩
  by_cases refused : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = true
  · rw [if_pos refused]; exact True.intro
  · rw [if_neg refused]
    apply Equation.references_enum
    intro node member
    exact built.2 node ((storage_member_reverse node (variantsAction graph).1).mp member)

private theorem BuildsReferenceEquation.install_yield (index : Index) (node : Nat)
    (reserved : node < 2 * index.count + 2) (action : Build Equation)
    (safe : BuildsReferenceEquation index action) :
    PreservesState (ReferenceState index) (do
      let equation ← action
      put node equation
      Pure.pure (ForInStep.yield ())) := by
  intro graph valid
  have built := safe graph valid
  exact ⟨put_scalar_state _ _ node reserved (action graph).1 (action graph).2 built.1.1,
    built.1.2.insert (action graph).2.count (Nat.le_refl _) node (action graph).1 built.2⟩

private theorem copyCompiled_reference (index : Index) (ready : RootReady index) (mode : Mode) (ty : Ty) :
    BuildsReferenceEquation index (do
      let child ← compileTy index mode ty
      let graph ← get
      pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  let compiled := compileTy index mode ty graph
  have state := compileTy_reference_state index ready mode ty graph valid
  have inside := compileTy_root_bound index ready mode ty graph valid.1
  change ReferenceState index compiled.2 ∧ StepsIn (fun child => child < compiled.2.count)
    ((compiled.2.nodes.find compiled.1).getD (alias compiled.1)).steps
  refine ⟨state,?_⟩
  cases found : compiled.2.nodes.find compiled.1 with
  | none => exact Equation.references_alias compiled.1 inside
  | some equation => exact state.2 compiled.1 equation found

private theorem array_join_bound {α : Type} (rows : Array (Option α)) (position : Nat) (value : α)
    (found : ((trustIrArrayGet? rows position)).join = some value) : position < rows.size := by
  cases lookup : (trustIrArrayGet? rows position) with
  | none => rw [lookup] at found; cases found
  | some entry => exact array_present_bound rows position (by rw [lookup]; rfl)

private theorem tupleValidation_references (index : Index) (rows : List TupleLayoutDescriptor) :
    StepsIn (fun child => child < 2 * index.count + 2)
      (rows.map (fun row => match ((trustIrArrayGet? index.typeRows row.tupleType.index)).join with
        | none => (Step.check fun (_ : Unit) => .error (.missingType row.tupleType.index))
        | some (.Tuple _) => .child (index.node .shape row.tupleType.index) fun _ state => .ok state
        | some _ => .check fun _ => .error (.incoherent "tuple" row.tupleType.index))) := by
  induction rows with
  | nil => trivial
  | cons row rows ih =>
    rw [List.map_cons]
    try dsimp only
    cases found : ((trustIrArrayGet? index.typeRows row.tupleType.index)).join with
    | none => exact ih
    | some ty =>
      cases ty <;> try exact ih
      refine ⟨?_,ih⟩
      have inside := array_join_bound index.typeRows row.tupleType.index _ found
      simp only [Index.node,show (Mode.shape == Mode.shape) = true from rfl,ite_true,Nat.zero_add]
      unfold Index.count Index.closureBase Index.enumBase Index.structBase
      omega

private theorem closureValidation_references (index : Index) (rows : List ClosureLayoutDescriptor) :
    StepsIn (fun child => child < 2 * index.count + 2)
      (rows.map (fun row => if !((trustIrArrayGet? index.closureRows row.closure.index)).isSome then
        (Step.check fun (_ : Unit) => .error (.incoherent "closure" row.closure.index))
        else .child (index.node .shape (index.closureBase + row.closure.index)) fun _ state => .ok state)) := by
  induction rows with
  | nil => trivial
  | cons row rows ih =>
    by_cases present : ((trustIrArrayGet? index.closureRows row.closure.index)).isSome = true
    · simp only [List.map_cons,present,Bool.not_true,Bool.false_eq_true,ite_false]
      refine ⟨?_,ih⟩
      have inside := array_present_bound index.closureRows row.closure.index present
      simp only [Index.node,show (Mode.shape == Mode.shape) = true from rfl,ite_true,Nat.zero_add]
      unfold Index.count
      omega
    · have absent : ((trustIrArrayGet? index.closureRows row.closure.index)).isSome = false := by
        cases lookup : (trustIrArrayGet? index.closureRows row.closure.index) with
        | none => rfl
        | some value =>
          exact False.elim (present (by rw [lookup]; rfl))
      simp only [List.map_cons,absent,Bool.not_false,ite_true]
      exact ih

private theorem buildProgram_covers (index : Index) (facts : NatIndexTree Unit) : CoversGraph (buildProgram index facts) := by
  unfold buildProgram
  dsimp only
  simp only [pure_bind,bind_pure]
  apply CoversGraph.bind
  · apply CoversGraph.forIn
    intro mode modeMember modeState
    apply CoversGraph.bind
    · apply CoversGraph.forIn
      intro row member state
      rcases row with ⟨entry,position⟩
      cases entry with
      | none =>
        apply CoversGraph.bind (put_covers _ _)
        intro unit
        exact CoversGraph.pure _
      | some ty =>
        apply CoversGraph.bind (compileTy_covers index mode ty)
        intro child
        apply CoversGraph.bind CoversGraph.get
        intro graph
        apply CoversGraph.bind (put_covers _ _)
        intro unit
        exact CoversGraph.pure _
    · intro unit
      apply CoversGraph.bind
      · apply CoversGraph.forIn
        intro row member state
        rcases row with ⟨definition,position⟩
        apply CoversGraph.bind (structEquation_covers index mode definition)
        intro equation
        apply CoversGraph.bind (put_covers _ _)
        intro unit
        exact CoversGraph.pure _
      · intro unit
        apply CoversGraph.bind
        · apply CoversGraph.forIn
          intro row member state
          rcases row with ⟨definition,position⟩
          apply CoversGraph.bind
          · apply CoversGraph.forIn
            intro row variantMember variants
            rcases row with ⟨variant,variantIndex⟩
            repeat first
              | exact CoversGraph.pure _
              | (apply CoversGraph.bind (enumNodes_covers _ _ _ _); intro children)
              | (apply CoversGraph.bind (add_covers _); intro node)
              | (simp only [pure_bind])
              | split
          · intro variants
            apply CoversGraph.bind (put_covers _ _)
            intro unit
            exact CoversGraph.pure _
        · intro unit
          apply CoversGraph.bind
          · apply CoversGraph.forIn
            intro row member state
            rcases row with ⟨definition,position⟩
            repeat first
              | exact CoversGraph.pure _
              | (apply CoversGraph.bind (closureEquation_covers _ _ _); intro equation)
              | (apply CoversGraph.bind (put_covers _ _); intro unit)
              | split
          · intro unit
            exact CoversGraph.pure _
  · intro unit
    apply CoversGraph.bind (put_covers _ _)
    intro unit
    exact put_covers _ _

/-- Preparation fills every dynamically allocated slot. Reserved source slots
below the initial frontier require the separate row-installation argument. -/
theorem prepare_allocated_present (source : Environment) (node : Nat)
    (allocated : 2 * (prepare source).index.count + 2 ≤ node)
    (inside : node < (prepare source).graph.count) :
    (prepare source).graph.Present node := by
  let index := Index.ofEnvironment source
  have coverage := buildProgram_covers index (uninhabitedFacts index)
    ({ count := globalClosures index + 1 } : Graph)
  apply coverage.fresh node
  · change globalClosures index + 1 ≤ node
    simpa only [prepare, globalClosures, globalTuples, Nat.add_assoc] using allocated
  · exact inside

private theorem put_installs (node : Nat) (equation : Equation) : Installs node (put node equation) :=
  fun graph => Graph.present_insert graph node equation

private theorem build_validators_present (index : Index) (facts : NatIndexTree Unit) :
    (build index facts).Present (globalTuples index) ∧
    (build index facts).Present (globalClosures index) := by
  have tuples : Installs (globalTuples index) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind,bind_pure]
    apply Installs.bind_right _
    intro unit
    exact Installs.bind_left (put_installs _ _) (fun _ => put_covers _ _)
  have closures : Installs (globalClosures index) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind,bind_pure]
    apply Installs.bind_right _
    intro unit
    apply Installs.bind_right _
    intro unit
    exact put_installs _ _
  exact ⟨tuples _,closures _⟩

/-- Both final validation roots are installed, even when their equations
will refuse malformed tuple or closure metadata. -/
theorem prepare_validators_present (source : Environment) :
    (prepare source).graph.Present (2 * (prepare source).index.count) ∧
    (prepare source).graph.Present (2 * (prepare source).index.count + 1) :=
  build_validators_present (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))

private theorem build_rows_present (index : Index) (facts : NatIndexTree Unit) (mode : Mode) (position : Nat)
    (row : (∃ entry, (entry,position) ∈ numbered index.source.types) ∨
      (∃ entry offset, position = index.structBase + offset ∧ (entry,offset) ∈ numbered index.source.structs) ∨
      (∃ entry offset, position = index.enumBase + offset ∧ (entry,offset) ∈ numbered index.source.enums) ∨
      (∃ entry offset, position = index.closureBase + offset ∧ (entry,offset) ∈ numbered index.source.closures)) :
    (build index facts).Present (index.node mode position) := by
  let typeBody (mode : Mode) (row : Option Ty × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (entry, position) := row
    let equation ← match entry with
      | none => pure (.done (.error (.missingType position)))
      | some ty => do
        let child ← compileTy index mode ty
        let graph ← get
        pure ((graph.nodes.find child).getD (alias child))
    put (index.node mode position) equation
    pure (.yield ())
  let structBody (mode : Mode) (row : StructDef × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (definition, position) := row
    put (index.node mode (index.structBase + position)) (← structEquation index mode definition)
    pure (.yield ())
  let enumBody (mode : Mode) (row : EnumDef × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (definition, position) := row
    let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
    let selected := enumPhysicalSelection definition uninhabited
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    let equation := enumEquation mode definition uninhabited variants.reverse
    let equation := if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
          Equation.done (.error Error.scalarTarget) else equation
    put (index.node mode (index.enumBase + position)) equation
    pure (.yield ())
  let closureBody (mode : Mode) (row : ClosureTy × Nat) (_ : Unit) : Build (ForInStep Unit) := do
    let (definition, position) := row
    let equation ← if mode == .shape then closureEquation index position definition
      else pure (Equation.done (.error (.unsupported (.Closure ⟨position⟩))))
    put (index.node mode (index.closureBase + position)) equation
    pure (.yield ())
  let modeBody (mode : Mode) (_ : Unit) : Build (ForInStep Unit) := do
    forIn (numbered index.source.types) () (typeBody mode)
    forIn (numbered index.source.structs) () (structBody mode)
    forIn (numbered index.source.enums) () (enumBody mode)
    forIn (numbered index.source.closures) () (closureBody mode)
    pure (.yield ())
  have typeCover : ∀ mode row, CoversGraph (typeBody mode row ()) := by
    intro mode row
    rcases row with ⟨entry,position⟩
    dsimp only [typeBody]
    repeat first
      | exact CoversGraph.pure _
      | exact CoversGraph.get
      | exact put_covers _ _
      | exact compileTy_covers _ _ _
      | exact structEquation_covers _ _ _
      | exact closureEquation_covers _ _ _
      | exact enumNodes_covers _ _ _ _
      | exact add_covers _
      | apply CoversGraph.bind
      | (apply CoversGraph.forIn; intro row member acc; rcases row with ⟨entry,position⟩)
      | (simp only [pure_bind,bind_pure])
      | split
      | intro value
  have structCover : ∀ mode row, CoversGraph (structBody mode row ()) := by
    intro mode row
    rcases row with ⟨entry,position⟩
    dsimp only [structBody]
    repeat first
      | exact CoversGraph.pure _
      | exact CoversGraph.get
      | exact put_covers _ _
      | exact compileTy_covers _ _ _
      | exact structEquation_covers _ _ _
      | exact closureEquation_covers _ _ _
      | exact enumNodes_covers _ _ _ _
      | exact add_covers _
      | apply CoversGraph.bind
      | (apply CoversGraph.forIn; intro row member acc; rcases row with ⟨entry,position⟩)
      | (simp only [pure_bind,bind_pure])
      | split
      | intro value
  have enumCover : ∀ mode row, CoversGraph (enumBody mode row ()) := by
    intro mode row
    rcases row with ⟨entry,position⟩
    dsimp only [enumBody]
    repeat first
      | exact CoversGraph.pure _
      | exact CoversGraph.get
      | exact put_covers _ _
      | exact compileTy_covers _ _ _
      | exact structEquation_covers _ _ _
      | exact closureEquation_covers _ _ _
      | exact enumNodes_covers _ _ _ _
      | exact add_covers _
      | apply CoversGraph.bind
      | (apply CoversGraph.forIn; intro row member acc; rcases row with ⟨entry,position⟩)
      | (simp only [pure_bind,bind_pure])
      | split
      | intro value
  have closureCover : ∀ mode row, CoversGraph (closureBody mode row ()) := by
    intro mode row
    rcases row with ⟨entry,position⟩
    dsimp only [closureBody]
    repeat first
      | exact CoversGraph.pure _
      | exact CoversGraph.get
      | exact put_covers _ _
      | exact compileTy_covers _ _ _
      | exact structEquation_covers _ _ _
      | exact closureEquation_covers _ _ _
      | exact enumNodes_covers _ _ _ _
      | exact add_covers _
      | apply CoversGraph.bind
      | (apply CoversGraph.forIn; intro row member acc; rcases row with ⟨entry,position⟩)
      | (simp only [pure_bind,bind_pure])
      | split
      | intro value
  have typeLoop : ∀ mode, CoversGraph (forIn (numbered index.source.types) () (typeBody mode)) :=
    fun mode => CoversGraph.forIn _ _ _ (fun row _ _ => typeCover mode row)
  have structLoop : ∀ mode, CoversGraph (forIn (numbered index.source.structs) () (structBody mode)) :=
    fun mode => CoversGraph.forIn _ _ _ (fun row _ _ => structCover mode row)
  have enumLoop : ∀ mode, CoversGraph (forIn (numbered index.source.enums) () (enumBody mode)) :=
    fun mode => CoversGraph.forIn _ _ _ (fun row _ _ => enumCover mode row)
  have closureLoop : ∀ mode, CoversGraph (forIn (numbered index.source.closures) () (closureBody mode)) :=
    fun mode => CoversGraph.forIn _ _ _ (fun row _ _ => closureCover mode row)
  have modeCover : ∀ mode, CoversGraph (modeBody mode ()) := by
    intro mode
    dsimp only [modeBody]
    repeat first
      | exact CoversGraph.pure _
      | (apply CoversGraph.bind (typeLoop _); intro unit)
      | (apply CoversGraph.bind (structLoop _); intro unit)
      | (apply CoversGraph.bind (enumLoop _); intro unit)
      | (apply CoversGraph.bind (closureLoop _); intro unit)
  have modeWrites : ∀ selected, Installs (index.node selected position) (modeBody selected ()) := by
    intro selected
    rcases row with typeRow | structRow | enumRow | closureRow
    · obtain ⟨entry,member⟩ := typeRow
      dsimp only [modeBody]
      apply Installs.bind_left
      · apply Installs.forIn_member (destination := fun entry => index.node selected (entry.2)) (row := (entry,position))
        · exact typeCover selected
        · intro row graph
          rcases row with ⟨entry,position⟩
          dsimp only [typeBody]
          cases entry <;> rfl
        · intro row
          rcases row with ⟨entry,position⟩
          dsimp only [typeBody]
          repeat first
            | exact put_installs _ _
            | (apply Installs.bind_left (put_installs _ _); intro unit; exact CoversGraph.pure _)
            | (apply Installs.bind_right _; intro value)
            | (simp only [pure_bind,bind_pure])
            | split
        · exact member
      · intro unit
        repeat first
          | exact CoversGraph.pure _
          | (apply CoversGraph.bind (typeLoop _); intro unit)
          | (apply CoversGraph.bind (structLoop _); intro unit)
          | (apply CoversGraph.bind (enumLoop _); intro unit)
          | (apply CoversGraph.bind (closureLoop _); intro unit)
    · obtain ⟨entry,offset,same,member⟩ := structRow
      subst position
      dsimp only [modeBody]
      apply Installs.bind_right _
      intro unit
      apply Installs.bind_left
      · apply Installs.forIn_member (destination := fun entry => index.node selected (index.structBase + entry.2)) (row := (entry,offset))
        · exact structCover selected
        · intro row graph
          rcases row with ⟨entry,position⟩
          dsimp only [structBody]
          rfl
        · intro row
          rcases row with ⟨entry,position⟩
          dsimp only [structBody]
          repeat first
            | exact put_installs _ _
            | (apply Installs.bind_left (put_installs _ _); intro unit; exact CoversGraph.pure _)
            | (apply Installs.bind_right _; intro value)
            | (simp only [pure_bind,bind_pure])
            | split
        · exact member
      · intro unit
        repeat first
          | exact CoversGraph.pure _
          | (apply CoversGraph.bind (typeLoop _); intro unit)
          | (apply CoversGraph.bind (structLoop _); intro unit)
          | (apply CoversGraph.bind (enumLoop _); intro unit)
          | (apply CoversGraph.bind (closureLoop _); intro unit)
    · obtain ⟨entry,offset,same,member⟩ := enumRow
      subst position
      dsimp only [modeBody]
      apply Installs.bind_right _
      intro unit
      apply Installs.bind_right _
      intro unit
      apply Installs.bind_left
      · apply Installs.forIn_member (destination := fun entry => index.node selected (index.enumBase + entry.2)) (row := (entry,offset))
        · exact enumCover selected
        · intro row graph
          rcases row with ⟨entry,position⟩
          dsimp only [enumBody]
          rfl
        · intro row
          rcases row with ⟨entry,position⟩
          dsimp only [enumBody]
          repeat first
            | exact put_installs _ _
            | (apply Installs.bind_left (put_installs _ _); intro unit; exact CoversGraph.pure _)
            | (apply Installs.bind_right _; intro value)
            | (simp only [pure_bind,bind_pure])
            | split
        · exact member
      · intro unit
        repeat first
          | exact CoversGraph.pure _
          | (apply CoversGraph.bind (typeLoop _); intro unit)
          | (apply CoversGraph.bind (structLoop _); intro unit)
          | (apply CoversGraph.bind (enumLoop _); intro unit)
          | (apply CoversGraph.bind (closureLoop _); intro unit)
    · obtain ⟨entry,offset,same,member⟩ := closureRow
      subst position
      dsimp only [modeBody]
      apply Installs.bind_right _
      intro unit
      apply Installs.bind_right _
      intro unit
      apply Installs.bind_right _
      intro unit
      apply Installs.bind_left
      · apply Installs.forIn_member (destination := fun entry => index.node selected (index.closureBase + entry.2)) (row := (entry,offset))
        · exact closureCover selected
        · intro row graph
          rcases row with ⟨entry,position⟩
          dsimp only [closureBody]
          split <;> rfl
        · intro row
          rcases row with ⟨entry,position⟩
          dsimp only [closureBody]
          repeat first
            | exact put_installs _ _
            | (apply Installs.bind_left (put_installs _ _); intro unit; exact CoversGraph.pure _)
            | (apply Installs.bind_right _; intro value)
            | (simp only [pure_bind,bind_pure])
            | split
        · exact member
      · intro unit
        repeat first
          | exact CoversGraph.pure _
          | (apply CoversGraph.bind (typeLoop _); intro unit)
          | (apply CoversGraph.bind (structLoop _); intro unit)
          | (apply CoversGraph.bind (enumLoop _); intro unit)
          | (apply CoversGraph.bind (closureLoop _); intro unit)
  have installed : Installs (index.node mode position) (forIn [Mode.shape, Mode.execution] () modeBody) := by
    apply Installs.forIn_member (destination := fun selected => index.node selected position) (row := mode)
    · exact modeCover
    · intro selected graph
      dsimp only [modeBody]
      rfl
    · exact modeWrites
    · cases mode <;> simp
  have whole : Installs (index.node mode position) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind,bind_pure]
    apply Installs.bind_left
    · exact installed
    · intro unit
      exact CoversGraph.bind (put_covers _ _) (fun _ => put_covers _ _)
  exact whole _


private theorem numbered_exists {α : Type} (rows : List α) (position : Nat) (inside : position < rows.length) :
    ∃ entry, (entry,position) ∈ numbered rows := by
  refine ⟨rows.get ⟨position,inside⟩, (numbered_member_iff_get _ _ _).mpr ?_⟩
  exact CompilerCompat.listGet?_eq_some.mpr ⟨inside,rfl⟩

private theorem build_source_present (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index)
    (mode : Mode) (position : Nat) (inside : position < index.count) :
    (build index facts).Present (index.node mode position) := by
  apply build_rows_present
  by_cases inTypes : position < index.structBase
  · apply Or.inl
    apply numbered_exists
    simpa only [Index.structBase,ready.types] using inTypes
  · apply Or.inr
    by_cases inStructs : position < index.enumBase
    · apply Or.inl
      have bound : position - index.structBase < index.source.structs.length := by
        have sizes := ready.structs
        unfold Index.enumBase at inStructs
        omega
      obtain ⟨entry,member⟩ := numbered_exists index.source.structs _ bound
      exact ⟨entry,position - index.structBase,by omega,member⟩
    · apply Or.inr
      by_cases inEnums : position < index.closureBase
      · apply Or.inl
        have bound : position - index.enumBase < index.source.enums.length := by
          have sizes := ready.enums
          unfold Index.closureBase at inEnums
          omega
        obtain ⟨entry,member⟩ := numbered_exists index.source.enums _ bound
        exact ⟨entry,position - index.enumBase,by omega,member⟩
      · apply Or.inr
        have bound : position - index.closureBase < index.source.closures.length := by
          have sizes := ready.closures
          unfold Index.count at inside
          omega
        obtain ⟨entry,member⟩ := numbered_exists index.source.closures _ bound
        exact ⟨entry,position - index.closureBase,by omega,member⟩

private theorem build_complete (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    (build index facts).Complete := by
  have coverage := buildProgram_covers index facts ({ count := globalClosures index + 1 } : Graph)
  apply coverage.complete_with_reserved
  intro node inside
  change node < globalClosures index + 1 at inside
  by_cases sourceNode : node < 2 * index.count
  · by_cases shape : node < index.count
    · have present := build_source_present index facts ready .shape node shape
      have destination : index.node .shape node = node := by
        change 0 + node = node
        exact Nat.zero_add node
      rw [destination] at present
      exact present
    · have present := build_source_present index facts ready .execution (node - index.count) (by omega)
      have destination : index.node .execution (node - index.count) = node := by
        change index.count + (node - index.count) = node
        omega
      rw [destination] at present
      exact present
  · have validators := build_validators_present index facts
    have either : node = globalTuples index ∨ node = globalClosures index := by
      unfold globalClosures globalTuples at *
      omega
    rcases either with same | same
    · rw [same]; exact validators.1
    · rw [same]; exact validators.2

/-- Every source preparation installs an equation at every reserved or allocated
node, including malformed or cyclic sources whose evaluations may refuse. -/
theorem prepare_complete (source : Environment) : (prepare source).graph.Complete :=
  build_complete (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) (indexReady source)

private theorem build_reference (index : Index) (facts : NatIndexTree Unit)
    (ready : IndexReady index) (roots : RootReady index) : ReferenceState index (build index facts) := by
  let lower := globalClosures index + 1
  have install : ∀ (node : Nat), node < lower → ∀ equation,
      (∀ graph, ReferenceState index graph → StepsIn (fun child => child < graph.count) equation.steps) →
      PreservesState (ReferenceState index) (put node equation) := by
    intro node reserved equation safe graph valid
    exact ⟨put_scalar_state _ _ node reserved equation graph valid.1,
      valid.2.insert graph.count (Nat.le_refl _) node equation (safe graph valid)⟩
  have program : PreservesState (ReferenceState index) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind,bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry,position⟩
        have inside := reserved_type index ready mode entry position member
        cases entry with
        | none =>
          apply PreservesState.bind (install _ inside _ (fun _ _ => Equation.references_done _ _))
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsReferenceEquation.install_yield index _ inside _ (copyCompiled_reference index roots mode ty)
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition,position⟩
          have inside := reserved_struct index ready mode definition position member
          exact BuildsReferenceEquation.install_yield index _ inside _ (structEquation_reference index roots mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition,position⟩
            have inside := reserved_enum index ready mode definition position member
            exact BuildsReferenceEquation.install_yield index _ inside _ (enumEquation_reference index roots mode definition facts)
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition,position⟩
              have inside := reserved_closure index ready mode definition position member
              split
              · exact BuildsReferenceEquation.install_yield index _ inside _ (closureEquation_reference index roots position definition)
              · apply PreservesState.bind (install _ inside _ (fun _ _ => Equation.references_done _ _))
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      have tupleInside : globalTuples index < lower := by
        change globalTuples index < globalClosures index + 1
        unfold globalClosures
        omega
      have closureInside : globalClosures index < lower := Nat.lt_succ_self _
      apply PreservesState.bind
      · apply install _ tupleInside
        intro graph valid
        exact (tupleValidation_references index index.source.tupleLayouts).mono
          (fun _ inside => Nat.lt_of_lt_of_le inside valid.1.2.1)
      · intro unit
        apply install _ closureInside
        intro graph valid
        exact (closureValidation_references index index.source.closureLayouts).mono
          (fun _ inside => Nat.lt_of_lt_of_le inside valid.1.2.1)
  exact program { count := lower }
    ⟨⟨Graph.Bounded.empty lower,Nat.le_refl _,Graph.ScalarInvariant.empty _ _ _⟩,Graph.ReferenceBounds.empty lower⟩

/-- All actual source preparation installs equations whose child references
remain below the final allocation frontier, including refusing/cyclic sources. -/
theorem prepare_references (source : Environment) : (prepare source).graph.ReferenceBounds :=
  (build_reference (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
    (indexReady source) (rootReady source)).2

private theorem build_storage (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    StorageState (globalClosures index + 1) (build index facts) := by
  let lower := globalClosures index + 1
  have program : PreservesState (StorageState lower) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        have inside := reserved_type index ready mode entry position member
        cases entry with
        | none =>
          apply PreservesState.bind (put_storage lower _ inside _
            (fun graph valid => (Equation.StorageGuarded.failed _).rule lower graph))
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsStorageEquation.install_yield _ inside _
            (BuildsStorageEquation.bind (compileTy_storage lower index mode ty)
              (fun child => copyRoot_storage lower child))
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          have inside := reserved_struct index ready mode definition position member
          exact BuildsStorageEquation.install_yield _ inside _ (structEquation_storage lower index mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            have inside := reserved_enum index ready mode definition position member
            exact BuildsStorageEquation.install_yield _ inside _ (enumEquation_storage lower index mode definition facts)
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              have inside := reserved_closure index ready mode definition position member
              split
              · exact BuildsStorageEquation.install_yield _ inside _ (closureEquation_storage lower index position definition)
              · apply PreservesState.bind (put_storage lower _ inside _
                  (fun graph valid => (Equation.StorageGuarded.failed _).rule lower graph))
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      have tupleInside : globalTuples index < lower := by
        change globalTuples index < globalClosures index + 1
        unfold globalClosures
        omega
      have closureInside : globalClosures index < lower := Nat.lt_succ_self _
      apply PreservesState.bind (put_storage lower _ tupleInside _
        (fun graph valid => (Equation.StorageGuarded.unit _).rule lower graph))
      intro unit
      exact put_storage lower _ closureInside _
        (fun graph valid => (Equation.StorageGuarded.unit _).rule lower graph)
  exact program { count := lower }
    ⟨Graph.Bounded.empty lower, Nat.le_refl lower, Graph.StorageInvariant.empty lower lower⟩

/-- Preparation establishes direct and per-variant storage rules for every
 actual source equation, including forward references and refusing rows. -/
theorem prepare_storage (source : Environment) :
    (prepare source).graph.StorageInvariant (2 * (prepare source).index.count + 2) :=
  (build_storage (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
    (indexReady source)).2.2

theorem RootCompilation.preserves_storage {lower : Nat} {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (bounded : before.Bounded) (frontier : lower ≤ before.count)
    (safe : before.StorageInvariant lower) : after.StorageInvariant lower := by
  have kept := compileTy_storage lower index mode ty before ⟨bounded, frontier, safe⟩
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at kept
  exact kept.2.2

/-- Actual root-cache hits, memo hits and fresh compilation preserve the
 storage invariant and justify the returned value in the output graph. -/
theorem Session.query_preserves_storage (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (safe : session.graph.StorageInvariant (2 * session.index.count + 2))
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.StorageInvariant (2 * next.index.count + 2) ∧ StorageGeometry value := by
  rcases session.query_selection mode ty value next valid run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have selected : graph.StorageInvariant (2 * session.index.count + 2) := by
    cases chosen with
    | cached hit => exact safe
    | compiled graph compiled => exact compiled.preserves_storage valid.1.1 valid.1.2 safe
  constructor
  · rw [indexSame, graphSame]; exact selected
  · exact derived.satisfies_contextual selected.contextual

private theorem add_power_alignment (equation : Equation) (safe : equation.PowerAlignmentRule 0) :
    PreservesState Graph.PowerAlignmentInvariant (add equation) := by
  intro graph valid
  exact valid.insert graph.count equation (safe.reowner (fun _ good => good))

private theorem put_power_alignment (node : Nat) (equation : Equation) (safe : equation.PowerAlignmentRule 0) :
    PreservesState Graph.PowerAlignmentInvariant (put node equation) := by
  intro graph valid
  exact valid.insert node equation (safe.reowner (fun _ good => good))

private theorem failed_power_alignment (error : Error) :
    PreservesState Graph.PowerAlignmentInvariant (failed error) :=
  add_power_alignment _ (Equation.PowerAlignmentRule.failed 0 error)

private theorem leaves_power_alignment (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState Graph.PowerAlignmentInvariant
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun _ valid => valid

private theorem addScalar_power_alignment (result : Result Summary)
    (safe : ∀ value, result = .ok value → BoundedAlignment value) :
    PreservesState Graph.PowerAlignmentInvariant (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_power_alignment error
  | ok value =>
    apply PreservesState.bind (PreservesState.get Graph.PowerAlignmentInvariant)
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_power_alignment _ (Equation.PowerAlignmentRule.done 0 _ safe))
      intro node
      apply PreservesState.bind (leaves_power_alignment (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _

private theorem compileTuple_power_alignment (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState Graph.PowerAlignmentInvariant (compileTypes index mode fields))
    (shapeSafe : PreservesState Graph.PowerAlignmentInvariant (compileTypes index .shape fields)) :
    PreservesState Graph.PowerAlignmentInvariant (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_power_alignment _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_power_alignment
       repeat first
         | exact Equation.PowerAlignmentRule.failed 0 _
         | exact Equation.PowerAlignmentRule.canonicalFields 0 _ _ _ _
         | exact Equation.PowerAlignmentRule.declaredFields 0 _ _ _ _ _ _ _ _
         | apply Equation.PowerAlignmentRule.sequence 0
         | split)
    | split

mutual
  private theorem compileTy_power_alignment (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState Graph.PowerAlignmentInvariant (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_power_alignment _
    · split
      · rename_i result found
        exact addScalar_power_alignment result (fun value success => ⟨scalar_word mode index.source ty result value found success,
          (scalar_admissible mode index.source ty result value found success).power_alignment index.source.model⟩)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact failed_power_alignment _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_power_alignment _
            | (apply PreservesState.bind (compileTy_power_alignment index mode element)
               intro child
               exact add_power_alignment _ (Equation.PowerAlignmentRule.scaled 0 mode count child))
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_power_alignment index mode fields
            (compileTypes_power_alignment index mode fields) (compileTypes_power_alignment index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_power_alignment _
          | exact add_power_alignment _ (Equation.PowerAlignmentRule.scaled 0 _ _ _)
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_power_alignment (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState Graph.PowerAlignmentInvariant (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_power_alignment index mode first)
      intro child
      apply PreservesState.bind (compileTypes_power_alignment index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def BuildsPowerEquation (action : Build Equation) : Prop :=
  ∀ graph, graph.PowerAlignmentInvariant →
    (action graph).2.PowerAlignmentInvariant ∧ (action graph).1.PowerAlignmentRule 0

private theorem BuildsPowerEquation.pure (equation : Equation)
    (safe : equation.PowerAlignmentRule 0) :
    BuildsPowerEquation (pure equation) := fun _ valid => ⟨valid, safe⟩

private theorem BuildsPowerEquation.bind {α : Type} {action : Build α} {next : α → Build Equation}
    (first : PreservesState Graph.PowerAlignmentInvariant action)
    (later : ∀ value, BuildsPowerEquation (next value)) : BuildsPowerEquation (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (first graph valid)

private theorem BuildsPowerEquation.install_yield {α : Type} {action : Build Equation}
    (node : Nat) (result : α) (safe : BuildsPowerEquation action) :
    PreservesState Graph.PowerAlignmentInvariant (do put node (← action); Pure.pure result) := by
  intro graph valid
  have built := safe graph valid
  exact put_power_alignment node (action graph).1 built.2 (action graph).2 built.1

private theorem copyRoot_power_alignment (child : Nat) : BuildsPowerEquation (do
    let graph ← get
    pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  refine ⟨valid, ?_⟩
  change ((graph.nodes.find child).getD (alias child)).PowerAlignmentRule 0
  cases found : graph.nodes.find child with
  | none => exact Equation.IndexedRule.alias 0 child (fun _ safe => safe)
  | some equation => exact (valid child equation found).reowner (fun _ safe => safe)

private theorem structEquation_power_alignment (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsPowerEquation (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsPowerEquation.pure; exact (Equation.PowerAlignmentRule.failed 0 _))
    | (apply BuildsPowerEquation.pure; exact (Equation.PowerAlignmentRule.canonicalFields 0 _ _ _ _))
    | (apply BuildsPowerEquation.pure; exact (Equation.PowerAlignmentRule.declaredFields 0 _ _ _ _ _ _ _ _))
    | (apply BuildsPowerEquation.bind (compileTypes_power_alignment _ _ _); intro children)
    | split

private theorem closureEquation_power_alignment (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsPowerEquation (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsPowerEquation.pure; exact (Equation.PowerAlignmentRule.failed 0 _))
    | (apply BuildsPowerEquation.pure; exact (Equation.PowerAlignmentRule.declaredFields 0 _ _ _ _ _ _ _ _))
    | (apply BuildsPowerEquation.bind (compileTypes_power_alignment _ _ _); intro children)
    | split

private theorem enumNodes_power_alignment (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState Graph.PowerAlignmentInvariant (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_power_alignment _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_power_alignment _ (Equation.PowerAlignmentRule.done 0 _
           (by intro value same; cases same; exact BoundedAlignment.unit)))
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private theorem variantEquation_power_alignment (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).PowerAlignmentRule 0 := by
  repeat first
    | exact Equation.PowerAlignmentRule.failed 0 _
    | exact Equation.PowerAlignmentRule.canonicalFields 0 _ _ _ _
    | exact Equation.PowerAlignmentRule.declaredFields 0 _ _ _ _ _ _ _ _
    | split

private theorem enumRoot_power_alignment (index : Index) (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
      Equation.done (.error Error.scalarTarget)
    else enumEquation mode definition uninhabited variants).PowerAlignmentRule 0 := by
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact Equation.PowerAlignmentRule.failed 0 _
  · exact Equation.PowerAlignmentRule.enumeration 0 _ _ _ _

private theorem build_power_alignment (index : Index) (facts : NatIndexTree Unit) :
    (build index facts).PowerAlignmentInvariant := by
  have program : PreservesState Graph.PowerAlignmentInvariant (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_power_alignment _ _ (Equation.PowerAlignmentRule.failed 0 _))
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsPowerEquation.install_yield (index.node mode position) _
            (BuildsPowerEquation.bind (compileTy_power_alignment index mode ty) (fun child => copyRoot_power_alignment child))
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          exact BuildsPowerEquation.install_yield (index.node mode (index.structBase + position)) _
            (structEquation_power_alignment index mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row variantMember variants
              rcases row with ⟨variant, variantIndex⟩
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind (enumNodes_power_alignment _ _ _ _); intro children)
                | (apply PreservesState.bind
                     (add_power_alignment _ (variantEquation_power_alignment mode definition _ variantIndex)); intro node)
                | (simp only [pure_bind])
                | split
            · intro variants
              apply PreservesState.bind (put_power_alignment (index.node mode (index.enumBase + position)) _
                (enumRoot_power_alignment index mode definition _ _))
              intro unit
              exact PreservesState.pure _ _
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              split
              · exact BuildsPowerEquation.install_yield (index.node mode (index.closureBase + position)) _
                  (closureEquation_power_alignment index position definition)
              · apply PreservesState.bind (put_power_alignment _ _ (Equation.PowerAlignmentRule.failed 0 _))
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      apply PreservesState.bind (put_power_alignment _ _ (Equation.PowerAlignmentRule.unit 0 _))
      intro unit
      exact put_power_alignment _ _ (Equation.PowerAlignmentRule.unit 0 _)
  exact program _ (Graph.IndexedInvariant.empty _ _)

/-- Preparation establishes power-of-two alignment and aggregate-size
 divisibility for actual equations, including forward nominal references. -/
theorem prepare_power_alignment (source : Environment) : (prepare source).graph.PowerAlignmentInvariant :=
  build_power_alignment (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))

theorem RootCompilation.preserves_power_alignment {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (safe : before.PowerAlignmentInvariant) : after.PowerAlignmentInvariant := by
  have kept := compileTy_power_alignment index mode ty before safe
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at kept
  exact kept

theorem Session.query_preserves_power_alignment (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (safe : session.graph.PowerAlignmentInvariant)
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.PowerAlignmentInvariant ∧ BoundedAlignment value := by
  rcases session.query_selection mode ty value next valid run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have selected : graph.PowerAlignmentInvariant := by
    cases chosen with
    | cached hit => exact safe
    | compiled graph compiled => exact compiled.preserves_power_alignment safe
  constructor
  · rw [graphSame]; exact selected
  · exact derived.satisfies_at selected

private def FieldAlignmentState (lower : Nat) (graph : Graph) : Prop :=
  graph.Bounded ∧ lower ≤ graph.count ∧ graph.FieldAlignmentInvariant lower

private theorem add_field_alignment (lower : Nat) (equation : Equation)
    (guarded : ∀ graph, FieldAlignmentState lower graph → equation.FieldAlignmentRule lower graph) :
    PreservesState (FieldAlignmentState lower) (add equation) := by
  intro graph state
  exact ⟨state.1.allocate equation, Nat.le_trans state.2.1 (Nat.le_succ _),
    state.2.2.allocate state.1 equation (guarded graph state)⟩

private theorem add_field_alignment_guarded (lower : Nat) (equation : Equation) (guarded : equation.FieldAlignmentGuarded) :
    PreservesState (FieldAlignmentState lower) (add equation) :=
  add_field_alignment lower equation (fun graph state => guarded.rule lower graph)

private theorem failed_field_alignment (lower : Nat) (error : Error) :
    PreservesState (FieldAlignmentState lower) (failed error) :=
  add_field_alignment_guarded lower _ (Equation.FieldAlignmentGuarded.failed error)

private theorem put_field_alignment (lower node : Nat) (inside : node < lower) (equation : Equation)
    (guarded : ∀ graph, FieldAlignmentState lower graph → equation.FieldAlignmentRule lower graph) :
    PreservesState (FieldAlignmentState lower) (put node equation) := by
  intro graph state
  exact ⟨state.1.put node (Nat.lt_of_lt_of_le inside state.2.1) equation, state.2.1,
    state.2.2.put_below node inside equation (guarded graph state)⟩

private theorem leaves_field_alignment (lower : Nat) (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState (FieldAlignmentState lower)
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun graph state => ⟨state.1, state.2.1, state.2.2.leaves _⟩

private theorem addScalar_field_alignment (lower : Nat) (result : Result Summary)
    (safe : ∀ value, result = .ok value → FieldAlignmentSummary value) :
    PreservesState (FieldAlignmentState lower) (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_field_alignment lower error
  | ok value =>
    apply PreservesState.bind (PreservesState.get (FieldAlignmentState lower))
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_field_alignment_guarded lower _ (Equation.FieldAlignmentGuarded.done _ safe))
      intro node
      apply PreservesState.bind (leaves_field_alignment lower (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _

set_option maxHeartbeats 1000000 in
private theorem compileTuple_field_alignment (lower : Nat) (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState (FieldAlignmentState lower) (compileTypes index mode fields))
    (shapeSafe : PreservesState (FieldAlignmentState lower) (compileTypes index .shape fields)) :
    PreservesState (FieldAlignmentState lower) (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_field_alignment lower _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_field_alignment_guarded lower
       repeat first
         | exact Equation.FieldAlignmentGuarded.failed _
         | exact Equation.FieldAlignmentGuarded.canonicalFields _ _ _ _
         | exact Equation.FieldAlignmentGuarded.declaredFields _ _ _ _ _ _ _ _ (.inl rfl)
         | apply Equation.FieldAlignmentGuarded.sequence
         | split)
    | split

mutual
  private theorem compileTy_field_alignment (lower : Nat) (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState (FieldAlignmentState lower) (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_field_alignment lower _
    · split
      · rename_i result found
        exact addScalar_field_alignment lower result (fun value success =>
          (scalar_admissible mode index.source ty result value found success).field_alignment index.source.model)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact failed_field_alignment lower _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_field_alignment lower _
            | (apply PreservesState.bind (compileTy_field_alignment lower index mode element)
               intro child
               exact add_field_alignment_guarded lower _ (Equation.FieldAlignmentGuarded.scaled mode count child))
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_field_alignment lower index mode fields
            (compileTypes_field_alignment lower index mode fields) (compileTypes_field_alignment lower index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_field_alignment lower _
          | exact add_field_alignment_guarded lower _ (Equation.FieldAlignmentGuarded.scaled _ _ _)
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_field_alignment (lower : Nat) (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState (FieldAlignmentState lower) (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_field_alignment lower index mode first)
      intro child
      apply PreservesState.bind (compileTypes_field_alignment lower index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def BuildsFieldAlignmentEquation (lower : Nat) (action : Build Equation) : Prop :=
  ∀ graph, FieldAlignmentState lower graph →
    FieldAlignmentState lower (action graph).2 ∧ (action graph).1.FieldAlignmentRule lower (action graph).2

private theorem BuildsFieldAlignmentEquation.pure (lower : Nat) (equation : Equation)
    (safe : ∀ graph, equation.FieldAlignmentRule lower graph) :
    BuildsFieldAlignmentEquation lower (pure equation) := fun graph valid => ⟨valid, safe graph⟩

private theorem BuildsFieldAlignmentEquation.bind {lower : Nat} {α : Type} {action : Build α} {next : α → Build Equation}
    (first : PreservesState (FieldAlignmentState lower) action)
    (later : ∀ value, BuildsFieldAlignmentEquation lower (next value)) : BuildsFieldAlignmentEquation lower (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (first graph valid)

private theorem BuildsFieldAlignmentEquation.install_yield {lower : Nat} {α : Type} {action : Build Equation}
    (node : Nat) (inside : node < lower) (result : α) (safe : BuildsFieldAlignmentEquation lower action) :
    PreservesState (FieldAlignmentState lower) (do put node (← action); Pure.pure result) := by
  intro graph valid
  have built := safe graph valid
  exact ⟨built.1.1.put node (Nat.lt_of_lt_of_le inside built.1.2.1) _, built.1.2.1,
    built.1.2.2.put_below node inside _ built.2⟩

private theorem copyRoot_field_alignment (lower child : Nat) : BuildsFieldAlignmentEquation lower (do
    let graph ← get
    pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  refine ⟨valid, ?_⟩
  change ((graph.nodes.find child).getD (alias child)).FieldAlignmentRule lower graph
  cases found : graph.nodes.find child with
  | none => exact Equation.FieldAlignmentRule.alias lower graph child
  | some equation => exact valid.2.2 child equation found

private theorem structEquation_field_alignment (lower : Nat) (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsFieldAlignmentEquation lower (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsFieldAlignmentEquation.pure; intro graph; exact (Equation.FieldAlignmentGuarded.failed _).rule _ _)
    | (apply BuildsFieldAlignmentEquation.pure; intro graph; exact (Equation.FieldAlignmentGuarded.canonicalFields _ _ _ _).rule _ _)
    | (apply BuildsFieldAlignmentEquation.pure; intro graph; exact (Equation.FieldAlignmentGuarded.declaredFields _ _ _ _ _ _ _ _
        (by first | exact Or.inl rfl | exact Or.inr ((@Bool.and_eq_true_iff _ _).mp (by assumption)).1)).rule _ _)
    | (apply BuildsFieldAlignmentEquation.bind (compileTypes_field_alignment lower _ _ _); intro children)
    | split

private theorem closureEquation_field_alignment (lower : Nat) (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsFieldAlignmentEquation lower (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsFieldAlignmentEquation.pure; intro graph; exact (Equation.FieldAlignmentGuarded.failed _).rule _ _)
    | (apply BuildsFieldAlignmentEquation.pure; intro graph; exact (Equation.FieldAlignmentGuarded.declaredFields _ _ _ _ _ _ _ _ (.inl rfl)).rule _ _)
    | (apply BuildsFieldAlignmentEquation.bind (compileTypes_field_alignment lower _ _ _); intro children)
    | split

private theorem enumNodes_field_alignment (lower : Nat) (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState (FieldAlignmentState lower) (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_field_alignment lower _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_field_alignment_guarded lower _ (Equation.FieldAlignmentGuarded.done _
           (by intro value same; cases same; exact FieldAlignmentSummary.empty rfl rfl)))
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private def RowAlignmentCertificates (lower : Nat) (definition : EnumDef) (nodes : List Nat) (graph : Graph) : Prop :=
  graph.VariantAlignmentCertificates (definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.align)) nodes ∧
    ∀ child, child ∈ nodes → lower ≤ child

private theorem RowAlignmentCertificates.empty (lower : Nat) (definition : EnumDef) (graph : Graph) :
    RowAlignmentCertificates lower definition [] graph := by
  constructor
  · intro child impossible; cases impossible
  · intro child impossible; cases impossible

private theorem RowAlignmentCertificates.weaken {lower : Nat} {definition : EnumDef} {nodes : List Nat}
    {before after : Graph} (safe : RowAlignmentCertificates lower definition nodes before)
    (extended : before.Extends after) : RowAlignmentCertificates lower definition nodes after :=
  ⟨safe.1.weaken extended, safe.2⟩

private theorem variantEquation_field_alignment (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).FieldAlignmentGuarded := by
  repeat first
    | exact Equation.FieldAlignmentGuarded.failed _
    | exact Equation.FieldAlignmentGuarded.canonicalFields _ _ _ _
    | exact Equation.FieldAlignmentGuarded.declaredFields _ _ _ _ _ _ _ _ (.inl rfl)
    | split


private theorem variantEquation_row_alignment (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).VariantAlignmentGuarded (definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.align)) := by
  cases authored : definition.layout with
  | none =>
    simp only [authored, Option.map]
    exact Equation.VariantAlignmentGuarded.canonicalFields mode definition.id.index children
  | some descriptor =>
    simp only [authored, Option.map]
    repeat first
      | exact Equation.VariantAlignmentGuarded.failed _ _
      | exact Equation.VariantAlignmentGuarded.declaredFields _ _ _ _ _
      | split

private theorem variantStep_field_alignment (lower : Nat) (definition : EnumDef)
    (action : Build (List (Ty × Nat))) (equations : List (Ty × Nat) → Equation)
    (preserved : PreservesState (FieldAlignmentState lower) action) (grows : PreservesGraph action)
    (guarded : ∀ children, (equations children).FieldAlignmentGuarded)
    (parents : ∀ children, (equations children).VariantAlignmentGuarded (definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.align)))
    (nodes : List Nat) (graph : Graph)
    (valid : FieldAlignmentState lower graph ∧ RowAlignmentCertificates lower definition nodes graph) :
    let result := (do
      let children ← action
      let node ← add (equations children)
      pure (ForInStep.yield (node :: nodes))) graph
    FieldAlignmentState lower result.2 ∧ RowAlignmentCertificates lower definition
      (match result.1 with | .done value | .yield value => value) result.2 := by
  let before := (action graph).2
  let equation := equations (action graph).1
  let after : Graph := { before with nodes := before.nodes.insert before.count equation, count := before.count + 1 }
  have state : FieldAlignmentState lower before := preserved graph valid.1
  have certificates : RowAlignmentCertificates lower definition nodes before :=
    valid.2.weaken (grows graph valid.1.1).equations
  have added : FieldAlignmentState lower after := add_field_alignment_guarded lower equation (guarded _) before state
  change FieldAlignmentState lower after ∧ RowAlignmentCertificates lower definition (before.count :: nodes) after
  refine ⟨added, ?_⟩
  refine ⟨certificates.1.allocate state.1 equation (parents _), ?_⟩
  intro child member
  cases member with
  | head => exact state.2.1
  | tail _ member => exact certificates.2 child member


private theorem enumVariants_field_alignment (lower : Nat) (index : Index) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat))
    (nodes : List Nat) (graph : Graph)
    (valid : FieldAlignmentState lower graph ∧ RowAlignmentCertificates lower definition nodes graph) :
    let result := (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) graph
    FieldAlignmentState lower result.2 ∧ RowAlignmentCertificates lower definition result.1 result.2 := by
  apply forIn_accumulator (fun nodes graph => FieldAlignmentState lower graph ∧ RowAlignmentCertificates lower definition nodes graph)
    rows nodes _ ?_ graph valid
  intro row member acc before state
  rcases row with ⟨variant, variantIndex⟩
  dsimp only
  by_cases skipped : selected.any (fun active => variantIndex != active) = true
  all_goals simp only [skipped, ite_true, ite_false]
  · apply variantStep_field_alignment lower definition _ _
    · exact PreservesState.pure _ _
    · exact PreservesGraph.pure _
    · intro children
      exact variantEquation_field_alignment mode definition children variantIndex
    · intro children
      exact variantEquation_row_alignment mode definition children variantIndex
    · exact state
  · apply variantStep_field_alignment lower definition _ _
    · exact enumNodes_field_alignment lower index mode definition.layout.isSome variant.fields
    · exact enumNodes_preserves index mode definition.layout.isSome variant.fields
    · intro children
      exact variantEquation_field_alignment mode definition children variantIndex
    · intro children
      exact variantEquation_row_alignment mode definition children variantIndex
    · exact state



private theorem enumEquation_field_alignment (lower : Nat) (index : Index) (mode : Mode)
    (definition : EnumDef) (facts : NatIndexTree Unit) :
    BuildsFieldAlignmentEquation lower (do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := match definition.layout with
        | some descriptor => match descriptor.encoding with
          | .singleInhabited selected =>
            if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
          | _ => none
        | none => none
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      pure equation) := by
  intro graph valid
  let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
  let selected := match definition.layout with
    | some descriptor => match descriptor.encoding with
      | .singleInhabited selected =>
        if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
      | _ => none
    | none => none
  let variantsAction : Build (List Nat) := do
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      -- Skip physical children only after checking the actual structural
      -- facts and all inactive offset rows. Logical rows retain their IDs.
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    pure variants
  have built := enumVariants_field_alignment lower index mode definition selected
    (numbered definition.variants) [] graph ⟨valid, RowAlignmentCertificates.empty lower definition graph⟩
  change FieldAlignmentState lower (variantsAction graph).2 ∧
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)
      then Equation.done (.error Error.scalarTarget)
      else enumEquation mode definition uninhabited (variantsAction graph).1.reverse).FieldAlignmentRule lower (variantsAction graph).2
  refine ⟨built.1, ?_⟩
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact (Equation.FieldAlignmentGuarded.failed _).rule _ _
  · apply Equation.FieldAlignmentRule.enumeration lower _ mode definition uninhabited _ built.2.1.reverse
    intro child member
    exact built.2.2 child ((storage_member_reverse child (variantsAction graph).1).mp member)

private theorem build_field_alignment (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    FieldAlignmentState (globalClosures index + 1) (build index facts) := by
  let lower := globalClosures index + 1
  have program : PreservesState (FieldAlignmentState lower) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        have inside := reserved_type index ready mode entry position member
        cases entry with
        | none =>
          apply PreservesState.bind (put_field_alignment lower _ inside _
            (fun graph valid => (Equation.FieldAlignmentGuarded.failed _).rule lower graph))
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsFieldAlignmentEquation.install_yield _ inside _
            (BuildsFieldAlignmentEquation.bind (compileTy_field_alignment lower index mode ty)
              (fun child => copyRoot_field_alignment lower child))
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          have inside := reserved_struct index ready mode definition position member
          exact BuildsFieldAlignmentEquation.install_yield _ inside _ (structEquation_field_alignment lower index mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            have inside := reserved_enum index ready mode definition position member
            exact BuildsFieldAlignmentEquation.install_yield _ inside _ (enumEquation_field_alignment lower index mode definition facts)
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              have inside := reserved_closure index ready mode definition position member
              split
              · exact BuildsFieldAlignmentEquation.install_yield _ inside _ (closureEquation_field_alignment lower index position definition)
              · apply PreservesState.bind (put_field_alignment lower _ inside _
                  (fun graph valid => (Equation.FieldAlignmentGuarded.failed _).rule lower graph))
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      have tupleInside : globalTuples index < lower := by
        change globalTuples index < globalClosures index + 1
        unfold globalClosures
        omega
      have closureInside : globalClosures index < lower := Nat.lt_succ_self _
      apply PreservesState.bind (put_field_alignment lower _ tupleInside _
        (fun graph valid => (Equation.FieldAlignmentGuarded.unit _).rule lower graph))
      intro unit
      exact put_field_alignment lower _ closureInside _
        (fun graph valid => (Equation.FieldAlignmentGuarded.unit _).rule lower graph)
  exact program { count := lower }
    ⟨Graph.Bounded.empty lower, Nat.le_refl lower, Graph.PersistentInvariant.empty Graph.PowerAlignmentInvariant FieldAlignmentSummary lower lower⟩


/-- Exact source variant equations establish field and row alignment through
preparation; the separate aggregate-power invariant supplies child authenticity. -/
theorem prepare_field_alignment (source : Environment) :
    (prepare source).graph.FieldAlignmentInvariant (2 * (prepare source).index.count + 2) :=
  (build_field_alignment (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))
    (indexReady source)).2.2

theorem RootCompilation.preserves_field_alignment {lower : Nat} {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (bounded : before.Bounded) (frontier : lower ≤ before.count)
    (safe : before.FieldAlignmentInvariant lower) : after.FieldAlignmentInvariant lower := by
  have kept := compileTy_field_alignment lower index mode ty before ⟨bounded, frontier, safe⟩
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at kept
  exact kept.2.2

theorem Session.query_preserves_field_alignment (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (powers : session.graph.PowerAlignmentInvariant)
    (safe : session.graph.FieldAlignmentInvariant (2 * session.index.count + 2))
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.FieldAlignmentInvariant (2 * next.index.count + 2) ∧ FieldAlignmentSummary value := by
  rcases session.query_selection mode ty value next valid run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have selected : graph.FieldAlignmentInvariant (2 * session.index.count + 2) ∧ graph.PowerAlignmentInvariant := by
    cases chosen with
    | cached hit => exact ⟨safe, powers⟩
    | compiled graph compiled =>
      exact ⟨compiled.preserves_field_alignment valid.1.1 valid.1.2 safe, compiled.preserves_power_alignment powers⟩
  constructor
  · rw [indexSame, graphSame]; exact selected.1
  · exact derived.satisfies_contextual (selected.1.contextual selected.2)

private theorem add_encoding (equation : Equation) (safe : equation.InvariantRule EnumEncodingGeometry) :
    PreservesState Graph.EncodingInvariant (add equation) := by
  intro graph valid
  exact valid.insert graph.count equation safe

private theorem put_encoding (node : Nat) (equation : Equation)
    (safe : equation.InvariantRule EnumEncodingGeometry) :
    PreservesState Graph.EncodingInvariant (put node equation) := by
  intro graph valid
  exact valid.insert node equation safe

private theorem failed_encoding (error : Error) :
    PreservesState Graph.EncodingInvariant (failed error) :=
  add_encoding _ (Equation.EncodingGuarded.failed error).rule

private theorem leaves_encoding (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState Graph.EncodingInvariant
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun _ valid => valid

private theorem addScalar_encoding (result : Result Summary)
    (safe : ∀ value, result = .ok value → EnumEncodingGeometry value) :
    PreservesState Graph.EncodingInvariant (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_encoding error
  | ok value =>
    apply PreservesState.bind (PreservesState.get Graph.EncodingInvariant)
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_encoding _ (Equation.EncodingGuarded.done _ safe).rule)
      intro node
      apply PreservesState.bind (leaves_encoding (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _


private theorem compileTuple_encoding (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState Graph.EncodingInvariant (compileTypes index mode fields))
    (shapeSafe : PreservesState Graph.EncodingInvariant (compileTypes index .shape fields)) :
    PreservesState Graph.EncodingInvariant (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_encoding _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_encoding
       apply Equation.EncodingGuarded.rule
       repeat first
         | exact Equation.EncodingGuarded.failed _
         | exact Equation.EncodingGuarded.canonicalFields _ _ _ _
         | exact Equation.EncodingGuarded.declaredFields _ _ _ _ _ _ _ _
         | apply Equation.EncodingGuarded.sequence
         | split)
    | split

mutual
  private theorem compileTy_encoding (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState Graph.EncodingInvariant (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_encoding _
    · split
      · rename_i result found
        exact addScalar_encoding result (fun value success => (scalar_admissible mode index.source ty result value found success).enum_encoding_geometry)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact failed_encoding _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_encoding _
            | (apply PreservesState.bind (compileTy_encoding index mode element)
               intro child
               exact add_encoding _ (Equation.EncodingGuarded.scaled mode count child).rule)
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_encoding index mode fields
            (compileTypes_encoding index mode fields) (compileTypes_encoding index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_encoding _
          | exact add_encoding _ (Equation.EncodingGuarded.scaled _ _ _).rule
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_encoding (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState Graph.EncodingInvariant (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_encoding index mode first)
      intro child
      apply PreservesState.bind (compileTypes_encoding index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def BuildsEncodingEquation (action : Build Equation) : Prop :=
  ∀ graph, graph.EncodingInvariant →
    (action graph).2.EncodingInvariant ∧ (action graph).1.InvariantRule EnumEncodingGeometry

private theorem BuildsEncodingEquation.pure (equation : Equation)
    (safe : equation.InvariantRule EnumEncodingGeometry) :
    BuildsEncodingEquation (pure equation) := fun _ valid => ⟨valid, safe⟩

private theorem BuildsEncodingEquation.bind {α : Type} {action : Build α} {next : α → Build Equation}
    (first : PreservesState Graph.EncodingInvariant action)
    (later : ∀ value, BuildsEncodingEquation (next value)) : BuildsEncodingEquation (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (first graph valid)

private theorem BuildsEncodingEquation.install_yield {α : Type} {action : Build Equation}
    (node : Nat) (result : α) (safe : BuildsEncodingEquation action) :
    PreservesState Graph.EncodingInvariant (do put node (← action); Pure.pure result) := by
  intro graph valid
  have built := safe graph valid
  exact put_encoding node (action graph).1 built.2 (action graph).2 built.1

private theorem copyRoot_encoding (child : Nat) : BuildsEncodingEquation (do
    let graph ← get
    pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  refine ⟨valid, ?_⟩
  change ((graph.nodes.find child).getD (alias child)).InvariantRule EnumEncodingGeometry
  cases found : graph.nodes.find child with
  | none => exact .alias child
  | some equation => exact valid child equation found

private theorem structEquation_encoding (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsEncodingEquation (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsEncodingEquation.pure; exact (Equation.EncodingGuarded.failed _).rule)
    | (apply BuildsEncodingEquation.pure; exact (Equation.EncodingGuarded.canonicalFields _ _ _ _).rule)
    | (apply BuildsEncodingEquation.pure; exact (Equation.EncodingGuarded.declaredFields _ _ _ _ _ _ _ _).rule)
    | (apply BuildsEncodingEquation.bind (compileTypes_encoding _ _ _); intro children)
    | split

private theorem closureEquation_encoding (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsEncodingEquation (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsEncodingEquation.pure; exact (Equation.EncodingGuarded.failed _).rule)
    | (apply BuildsEncodingEquation.pure; exact (Equation.EncodingGuarded.declaredFields _ _ _ _ _ _ _ _).rule)
    | (apply BuildsEncodingEquation.bind (compileTypes_encoding _ _ _); intro children)
    | split

private theorem enumNodes_encoding (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState Graph.EncodingInvariant (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_encoding _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_encoding _ (Equation.EncodingGuarded.done _
           (by intro value same; cases same; exact EnumEncodingGeometry.no_enum rfl)).rule)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private theorem variantEquation_encoding (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).EncodingGuarded := by
  repeat first
    | exact Equation.EncodingGuarded.failed _
    | exact Equation.EncodingGuarded.canonicalFields _ _ _ _
    | exact Equation.EncodingGuarded.declaredFields _ _ _ _ _ _ _ _
    | split

private theorem enumRoot_encoding (index : Index) (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
      Equation.done (.error Error.scalarTarget)
    else enumEquation mode definition uninhabited variants).EncodingGuarded := by
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact Equation.EncodingGuarded.failed _
  · exact Equation.EncodingGuarded.enumeration _ _ _ _


private theorem build_encoding (index : Index) (facts : NatIndexTree Unit) :
    (build index facts).EncodingInvariant := by
  have program : PreservesState Graph.EncodingInvariant (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_encoding _ _ (Equation.EncodingGuarded.failed _).rule)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsEncodingEquation.install_yield (index.node mode position) _
            (BuildsEncodingEquation.bind (compileTy_encoding index mode ty) (fun child => copyRoot_encoding child))
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          exact BuildsEncodingEquation.install_yield (index.node mode (index.structBase + position)) _
            (structEquation_encoding index mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row variantMember variants
              rcases row with ⟨variant, variantIndex⟩
              repeat first
                | exact PreservesState.pure _ _
                | (apply PreservesState.bind (enumNodes_encoding _ _ _ _); intro children)
                | (apply PreservesState.bind
                     (add_encoding _ (variantEquation_encoding mode definition _ variantIndex).rule); intro node)
                | (simp only [pure_bind])
                | split
            · intro variants
              apply PreservesState.bind (put_encoding (index.node mode (index.enumBase + position)) _
                (enumRoot_encoding index mode definition _ _).rule)
              intro unit
              exact PreservesState.pure _ _
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              split
              · exact BuildsEncodingEquation.install_yield (index.node mode (index.closureBase + position)) _
                  (closureEquation_encoding index position definition)
              · apply PreservesState.bind (put_encoding _ _ (Equation.EncodingGuarded.failed _).rule)
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      apply PreservesState.bind (put_encoding _ _ (Equation.EncodingGuarded.unit _).rule)
      intro unit
      exact put_encoding _ _ (Equation.EncodingGuarded.unit _).rule
  exact program _ (Graph.SummaryInvariant.empty _ _)

/-- Every prepared equation enforces physical tag/niche checks on success. -/
theorem prepare_encoding (source : Environment) : (prepare source).graph.EncodingInvariant :=
  build_encoding (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))

theorem RootCompilation.preserves_encoding {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (safe : before.EncodingInvariant) : after.EncodingInvariant := by
  have kept := compileTy_encoding index mode ty before safe
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at kept
  exact kept

theorem Session.query_preserves_encoding (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (safe : session.graph.EncodingInvariant)
    (run : session.query mode ty = .ok (value, next)) :
    next.graph.EncodingInvariant ∧ EnumEncodingGeometry value := by
  rcases session.query_selection mode ty value next valid run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have selected : graph.EncodingInvariant := by
    cases chosen with
    | cached hit => exact safe
    | compiled graph compiled => exact compiled.preserves_encoding safe
  constructor
  · rw [graphSame]; exact selected
  · exact derived.satisfies selected

private theorem add_metadata (equation : Equation) (safe : equation.InvariantRule EnumMetadata) :
    PreservesState Graph.MetadataInvariant (add equation) := by
  intro graph valid
  exact valid.insert graph.count equation safe

private theorem put_metadata (node : Nat) (equation : Equation)
    (safe : equation.InvariantRule EnumMetadata) :
    PreservesState Graph.MetadataInvariant (put node equation) := by
  intro graph valid
  exact valid.insert node equation safe

private theorem failed_metadata (error : Error) :
    PreservesState Graph.MetadataInvariant (failed error) :=
  add_metadata _ (Equation.MetadataGuarded.failed error).rule

private theorem leaves_metadata (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState Graph.MetadataInvariant
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) :=
  fun _ valid => valid

private theorem addScalar_metadata (result : Result Summary)
    (safe : ∀ value, result = .ok value → EnumMetadata value) :
    PreservesState Graph.MetadataInvariant (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_metadata error
  | ok value =>
    apply PreservesState.bind (PreservesState.get Graph.MetadataInvariant)
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_metadata _ (Equation.MetadataGuarded.done _ safe).rule)
      intro node
      apply PreservesState.bind (leaves_metadata (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _


private theorem compileTuple_metadata (index : Index) (mode : Mode) (fields : List Ty)
    (modeSafe : PreservesState Graph.MetadataInvariant (compileTypes index mode fields))
    (shapeSafe : PreservesState Graph.MetadataInvariant (compileTypes index .shape fields)) :
    PreservesState Graph.MetadataInvariant (compileTy index mode (.Tuple fields)) := by
  rw [compileTy.eq_def]
  dsimp only [scalar]
  simp only [pure_bind, bind_pure]
  repeat first
    | exact failed_metadata _
    | (apply PreservesState.bind modeSafe; intro children)
    | (apply PreservesState.bind shapeSafe; intro children)
    | (apply add_metadata
       apply Equation.MetadataGuarded.rule
       repeat first
         | exact Equation.MetadataGuarded.failed _
         | exact Equation.MetadataGuarded.canonicalFields _ _ _ _
         | exact Equation.MetadataGuarded.declaredFields _ _ _ _ _ _ _ _
         | apply Equation.MetadataGuarded.sequence
         | split)
    | split

mutual
  private theorem compileTy_metadata (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState Graph.MetadataInvariant (compileTy index mode ty) := by
    rw [compileTy.eq_def]
    dsimp only
    split
    · exact failed_metadata _
    · split
      · rename_i result found
        exact addScalar_metadata result (fun value success => (scalar_admissible mode index.source ty result value found success).enum_metadata)
      · cases ty
        all_goals dsimp only
        all_goals simp only [pure_bind, bind_pure]
        all_goals try exact failed_metadata _
        case Vector count element scalarNone =>
          repeat first
            | exact failed_metadata _
            | (apply PreservesState.bind (compileTy_metadata index mode element)
               intro child
               exact add_metadata _ (Equation.MetadataGuarded.scaled mode count child).rule)
            | split
        case Tuple fields scalarNone =>
          have safe := compileTuple_metadata index mode fields
            (compileTypes_metadata index mode fields) (compileTypes_metadata index .shape fields)
          rw [compileTy.eq_def] at safe
          dsimp only [scalar] at safe
          simp_all only [Bool.false_eq_true, ite_false, pure_bind, bind_pure]
        all_goals repeat first
          | exact failed_metadata _
          | exact add_metadata _ (Equation.MetadataGuarded.scaled _ _ _).rule
          | exact PreservesState.pure _ _
          | split
    termination_by sizeOf ty
  private theorem compileTypes_metadata (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState Graph.MetadataInvariant (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_metadata index mode first)
      intro child
      apply PreservesState.bind (compileTypes_metadata index mode rest)
      intro later
      exact PreservesState.pure _ _
    termination_by sizeOf types
end

private def BuildsMetadataEquation (action : Build Equation) : Prop :=
  ∀ graph, graph.MetadataInvariant →
    (action graph).2.MetadataInvariant ∧ (action graph).1.InvariantRule EnumMetadata

private theorem BuildsMetadataEquation.pure (equation : Equation)
    (safe : equation.InvariantRule EnumMetadata) :
    BuildsMetadataEquation (pure equation) := fun _ valid => ⟨valid, safe⟩

private theorem BuildsMetadataEquation.bind {α : Type} {action : Build α} {next : α → Build Equation}
    (first : PreservesState Graph.MetadataInvariant action)
    (later : ∀ value, BuildsMetadataEquation (next value)) : BuildsMetadataEquation (action >>= next) :=
  fun graph valid => later (action graph).1 (action graph).2 (first graph valid)

private theorem BuildsMetadataEquation.install_yield {α : Type} {action : Build Equation}
    (node : Nat) (result : α) (safe : BuildsMetadataEquation action) :
    PreservesState Graph.MetadataInvariant (do put node (← action); Pure.pure result) := by
  intro graph valid
  have built := safe graph valid
  exact put_metadata node (action graph).1 built.2 (action graph).2 built.1

private theorem copyRoot_metadata (child : Nat) : BuildsMetadataEquation (do
    let graph ← get
    pure ((graph.nodes.find child).getD (alias child))) := by
  intro graph valid
  refine ⟨valid, ?_⟩
  change ((graph.nodes.find child).getD (alias child)).InvariantRule EnumMetadata
  cases found : graph.nodes.find child with
  | none => exact .alias child
  | some equation => exact valid child equation found

private theorem structEquation_metadata (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsMetadataEquation (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsMetadataEquation.pure; exact (Equation.MetadataGuarded.failed _).rule)
    | (apply BuildsMetadataEquation.pure; exact (Equation.MetadataGuarded.canonicalFields _ _ _ _).rule)
    | (apply BuildsMetadataEquation.pure; exact (Equation.MetadataGuarded.declaredFields _ _ _ _ _ _ _ _).rule)
    | (apply BuildsMetadataEquation.bind (compileTypes_metadata _ _ _); intro children)
    | split

private theorem closureEquation_metadata (index : Index) (position : Nat) (definition : ClosureTy) :
    BuildsMetadataEquation (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | (apply BuildsMetadataEquation.pure; exact (Equation.MetadataGuarded.failed _).rule)
    | (apply BuildsMetadataEquation.pure; exact (Equation.MetadataGuarded.declaredFields _ _ _ _ _ _ _ _).rule)
    | (apply BuildsMetadataEquation.bind (compileTypes_metadata _ _ _); intro children)
    | split

private theorem enumNodes_metadata (index : Index) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState Graph.MetadataInvariant (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_metadata _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_metadata _ (Equation.MetadataGuarded.done _
           (by intro value same; cases same; exact EnumMetadata.no_enum rfl)).rule)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private theorem variantEquation_metadata (mode : Mode) (definition : EnumDef)
    (children : List (Ty × Nat)) (variantIndex : Nat) :
    (match definition.layout with
      | none => canonicalFields mode "enum" definition.id.index children
      | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
        | none => Equation.done (.error (.incoherent "enum" definition.id.index))
        | some offsets =>
          if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
          else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
            (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))).MetadataGuarded := by
  repeat first
    | exact Equation.MetadataGuarded.failed _
    | exact Equation.MetadataGuarded.canonicalFields _ _ _ _
    | exact Equation.MetadataGuarded.declaredFields _ _ _ _ _ _ _ _
    | split

private theorem forIn_metadata_length {α : Type} (rows : List α) (initial : List Nat)
    (body : α → List Nat → Build (ForInStep (List Nat)))
    (pushed : ∀ row, row ∈ rows → ∀ nodes graph,
      ∃ next, (body row nodes graph).1 = .yield next ∧ next.length = nodes.length + 1)
    (graph : Graph) : (forIn rows initial body graph).1.length = initial.length + rows.length := by
  induction rows generalizing initial graph with
  | nil => rw [List.forIn_nil]; simp only [List.length_nil, Nat.add_zero]; rfl
  | cons first rest ih =>
    rcases pushed first ((trustIrListMemConsSelf _ _)) initial graph with ⟨next, yielded, length⟩
    rw [List.forIn_cons]
    cases outcome : body first initial graph with
    | mk selected after =>
      rw [outcome] at yielded
      cases yielded
      have later := ih next (fun row member => pushed row (List.mem_cons_of_mem _ member)) after
      have exactLength : (forIn rest next body after).1.length = initial.length + (first :: rest).length := by
        simp only [List.length_cons]
        omega
      simpa only [Bind.bind, StateT.bind, outcome] using exactLength

private theorem enumVariants_metadata_length (index : Index) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat))
    (nodes : List Nat) (graph : Graph) :
    let result := (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) graph
    result.1.length = nodes.length + rows.length := by
  apply forIn_metadata_length rows nodes _ ?_ graph
  intro row member acc before
  rcases row with ⟨variant, variantIndex⟩
  dsimp only
  by_cases skipped : selected.any (fun active => variantIndex != active) = true
  all_goals simp only [skipped, ite_true, ite_false]
  all_goals exact ⟨_, rfl, rfl⟩

private theorem enumVariants_metadata_preserves (index : Index) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat)) (nodes : List Nat) :
    PreservesState Graph.MetadataInvariant (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) := by
  apply PreservesState.forIn
  intro row member variants
  rcases row with ⟨variant, variantIndex⟩
  dsimp only
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (enumNodes_metadata _ _ _ _); intro children)
    | (apply PreservesState.bind (add_metadata _ (variantEquation_metadata mode definition _ variantIndex).rule); intro node)
    | (simp only [pure_bind])
    | split

private theorem enumEquation_metadata (index : Index) (mode : Mode)
    (definition : EnumDef) (facts : NatIndexTree Unit) :
    BuildsMetadataEquation (do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := match definition.layout with
        | some descriptor => match descriptor.encoding with
          | .singleInhabited selected =>
            if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
          | _ => none
        | none => none
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      pure equation) := by
  intro graph valid
  let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
  let selected := match definition.layout with
    | some descriptor => match descriptor.encoding with
      | .singleInhabited selected =>
        if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
      | _ => none
    | none => none
  let variantsAction : Build (List Nat) := do
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      -- Skip physical children only after checking the actual structural
      -- facts and all inactive offset rows. Logical rows retain their IDs.
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    pure variants
  have preserved := enumVariants_metadata_preserves index mode definition selected (numbered definition.variants) []
  have count := enumVariants_metadata_length index mode definition selected (numbered definition.variants) [] graph
  change (variantsAction graph).2.MetadataInvariant ∧
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)
      then Equation.done (.error Error.scalarTarget)
      else enumEquation mode definition uninhabited (variantsAction graph).1.reverse).InvariantRule EnumMetadata
  refine ⟨preserved graph valid, ?_⟩
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact (Equation.MetadataGuarded.failed _).rule
  · apply Equation.MetadataGuarded.rule
    apply Equation.MetadataGuarded.enumeration
    · simpa only [List.length_reverse, List.length_nil, Nat.zero_add, numbered_metadata_length] using count
    · simp only [uninhabited, List.length_map]

private theorem build_metadata (index : Index) (facts : NatIndexTree Unit) :
    (build index facts).MetadataInvariant := by
  have program : PreservesState Graph.MetadataInvariant (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_metadata _ _ (Equation.MetadataGuarded.failed _).rule)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          exact BuildsMetadataEquation.install_yield (index.node mode position) _
            (BuildsMetadataEquation.bind (compileTy_metadata index mode ty) (fun child => copyRoot_metadata child))
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          exact BuildsMetadataEquation.install_yield (index.node mode (index.structBase + position)) _
            (structEquation_metadata index mode definition)
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            exact BuildsMetadataEquation.install_yield (index.node mode (index.enumBase + position)) _
              (enumEquation_metadata index mode definition facts)
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              split
              · exact BuildsMetadataEquation.install_yield (index.node mode (index.closureBase + position)) _
                  (closureEquation_metadata index position definition)
              · apply PreservesState.bind (put_metadata _ _ (Equation.MetadataGuarded.failed _).rule)
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      apply PreservesState.bind (put_metadata _ _ (Equation.MetadataGuarded.unit _).rule)
      intro unit
      exact put_metadata _ _ (Equation.MetadataGuarded.unit _).rule
  exact program _ (Graph.SummaryInvariant.empty _ _)

/-- Preparation proves the actual source-sized row and flag counts and
retains unique, fitting discriminants through every installed equation. -/
theorem prepare_metadata (source : Environment) : (prepare source).graph.MetadataInvariant :=
  build_metadata (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source))

theorem RootCompilation.preserves_metadata {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (safe : before.MetadataInvariant) : after.MetadataInvariant := by
  have kept := compileTy_metadata index mode ty before safe
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at kept
  exact kept

theorem Session.query_preserves_metadata (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (safe : session.graph.MetadataInvariant)
    (run : session.query mode ty = .ok (value, next)) : next.graph.MetadataInvariant ∧ EnumMetadata value := by
  rcases session.query_selection mode ty value next valid run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have selected : graph.MetadataInvariant := by
    cases chosen with
    | cached hit => exact safe
    | compiled graph compiled => exact compiled.preserves_metadata safe
  constructor
  · rw [graphSame]; exact selected
  · exact derived.satisfies selected

/-- Generic state for obligations confined to the reserved source prefix.
    Every allocation beyond that prefix has a vacuous owner obligation. -/
private def ReservedState (lower : Nat) (property : Nat → Summary → Prop) (graph : Graph) : Prop :=
  lower ≤ graph.count ∧ graph.IndexedInvariant property

private theorem add_reserved (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (equation : Equation) :
    PreservesState (ReservedState lower property) (add equation) := by
  intro graph state
  have frontier := state.1
  refine ⟨by change lower ≤ graph.count + 1; omega, ?_⟩
  exact state.2.insert graph.count equation (.guarded (fun _ value _ => outside graph.count value state.1))

private theorem install_reserved (lower : Nat) (property : Nat → Summary → Prop) (node : Nat) (equation : Equation)
    (safe : equation.IndexedRule property node) :
    PreservesState (ReservedState lower property) (put node equation) := by
  intro graph state
  exact ⟨state.1, state.2.insert node equation safe⟩

private theorem leaves_reserved (lower : Nat) (property : Nat → Summary → Prop)
    (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesState (ReservedState lower property)
      (modify fun graph => { graph with leaves := update graph.leaves } : Build Unit) := by
  intro graph state
  exact state

private theorem failed_reserved (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (error : Error) :
    PreservesState (ReservedState lower property) (failed error) :=
  add_reserved lower property outside _

private theorem addScalar_reserved (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (result : Result Summary) :
    PreservesState (ReservedState lower property) (addScalar result) := by
  unfold addScalar
  cases result with
  | error error => exact failed_reserved lower property outside error
  | ok value =>
    apply PreservesState.bind (PreservesState.get (ReservedState lower property))
    intro graph
    split
    · exact PreservesState.pure _ _
    · apply PreservesState.bind (add_reserved lower property outside _)
      intro node
      apply PreservesState.bind (leaves_reserved lower property (fun leaves =>
        leaves.insert (64 * value.size + (value.align.map Nat.succ).getD 0) node))
      intro unit
      exact PreservesState.pure _ _

set_option maxHeartbeats 2000000 in
mutual
  private theorem compileTy_reserved (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (index : Index) (mode : Mode) (ty : Ty) :
      PreservesState (ReservedState lower property) (compileTy index mode ty) := by
    cases hty : ty
    all_goals rw [compileTy.eq_def]
    all_goals dsimp only [scalar]
    all_goals simp only [pure_bind, bind_pure]
    case Vector count element =>
      repeat first
        | exact failed_reserved lower property outside _
        | (apply PreservesState.bind (compileTy_reserved lower property outside index mode element)
           intro child
           exact add_reserved lower property outside _)
        | split
    case Tuple fields =>
      repeat first
        | exact failed_reserved lower property outside _
        | exact add_reserved lower property outside _
        | (apply PreservesState.bind (compileTypes_reserved lower property outside index mode fields)
           intro children
           exact add_reserved lower property outside _)
        | (apply PreservesState.bind (compileTypes_reserved lower property outside index .shape fields)
           intro children
           exact add_reserved lower property outside _)
        | split
    all_goals repeat first
      | exact addScalar_reserved lower property outside _
      | exact add_reserved lower property outside _
      | exact PreservesState.pure _ _
      | split
  termination_by sizeOf ty
  private theorem compileTypes_reserved (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (index : Index) (mode : Mode) (types : List Ty) :
      PreservesState (ReservedState lower property) (compileTypes index mode types) := by
    rw [compileTypes.eq_def]
    cases htypes : types with
    | nil => exact PreservesState.pure _ _
    | cons first rest =>
      apply PreservesState.bind (compileTy_reserved lower property outside index mode first)
      intro child
      apply PreservesState.bind (compileTypes_reserved lower property outside index mode rest)
      intro later
      exact PreservesState.pure _ _
  termination_by sizeOf types
end

private abbrev OriginState (index : Index) (facts : NatIndexTree Unit) :=
  ReservedState (2 * index.count + 2) (EnumSourceAt index facts)

private theorem origin_outside (index : Index) (facts : NatIndexTree Unit) :
    ∀ node value, 2 * index.count + 2 ≤ node → EnumSourceAt index facts node value := by
  intro node value bound
  exact EnumSourceAt.above index facts node (by omega) value

private theorem put_other_origin (index : Index) (facts : NatIndexTree Unit) (mode : Mode) (slot : Nat)
    (inside : slot < index.count) (outside : slot < index.enumBase ∨ index.closureBase ≤ slot)
    (equation : Equation) : PreservesState (OriginState index facts) (put (index.node mode slot) equation) :=
  install_reserved _ _ _ equation (.guarded (fun _ value _ =>
    EnumSourceAt.other_slot index facts mode slot inside outside value))

private theorem put_global_origin (index : Index) (facts : NatIndexTree Unit) (node : Nat)
    (outside : 2 * index.count ≤ node) (equation : Equation) :
    PreservesState (OriginState index facts) (put node equation) :=
  install_reserved _ _ _ equation (.guarded (fun _ value _ => EnumSourceAt.above index facts node outside value))

private def BuildsReservedEquation (lower : Nat) (property : Nat → Summary → Prop) (owner : Nat)
    (action : Build Equation) : Prop :=
  ∀ graph, ReservedState lower property graph → ReservedState lower property (action graph).2 ∧
    (action graph).1.IndexedRule property owner

private theorem BuildsReservedEquation.install_yield {α : Type} (lower : Nat) (property : Nat → Summary → Prop)
    (node : Nat) (result : α) {action : Build Equation} (safe : BuildsReservedEquation lower property node action) :
    PreservesState (ReservedState lower property) (do put node (← action); pure result) := by
  intro graph state
  have built := safe graph state
  exact install_reserved lower property node (action graph).1 built.2 (action graph).2 built.1

private theorem structEquation_reserved_state (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (index : Index) (mode : Mode) (definition : StructDef) :
    PreservesState (ReservedState lower property) (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (compileTypes_reserved _ _ outside _ _ _)
       intro children
       exact PreservesState.pure _ _)
    | split

private theorem closureEquation_reserved_state (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (index : Index) (position : Nat) (definition : ClosureTy) :
    PreservesState (ReservedState lower property) (closureEquation index position definition) := by
  unfold closureEquation
  dsimp only
  try simp only [pure_bind, bind_pure]
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (compileTypes_reserved _ _ outside _ _ _)
       intro children
       exact PreservesState.pure _ _)
    | split

private theorem enumNodes_reserved_state (index : Index) (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState (ReservedState lower property) (enumNodes index mode descriptor types) := by
  induction types with
  | nil => rw [enumNodes.eq_def]; exact PreservesState.pure _ _
  | cons first rest ih =>
    rw [enumNodes.eq_def]
    dsimp only
    cases first <;> repeat first
      | (apply PreservesState.bind (compileTy_reserved _ _ outside _ _ _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | (apply PreservesState.bind (add_reserved _ _ outside _)
         intro child
         apply PreservesState.bind ih
         intro later
         exact PreservesState.pure _ _)
      | split

private theorem enumVariants_reserved_preserves (index : Index) (lower : Nat) (property : Nat → Summary → Prop)
    (outside : ∀ node value, lower ≤ node → property node value) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat)) (nodes : List Nat) :
    PreservesState (ReservedState lower property) (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) := by
  apply PreservesState.forIn
  intro row member variants
  rcases row with ⟨variant, variantIndex⟩
  dsimp only
  repeat first
    | exact PreservesState.pure _ _
    | (apply PreservesState.bind (enumNodes_reserved_state index lower property outside _ _ _); intro children)
    | (apply PreservesState.bind (add_reserved _ _ outside _); intro node)
    | (simp only [pure_bind])
    | split


private theorem structEquation_origin_state (facts : NatIndexTree Unit) (index : Index) (mode : Mode) (definition : StructDef) :
    PreservesState (OriginState index facts) (structEquation index mode definition) :=
  structEquation_reserved_state _ _ (origin_outside index facts) index mode definition

private theorem closureEquation_origin_state (facts : NatIndexTree Unit) (index : Index) (position : Nat) (definition : ClosureTy) :
    PreservesState (OriginState index facts) (closureEquation index position definition) :=
  closureEquation_reserved_state _ _ (origin_outside index facts) index position definition

private theorem enumNodes_origin_state (index : Index) (facts : NatIndexTree Unit) (mode : Mode) (descriptor : Bool) (types : List Ty) :
    PreservesState (OriginState index facts) (enumNodes index mode descriptor types) :=
  enumNodes_reserved_state index _ _ (origin_outside index facts) mode descriptor types

private theorem enumVariants_origin_preserves (index : Index) (facts : NatIndexTree Unit) (mode : Mode)
    (definition : EnumDef) (selected : Option Nat) (rows : List (EnumVariantDef × Nat)) (nodes : List Nat) :
    PreservesState (OriginState index facts) (forIn rows nodes fun (row : EnumVariantDef × Nat) (variants : List Nat) => do
      let variant := row.1
      let variantIndex := row.2
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      let node ← add equation
      pure (ForInStep.yield (node :: variants))) :=
  enumVariants_reserved_preserves index _ _ (origin_outside index facts) mode definition selected rows nodes

private theorem enumEquation_origin (index : Index) (mode : Mode)
    (definition : EnumDef) (facts : NatIndexTree Unit) (position : Nat)
    (bound : position < index.enumCount) (row : (trustIrListGet? index.source.enums position) = some definition) :
    BuildsReservedEquation (2 * index.count + 2) (EnumSourceAt index facts)
      (index.node mode (index.enumBase + position)) (do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := match definition.layout with
        | some descriptor => match descriptor.encoding with
          | .singleInhabited selected =>
            if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
          | _ => none
        | none => none
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      pure equation) := by
  intro graph valid
  let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
  let selected := match definition.layout with
    | some descriptor => match descriptor.encoding with
      | .singleInhabited selected =>
        if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
      | _ => none
    | none => none
  let variantsAction : Build (List Nat) := do
    let mut variants := []
    for (variant, variantIndex) in numbered definition.variants do
      -- Skip physical children only after checking the actual structural
      -- facts and all inactive offset rows. Logical rows retain their IDs.
      let children ← if selected.any (fun active => variantIndex != active) then pure []
        else enumNodes index mode definition.layout.isSome variant.fields
      let equation := match definition.layout with
        | none => canonicalFields mode "enum" definition.id.index children
        | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
          | none => Equation.done (.error (.incoherent "enum" definition.id.index))
          | some offsets =>
            if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
            else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
              (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
      variants := (← add equation) :: variants
    pure variants
  have preserved := enumVariants_origin_preserves index facts mode definition selected (numbered definition.variants) []
  change OriginState index facts (variantsAction graph).2 ∧
    (if mode == .shape && !index.source.canonicalScalars &&
        (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
        | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)
      then Equation.done (.error Error.scalarTarget)
      else enumEquation mode definition uninhabited (variantsAction graph).1.reverse).IndexedRule (EnumSourceAt index facts) (index.node mode (index.enumBase + position))
  refine ⟨preserved graph valid, ?_⟩
  trustIrCompilerProof { skip } {
    generalize selection : (mode == .shape && !index.source.canonicalScalars &&
      (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with
      | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true)) = flag
  }
  split
  · exact Equation.IndexedRule.done _ (.error Error.scalarTarget) (by intro value impossible; cases impossible)
  · exact Equation.IndexedRule.enum_origin index facts mode definition position bound row _


private theorem put_type_origin (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index)
    (mode : Mode) (entry : Option Ty) (position : Nat) (member : (entry, position) ∈ numbered index.source.types)
    (equation : Equation) : PreservesState (OriginState index facts) (put (index.node mode position) equation) := by
  have bound := numbered_bound _ _ _ member
  have size := ready.types
  apply put_other_origin index facts mode position
  · unfold Index.count Index.closureBase Index.enumBase Index.structBase
    omega
  · left
    unfold Index.enumBase Index.structBase
    omega

private theorem put_struct_origin (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index)
    (mode : Mode) (entry : StructDef) (position : Nat) (member : (entry, position) ∈ numbered index.source.structs)
    (equation : Equation) :
    PreservesState (OriginState index facts) (put (index.node mode (index.structBase + position)) equation) := by
  have bound := numbered_bound _ _ _ member
  have size := ready.structs
  apply put_other_origin index facts mode (index.structBase + position)
  · unfold Index.count Index.closureBase Index.enumBase
    omega
  · left
    unfold Index.enumBase
    omega

private theorem put_closure_origin (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index)
    (mode : Mode) (entry : ClosureTy) (position : Nat) (member : (entry, position) ∈ numbered index.source.closures)
    (equation : Equation) :
    PreservesState (OriginState index facts) (put (index.node mode (index.closureBase + position)) equation) := by
  have bound := numbered_bound _ _ _ member
  have size := ready.closures
  apply put_other_origin index facts mode (index.closureBase + position)
  · unfold Index.count
    omega
  · right
    omega

set_option maxHeartbeats 2000000 in
private theorem build_enum_origin (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    Graph.EnumOriginInvariant index facts (build index facts) := by
  have program : PreservesState (OriginState index facts) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_type_origin index facts ready mode _ position member _)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          apply PreservesState.bind (compileTy_reserved _ _ (origin_outside index facts) index mode ty)
          intro child
          apply PreservesState.bind (PreservesState.get (OriginState index facts))
          intro graph
          apply PreservesState.bind (put_type_origin index facts ready mode _ position member _)
          intro unit
          exact PreservesState.pure _ _
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          apply PreservesState.bind (structEquation_origin_state facts index mode definition)
          intro equation
          apply PreservesState.bind (put_struct_origin index facts ready mode definition position member equation)
          intro unit
          exact PreservesState.pure _ _
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            have bound : position < index.enumCount := by
              have below := numbered_bound _ _ _ member
              have size := ready.enums
              omega
            exact BuildsReservedEquation.install_yield _ _ _ _
              (enumEquation_origin index mode definition facts position bound (numbered_get _ _ _ member))
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              split
              · apply PreservesState.bind (closureEquation_origin_state facts index position definition)
                intro equation
                apply PreservesState.bind (put_closure_origin index facts ready mode definition position member equation)
                intro unit
                exact PreservesState.pure _ _
              · apply PreservesState.bind (put_closure_origin index facts ready mode definition position member _)
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      apply PreservesState.bind (put_global_origin index facts (globalTuples index) (by unfold globalTuples; omega) _)
      intro unit
      exact put_global_origin index facts (globalClosures index) (by unfold globalClosures globalTuples; omega) _
  have initial : OriginState index facts { count := globalClosures index + 1 } :=
    ⟨by change 2 * index.count + 2 ≤ globalClosures index + 1; unfold globalClosures globalTuples; omega,
      Graph.IndexedInvariant.empty _ _⟩
  exact (program _ initial).2

/-- Every original enum slot in the actual prepared graph authenticates its
    own source definition, compilation mode and exact solver flag computation. -/
theorem prepare_enum_origin (source : Environment) :
    Graph.EnumOriginInvariant (Index.ofEnvironment source)
      (uninhabitedFacts (Index.ofEnvironment source)) (prepare source).graph :=
  build_enum_origin _ _ (indexReady source)

/-- Query-time structural compilation cannot replace source enum provenance;
    fresh dynamic owners lie outside the reserved source slots. -/
theorem RootCompilation.preserves_enum_origin {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (facts : NatIndexTree Unit) (frontier : 2 * index.count + 2 ≤ before.count)
    (safe : Graph.EnumOriginInvariant index facts before) : Graph.EnumOriginInvariant index facts after := by
  have preserved := compileTy_reserved _ _ (origin_outside index facts) index mode ty before ⟨frontier, safe⟩
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at preserved
  exact preserved.2

/-- Real successful query transitions retain source enum provenance, including
    root-cache and derived memo hits. -/
theorem Session.query_preserves_enum_origin (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (facts : NatIndexTree Unit) (valid : session.DerivationInvariant)
    (safe : Graph.EnumOriginInvariant session.index facts session.graph)
    (run : session.query mode ty = .ok (value, next)) :
    Graph.EnumOriginInvariant session.index facts next.graph := by
  obtain ⟨root, graph, reused, chosen, _indexSame, graphSame, _rootsSame, _derived⟩ :=
    Session.query_selection session mode ty value next valid run
  rw [graphSame]
  cases chosen with
  | cached hit => exact safe
  | compiled graph compiled => exact compiled.preserves_enum_origin facts valid.1.2 safe


private theorem failed_present (before : Graph) (error : Error) :
    (failed error before).2.nodes.find (failed error before).1 = some (Equation.done (.error error)) := by
  change (before.nodes.insert before.count (Equation.done (.error error))).find before.count = _
  rw [NatIndexTree.find_insert, if_pos rfl]

private theorem failed_no_derivation (before : Graph) (error : Error) (root : Nat) (after graph : Graph)
    (value : Summary) (compiled : failed error before = (root, after))
    (extended : after.Extends graph) (derived : NodeDerivation graph root value) : False := by
  have present := failed_present before error
  rw [compiled] at present
  have executed := derived.execution (extended root _ present)
  obtain ⟨first, last, initial, _steps, _finished⟩ := executed
  cases initial

/-- A successful derivation at an actually compiled enum root identifies the
    exact source-position selector. A newly installed refusal cannot become a
    success through a cache or a later graph extension. -/
theorem RootCompilation.enum_selected {index : Index} {mode : Mode} {id : EnumId}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode (.Enum id) before root after)
    (graph : Graph) (value : Summary) (extended : after.Extends graph)
    (derived : NodeDerivation graph root value) :
    ∃ position, (if mode == .shape then index.enumShapePositions else index.enumPositions).find id.index = some position ∧
      root = index.node mode (index.enumBase + position) ∧ after = before := by
  change compileTy index mode (.Enum id) before = (root, after) at compiled
  rw [compileTy.eq_def] at compiled
  dsimp only [scalar] at compiled
  simp only [pure_bind, bind_pure] at compiled
  split at compiled
  · exact False.elim (failed_no_derivation before .scalarTarget root after graph value compiled extended derived)
  · cases found : (if mode == .shape then index.enumShapePositions else index.enumPositions).find id.index with
    | none =>
      simp only [found] at compiled
      exact False.elim (failed_no_derivation before (.missingEnum id.index) root after graph value compiled extended derived)
    | some position =>
      simp only [found] at compiled
      cases compiled
      exact ⟨position, rfl, rfl, rfl⟩


private theorem compileTypes_length (index : Index) (mode : Mode) (types : List Ty) (graph : Graph) :
    (compileTypes index mode types graph).1.length = types.length := by
  induction types generalizing graph with
  | nil => rw [compileTypes.eq_def]; rfl
  | cons first rest ih =>
    rw [compileTypes.eq_def]
    change (compileTypes index mode rest (compileTy index mode first graph).2).1.length + 1 = rest.length + 1
    rw [ih]

theorem TypesCompilation.length {index : Index} {mode : Mode} {types : List Ty}
    {before after : Graph} {roots : List Nat} (compiled : TypesCompilation index mode types before roots after) :
    roots.length = types.length := by
  have count := compileTypes_length index mode types before
  change compileTypes index mode types before = (roots,after) at compiled
  rw [compiled] at count
  exact count

private def BuildsFieldTypes (types : List Ty) (action : Build Equation) : Prop :=
  ∀ before graph value, (action before).1.Executes graph value → value.fields.map (·.ty) = types

private theorem BuildsFieldTypes.of_equation (types : List Ty) (equation : Equation)
    (typed : ∀ graph value, equation.Executes graph value → value.fields.map (·.ty) = types) :
    BuildsFieldTypes types (pure equation) := fun _ => typed

private theorem BuildsFieldTypes.failed (types : List Ty) (error : Error) :
    BuildsFieldTypes types (pure (Equation.done (.error error))) := by
  apply BuildsFieldTypes.of_equation
  intro graph value run
  obtain ⟨first,last,initial,steps,finished⟩ := run
  cases initial

private theorem BuildsFieldTypes.bind_types (index : Index) (mode : Mode) (types expected : List Ty)
    (next : List Nat → Build Equation)
    (later : ∀ roots, roots.length = types.length → BuildsFieldTypes expected (next roots)) :
    BuildsFieldTypes expected (compileTypes index mode types >>= next) := by
  intro before graph value run
  exact later _ (compileTypes_length index mode types before) (compileTypes index mode types before).2 graph value run

private theorem BuildsFieldTypes.canonical (mode : Mode) (kind : String) (id : Nat)
    (types : List Ty) (roots : List Nat) (count : roots.length = types.length) :
    BuildsFieldTypes types (pure (canonicalFields mode kind id (types.zip roots))) := by
  apply BuildsFieldTypes.of_equation
  intro graph value run
  exact (run.canonicalFields_types mode kind id _).trans (zip_fst_exact types roots count.symm)

private theorem BuildsFieldTypes.declared (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List FieldDef) (roots : List Nat) (count : roots.length = (fields.map (·.ty)).length) :
    BuildsFieldTypes (fields.map (·.ty)) (pure (declaredFields mode kind id size align clamp transparent
      (fields.zip roots |>.map (fun (field,child) => (field.ty,field.offset,child))))) := by
  apply BuildsFieldTypes.of_equation
  intro graph value run
  rw [run.declaredFields_types mode kind id size align clamp transparent _]
  have same := zip_fst_exact fields roots (by simpa only [List.length_map] using count.symm)
  simpa only [List.map_map] using congrArg (List.map FieldDef.ty) same

private theorem structEquation_types (index : Index) (mode : Mode) (definition : StructDef) :
    BuildsFieldTypes (definition.fields.map (·.ty)) (structEquation index mode definition) := by
  unfold structEquation
  dsimp only
  simp only [pure_bind,bind_pure]
  repeat first
    | exact BuildsFieldTypes.failed _ _
    | (apply BuildsFieldTypes.canonical; assumption)
    | (apply BuildsFieldTypes.declared; assumption)
    | (apply BuildsFieldTypes.bind_types; intro roots count)
    | split

/-- A successful real struct construction preserves the selected declaration's
    complete logical field type order, for canonical and authored layouts. -/
theorem StructCompilation.field_types {index : Index} {mode : Mode} {definition : StructDef}
    {before after : Graph} {equation : Equation} (compiled : StructCompilation index mode definition before equation after)
    (graph : Graph) (value : Summary) (run : equation.Executes graph value) :
    value.fields.map (·.ty) = definition.fields.map (·.ty) := by
  have typed := structEquation_types index mode definition before graph value
  change structEquation index mode definition before = (equation,after) at compiled
  rw [compiled] at typed
  exact typed run

/-- A successful derivation at an actually compiled struct root identifies the
    exact source-position selector. A newly installed refusal cannot become a
    success through a cache or a later graph extension. -/
theorem RootCompilation.struct_selected {index : Index} {mode : Mode} {id : StructId}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode (.Struct id) before root after)
    (graph : Graph) (value : Summary) (extended : after.Extends graph)
    (derived : NodeDerivation graph root value) :
    ∃ position, (if mode == .shape then index.structShapePositions else index.structPositions).find id.index = some position ∧
      root = index.node mode (index.structBase + position) ∧ after = before := by
  change compileTy index mode (.Struct id) before = (root, after) at compiled
  rw [compileTy.eq_def] at compiled
  dsimp only [scalar] at compiled
  simp only [pure_bind, bind_pure] at compiled
  split at compiled
  · exact False.elim (failed_no_derivation before .scalarTarget root after graph value compiled extended derived)
  · cases found : (if mode == .shape then index.structShapePositions else index.structPositions).find id.index with
    | none =>
      simp only [found] at compiled
      exact False.elim (failed_no_derivation before (.missingStruct id.index) root after graph value compiled extended derived)
    | some position =>
      simp only [found] at compiled
      cases compiled
      exact ⟨position, rfl, rfl, rfl⟩


private abbrev StructOriginState (index : Index) :=
  ReservedState (2 * index.count + 2) (StructSourceAt index)

private theorem struct_origin_outside (index : Index) :
    ∀ node value, 2 * index.count + 2 ≤ node → StructSourceAt index node value := by
  intro node value bound
  exact StructSourceAt.above index node (by omega) value

private theorem structEquation_origin_rule (index : Index) (mode : Mode) (definition : StructDef)
    (position : Nat) (bound : position < index.structCount)
    (row : (trustIrListGet? index.source.structs position) = some definition) :
    BuildsReservedEquation (2 * index.count + 2) (StructSourceAt index)
      (index.node mode (index.structBase + position)) (structEquation index mode definition) := by
  intro before state
  refine ⟨structEquation_reserved_state _ _ (struct_origin_outside index) index mode definition before state, ?_⟩
  exact Equation.IndexedRule.struct_types index mode definition position bound row _
    (structEquation_types index mode definition before)

private theorem put_other_struct_origin (index : Index) (mode : Mode) (slot : Nat)
    (inside : slot < index.count) (outside : slot < index.structBase ∨ index.enumBase ≤ slot)
    (equation : Equation) : PreservesState (StructOriginState index) (put (index.node mode slot) equation) :=
  install_reserved _ _ _ equation (.guarded (fun _ value _ =>
    StructSourceAt.other_slot index mode slot inside outside value))

private theorem put_global_struct_origin (index : Index) (node : Nat)
    (outside : 2 * index.count ≤ node) (equation : Equation) :
    PreservesState (StructOriginState index) (put node equation) :=
  install_reserved _ _ _ equation (.guarded (fun _ value _ => StructSourceAt.above index node outside value))

private theorem put_type_struct_origin (index : Index) (ready : IndexReady index)
    (mode : Mode) (entry : Option Ty) (position : Nat) (member : (entry, position) ∈ numbered index.source.types)
    (equation : Equation) : PreservesState (StructOriginState index) (put (index.node mode position) equation) := by
  have bound := numbered_bound _ _ _ member
  have size := ready.types
  apply put_other_struct_origin index mode position
  · unfold Index.count Index.closureBase Index.enumBase Index.structBase
    omega
  · left
    unfold Index.structBase
    omega

private theorem put_enum_struct_origin (index : Index) (ready : IndexReady index)
    (mode : Mode) (entry : EnumDef) (position : Nat) (member : (entry, position) ∈ numbered index.source.enums)
    (equation : Equation) :
    PreservesState (StructOriginState index) (put (index.node mode (index.enumBase + position)) equation) := by
  have bound := numbered_bound _ _ _ member
  have size := ready.enums
  apply put_other_struct_origin index mode (index.enumBase + position)
  · unfold Index.count Index.closureBase
    omega
  · right
    omega

private theorem put_closure_struct_origin (index : Index) (ready : IndexReady index)
    (mode : Mode) (entry : ClosureTy) (position : Nat) (member : (entry, position) ∈ numbered index.source.closures)
    (equation : Equation) :
    PreservesState (StructOriginState index) (put (index.node mode (index.closureBase + position)) equation) := by
  have bound := numbered_bound _ _ _ member
  have size := ready.closures
  apply put_other_struct_origin index mode (index.closureBase + position)
  · unfold Index.count
    omega
  · right
    unfold Index.closureBase
    omega

private theorem enum_build_struct_origin (index : Index) (mode : Mode)
    (definition : EnumDef) (facts : NatIndexTree Unit) (position : Nat) (ready : IndexReady index)
    (member : (definition,position) ∈ numbered index.source.enums) :
    PreservesState (StructOriginState index) (do
      let uninhabited := definition.variants.map (fun variant => variantUninhabited index facts variant.fields)
      let selected := match definition.layout with
        | some descriptor => match descriptor.encoding with
          | .singleInhabited selected =>
            if singleInhabitedValid definition descriptor uninhabited selected then some selected else none
          | _ => none
        | none => none
      let mut variants := []
      for (variant, variantIndex) in numbered definition.variants do
        -- Skip physical children only after checking the actual structural
        -- facts and all inactive offset rows. Logical rows retain their IDs.
        let children ← if selected.any (fun active => variantIndex != active) then pure []
          else enumNodes index mode definition.layout.isSome variant.fields
        let equation := match definition.layout with
          | none => canonicalFields mode "enum" definition.id.index children
          | some descriptor => match (trustIrListGet? descriptor.variantFieldOffsets variantIndex) with
            | none => Equation.done (.error (.incoherent "enum" definition.id.index))
            | some offsets =>
              if offsets.length != children.length then .done (.error (.incoherent "enum" definition.id.index))
              else declaredFields mode "enum" definition.id.index descriptor.size descriptor.align word64Max false
                (children.zip offsets |>.map (fun ((ty, child), offset) => (ty, some offset, child)))
        variants := (← add equation) :: variants
      let equation := enumEquation mode definition uninhabited variants.reverse
      let equation := if mode == .shape && !index.source.canonicalScalars &&
          (match definition.layout.map (fun (descriptor : EnumLayoutDescriptor) => descriptor.encoding) with | some EnumTagEncoding.untagged | some (.singleInhabited _) => false | _ => true) then
            Equation.done (.error Error.scalarTarget) else equation
      put (index.node mode (index.enumBase + position)) equation) := by
  dsimp only
  simp only [pure_bind, bind_pure]
  apply PreservesState.bind
  · exact enumVariants_reserved_preserves index _ _ (struct_origin_outside index) mode definition _ _ _
  · intro variants
    exact put_enum_struct_origin index ready mode definition position member _
private theorem build_struct_origin (index : Index) (facts : NatIndexTree Unit) (ready : IndexReady index) :
    Graph.StructOriginInvariant index (build index facts) := by
  have program : PreservesState (StructOriginState index) (buildProgram index facts) := by
    unfold buildProgram
    dsimp only
    simp only [pure_bind, bind_pure]
    apply PreservesState.bind
    · apply PreservesState.forIn
      intro mode modeMember modeState
      apply PreservesState.bind
      · apply PreservesState.forIn
        intro row member state
        rcases row with ⟨entry, position⟩
        dsimp only
        cases entry with
        | none =>
          apply PreservesState.bind (put_type_struct_origin index ready mode _ position member _)
          intro unit
          exact PreservesState.pure _ _
        | some ty =>
          apply PreservesState.bind (compileTy_reserved _ _ (struct_origin_outside index) index mode ty)
          intro child
          apply PreservesState.bind (PreservesState.get (StructOriginState index))
          intro graph
          apply PreservesState.bind (put_type_struct_origin index ready mode _ position member _)
          intro unit
          exact PreservesState.pure _ _
      · intro unit
        apply PreservesState.bind
        · apply PreservesState.forIn
          intro row member state
          rcases row with ⟨definition, position⟩
          have bound : position < index.structCount := by
            have below := numbered_bound _ _ _ member
            have size := ready.structs
            omega
          exact BuildsReservedEquation.install_yield _ _ _ _
            (structEquation_origin_rule index mode definition position bound (numbered_get _ _ _ member))
        · intro unit
          apply PreservesState.bind
          · apply PreservesState.forIn
            intro row member state
            rcases row with ⟨definition, position⟩
            exact enum_build_struct_origin index mode definition facts position ready member
          · intro unit
            apply PreservesState.bind
            · apply PreservesState.forIn
              intro row member state
              rcases row with ⟨definition, position⟩
              split
              · apply PreservesState.bind (closureEquation_reserved_state _ _ (struct_origin_outside index) index position definition)
                intro equation
                apply PreservesState.bind (put_closure_struct_origin index ready mode definition position member equation)
                intro unit
                exact PreservesState.pure _ _
              · apply PreservesState.bind (put_closure_struct_origin index ready mode definition position member _)
                intro unit
                exact PreservesState.pure _ _
            · intro unit
              exact PreservesState.pure _ _
    · intro unit
      apply PreservesState.bind (put_global_struct_origin index (globalTuples index) (by unfold globalTuples; omega) _)
      intro unit
      exact put_global_struct_origin index (globalClosures index) (by unfold globalClosures globalTuples; omega) _
  have initial : StructOriginState index { count := globalClosures index + 1 } :=
    ⟨by change 2 * index.count + 2 ≤ globalClosures index + 1; unfold globalClosures globalTuples; omega,
      Graph.IndexedInvariant.empty _ _⟩
  exact (program _ initial).2


/-- Actual preparation authenticates every reserved struct declaration slot. -/
theorem prepare_struct_origin (source : Environment) :
    Graph.StructOriginInvariant (Index.ofEnvironment source) (prepare source).graph :=
  build_struct_origin _ _ (indexReady source)

/-- Dynamic structural compilation preserves the reserved source struct slots. -/
theorem RootCompilation.preserves_struct_origin {index : Index} {mode : Mode} {ty : Ty}
    {before after : Graph} {root : Nat} (compiled : RootCompilation index mode ty before root after)
    (frontier : 2 * index.count + 2 ≤ before.count)
    (safe : Graph.StructOriginInvariant index before) : Graph.StructOriginInvariant index after := by
  have preserved := compileTy_reserved _ _ (struct_origin_outside index) index mode ty before ⟨frontier, safe⟩
  change compileTy index mode ty before = (root, after) at compiled
  rw [compiled] at preserved
  exact preserved.2

theorem Session.query_preserves_struct_origin (session : Session) (mode : Mode) (ty : Ty)
    (value : Summary) (next : Session) (valid : session.DerivationInvariant)
    (safe : Graph.StructOriginInvariant session.index session.graph)
    (run : session.query mode ty = .ok (value, next)) :
    Graph.StructOriginInvariant session.index next.graph := by
  obtain ⟨root, graph, reused, chosen, _indexSame, graphSame, _rootsSame, _derived⟩ :=
    Session.query_selection session mode ty value next valid run
  rw [graphSame]
  cases chosen with
  | cached hit => exact safe
  | compiled graph compiled => exact compiled.preserves_struct_origin valid.1.2 safe

end TrustIr.SourceLayout
