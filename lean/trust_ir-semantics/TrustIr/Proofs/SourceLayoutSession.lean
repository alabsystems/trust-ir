-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Service
import TrustIr.Proofs.SourceLayoutDerivation
import TrustIr.Semantics.Eval

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.SourceLayout

/-- Actual persistent sessions obtained from preparation and successful
    query transitions. Refused queries return no replacement session. -/
inductive Session.Reachable (source : Environment) : Session → Prop where
  | prepared : Session.Reachable source (prepare source)
  | queried {before after : Session} {mode : Mode} {ty : Ty} {value : Summary}
      (prior : Session.Reachable source before)
      (run : before.query mode ty = .ok (value, after)) : Session.Reachable source after

theorem Session.Reachable.invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.DerivationInvariant := by
  induction history with
  | prepared => exact prepare_derivation source
  | queried prior run ih => exact (Session.query_preserves_derivation _ _ _ _ _ ih run).1

/-- Every graph in the actual prepared-session lifecycle retains byte-bound
rules, including newly compiled roots and all old memo dependencies. -/
theorem Session.Reachable.word_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.WordInvariant := by
  induction history with
  | prepared => exact prepare_word source
  | queried prior run ih =>
    exact (Session.query_preserves_word _ _ _ _ _ prior.invariant ih run).1

theorem Session.Reachable.index_eq {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.index = Index.ofEnvironment source := by
  induction history with
  | prepared => rfl
  | queried prior run ih =>
    exact (Session.query_preserves_derivation _ _ _ _ _ prior.invariant run).2.1.trans ih

/-- A cached root came from the actual compiler at a reachable session of this
source. Every equation of that compiled graph survives in the current graph. -/
def Session.CompiledRoot (source : Environment) (mode : Mode) (ty : Ty)
    (root : Nat) (graph : Graph) : Prop :=
  ∃ before : Session, Session.Reachable source before ∧ ∃ compiled : Graph,
    RootCompilation before.index mode ty before.graph root compiled ∧ compiled.Extends graph

theorem Session.CompiledRoot.weaken {source : Environment} {mode : Mode} {ty : Ty}
    {root : Nat} {before after : Graph} (origin : Session.CompiledRoot source mode ty root before)
    (growth : before.Extends after) : Session.CompiledRoot source mode ty root after := by
  rcases origin with ⟨session, history, compiled, run, preserved⟩
  exact ⟨session, history, compiled, run, preserved.trans growth⟩

/-- Full type and mode are attached to an actual compilation, not to a bucket
hash or to an equal byte layout. Bucket collisions remain ordinary list entries. -/
def Session.RootsCompiled (source : Environment) (session : Session) : Prop :=
  ∀ bucket ty mode root, (ty, mode, root) ∈ (session.roots.find bucket).getD [] →
    Session.CompiledRoot source mode ty root session.graph

theorem Session.Reachable.roots_compiled {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.RootsCompiled source := by
  induction history with
  | prepared =>
    intro bucket ty mode root impossible
    change (ty, mode, root) ∈ ([] : List (Ty × Mode × Nat)) at impossible
    cases impossible
  | @queried before after mode ty value prior run ih =>
    rcases Session.query_selection before mode ty value after prior.invariant run with
      ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
    have growth := (Session.query_preserves_derivation before mode ty value after prior.invariant run).2.2.1
    intro bucket storedTy storedMode storedRoot member
    rw [rootsSame] at member
    cases chosen with
    | cached hit =>
      change (storedTy, storedMode, storedRoot) ∈ (before.roots.find bucket).getD [] at member
      exact (ih bucket storedTy storedMode storedRoot member).weaken growth.equations
    | compiled graph compiled =>
      have fresh : Session.CompiledRoot source mode ty root after.graph :=
        ⟨before, prior, graph, compiled, by rw [graphSame]; exact Graph.Extends.refl graph⟩
      change (storedTy, storedMode, storedRoot) ∈
        ((before.roots.insert (rootBucket mode ty)
          ((ty, mode, root) :: (before.roots.find (rootBucket mode ty)).getD [])).find bucket).getD [] at member
      rw [NatIndexTree.find_insert] at member
      by_cases same : bucket = rootBucket mode ty
      · rw [if_pos same] at member
        rcases List.mem_cons.mp member with equal | old
        · cases equal
          exact fresh
        · exact (ih _ storedTy storedMode storedRoot old).weaken growth.equations
      · rw [if_neg same] at member
        exact (ih bucket storedTy storedMode storedRoot member).weaken growth.equations

/-- The returned value has a derivation at the root compiled for this exact
requested type and mode, whether the current query compiled it or reused it. -/
theorem Session.Reachable.query_compilation_origin {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) :
    ∃ root, Session.CompiledRoot source mode ty root next.graph ∧ NodeDerivation next.graph root value := by
  rcases Session.query_selection session mode ty value next history.invariant run with
    ⟨root, graph, reused, chosen, indexSame, graphSame, rootsSame, derived⟩
  have growth := (Session.query_preserves_derivation session mode ty value next history.invariant run).2.2.1
  have origin : Session.CompiledRoot source mode ty root next.graph := by
    cases chosen with
    | cached hit => exact (history.roots_compiled _ ty mode root hit).weaken growth.equations
    | compiled graph compiled =>
      exact ⟨session, history, graph, compiled, by rw [graphSame]; exact Graph.Extends.refl graph⟩
  exact ⟨root, origin, by rw [graphSame]; exact derived⟩

/-- Exact scalar interning holds after every actual finite query history. -/
theorem Session.Reachable.scalar_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) :
    session.graph.ScalarInvariant (2 * session.index.count + 2) session.index.source.model.pointerBytes := by
  induction history with
  | prepared => exact prepare_scalars source
  | queried prior run ih => exact Session.query_preserves_scalars _ _ _ _ _ prior.invariant ih run

/-- The fixed mode assignment survives every actual successful history. -/
theorem Session.Reachable.mode_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.ModeInvariant session.index.nodeMode := by
  induction history with
  | prepared => exact prepare_modes source
  | queried prior run ih =>
    exact Session.query_preserves_modes _ _ _ _ _ prior.invariant prior.scalar_invariant ih run

theorem Session.CompiledRoot.shape_root {source : Environment} {ty : Ty} {root : Nat} {graph : Graph}
    (origin : Session.CompiledRoot source .shape ty root graph) :
    ShapeRoot (Index.ofEnvironment source) graph root := by
  rcases origin with ⟨before, history, compiled, run, growth⟩
  have frontier := history.invariant.1.2
  have scalars := history.scalar_invariant
  rw [history.index_eq] at run frontier scalars
  exact (RootCompilation.shape_root run history.invariant.1.1 frontier scalars).weaken growth

theorem Session.Reachable.extends_prepared {source : Environment} {session : Session}
    (history : Session.Reachable source session) : (prepare source).graph.Extends session.graph := by
  induction history with
  | prepared => exact Graph.Extends.refl _
  | queried prior run ih =>
    exact ih.trans (Session.query_preserves_derivation _ _ _ _ _ prior.invariant run).2.2.1.equations

/-- Every cached result in every real finite session history has a derivation
    in that history's actual current graph. No cache oracle is assumed. -/
theorem Session.Reachable.cached {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : NodeDerivation session.graph node value :=
  history.invariant.2 node value found

/-- An actual cached scalar is the exact target-specific candidate for its key;
no fabricated cache-validity or equation-classification premise is needed. -/
theorem Session.Reachable.cached_scalar_value {source : Environment} {session : Session}
    (history : Session.Reachable source session) {expected value : Summary}
    (scalar : ScalarSummary source.model.pointerBytes expected) {node : Nat}
    (interned : session.graph.leaves.find (scalarKey expected) = some node)
    (cached : session.memo.find node = some value) : value = expected := by
  have localScalar : ScalarSummary session.index.source.model.pointerBytes expected := by
    simpa only [history.index_eq] using scalar
  exact history.scalar_invariant.derivation_value localScalar interned (history.cached node value cached)

/-- Exact interned scalars in real session memos satisfy both modes' bounds,
regardless of the mode that first allocated their shared node. -/
theorem Session.Reachable.cached_scalar_bounds {source : Environment} {session : Session}
    (history : Session.Reachable source session) {expected value : Summary}
    (scalar : ScalarSummary source.model.pointerBytes expected) {node : Nat}
    (interned : session.graph.leaves.find (scalarKey expected) = some node)
    (cached : session.memo.find node = some value) (mode : Mode) : FinishBounds mode value := by
  rw [history.cached_scalar_value scalar interned cached]
  exact scalar.finish_bounds source.model mode

theorem Session.Reachable.cached_word_bounds {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : WordBounds 1 value :=
  (history.cached node value found).satisfies history.word_invariant

theorem Session.Reachable.query_word_bounds {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : WordBounds 1 value :=
  (Session.query_preserves_word _ _ _ _ _ history.invariant history.word_invariant run).2

/-- Successful results carry the requested byte/bit bounds at their exact
compiled root, including root-cache and memo hits. -/
theorem Session.Reachable.query_mode_bounds {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : FinishBounds mode value := by
  cases mode with
  | execution =>
    refine ⟨history.query_word_bounds .execution ty value run, ?_⟩
    intro impossible
    cases impossible
  | shape =>
    rcases history.query_compilation_origin .shape ty value run with ⟨root, origin, derived⟩
    have later := Session.Reachable.queried history run
    have modes := later.mode_invariant
    rw [later.index_eq] at modes
    exact origin.shape_root.derivation_bounds modes derived

/-- Memo bounds retain the mode and full type of the actual persistent root
entry; arbitrary untyped memo nodes are not declared shape-safe. -/
theorem Session.Reachable.cached_root_mode_bounds {source : Environment} {session : Session}
    (history : Session.Reachable source session) (bucket : Nat) (ty : Ty) (mode : Mode)
    (root : Nat) (value : Summary)
    (member : (ty, mode, root) ∈ (session.roots.find bucket).getD [])
    (cached : session.memo.find root = some value) : FinishBounds mode value := by
  have origin := history.roots_compiled bucket ty mode root member
  cases mode with
  | execution =>
    refine ⟨history.cached_word_bounds root value cached, ?_⟩
    intro impossible
    cases impossible
  | shape =>
    have modes := history.mode_invariant
    rw [history.index_eq] at modes
    exact origin.shape_root.derivation_bounds modes (history.cached root value cached)

/-- The public one-shot service inherits derivation soundness from its actual
    prepared-session call, retaining the output graph as an explicit witness. -/
theorem query_session_derivation (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) :
    ∃ next, (prepare source).query mode ty = .ok (value, next) ∧ next.DerivationInvariant ∧
      ∃ node, NodeDerivation next.graph node value := by
  cases event : (prepare source).query mode ty with
  | error error => simp [query, event, Bind.bind, Except.bind] at run
  | ok pair =>
    rcases pair with ⟨result, next⟩
    have preserved := Session.query_preserves_derivation (prepare source) mode ty result next
      (prepare_derivation source) event
    have same : result = value := by
      simpa [query, event, Bind.bind, Except.bind, Pure.pure, Except.pure] using run
    subst result
    exact ⟨next, rfl, preserved.1, preserved.2.2.2⟩

/-- Public one-shot success is derived at a root whose compiler origin carries
this exact source, type and mode; there is no caller-provided cache oracle. -/
theorem query_compilation_origin (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) :
    ∃ next root, (prepare source).query mode ty = .ok (value, next) ∧
      Session.CompiledRoot source mode ty root next.graph ∧ NodeDerivation next.graph root value := by
  cases event : (prepare source).query mode ty with
  | error error => simp [query, event, Bind.bind, Except.bind] at run
  | ok pair =>
    rcases pair with ⟨result, next⟩
    have origin := Session.Reachable.query_compilation_origin
      (Session.Reachable.prepared (source := source)) mode ty result event
    have same : result = value := by
      simpa [query, event, Bind.bind, Except.bind, Pure.pure, Except.pure] using run
    subst result
    rcases origin with ⟨root, compiled, derived⟩
    exact ⟨next, root, rfl, compiled, derived⟩

/-- Every successful public layout query has the complete bounds required
by its requested mode. The actual preparation, compiler and caches discharge
all invariant and derivation premises. -/
theorem query_mode_bounds (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : FinishBounds mode value := by
  rcases query_session_derivation source mode ty value run with ⟨next, event, rest⟩
  exact Session.Reachable.query_mode_bounds (Session.Reachable.prepared (source := source)) mode ty value event

/-- The real compiler and every successful query preserve direct-field and
per-variant storage, including cached roots and derivation-backed memo hits. -/
theorem Session.Reachable.storage_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) :
    session.graph.StorageInvariant (2 * session.index.count + 2) := by
  induction history with
  | prepared => exact prepare_storage source
  | queried prior run ih =>
    exact (Session.query_preserves_storage _ _ _ _ _ prior.invariant ih run).1

theorem Session.Reachable.query_storage_geometry {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : StorageGeometry value :=
  (Session.query_preserves_storage _ _ _ _ _ history.invariant history.storage_invariant run).2

/-- An actual memo entry has the same storage guarantee as fresh solving.
No type or mode is invented for an untyped memo key. -/
theorem Session.Reachable.memo_storage_geometry {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : StorageGeometry value :=
  (history.invariant.2 node value found).satisfies_contextual history.storage_invariant.contextual

/-- Successful public layout queries discharge all compiler, child-storage
and cache premises through their actual preparation and execution. -/
theorem query_storage_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : StorageGeometry value := by
  rcases query_session_derivation source mode ty value run with ⟨next, event, rest⟩
  exact Session.Reachable.query_storage_geometry (Session.Reachable.prepared (source := source)) mode ty value event

theorem query_field_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : FieldGeometry value :=
  (query_storage_geometry source mode ty value run).1

theorem query_enumeration_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : EnumerationGeometry value :=
  (query_storage_geometry source mode ty value run).2

/-- Present aggregate alignments remain powers of two and divide their
sizes through actual preparation, compilation and successful cache histories. -/
theorem Session.Reachable.power_alignment_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.PowerAlignmentInvariant := by
  induction history with
  | prepared => exact prepare_power_alignment source
  | queried prior run ih =>
    exact (Session.query_preserves_power_alignment _ _ _ _ _ prior.invariant ih run).1

theorem Session.Reachable.query_power_alignment {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : PowerAlignment value :=
  (Session.query_preserves_power_alignment _ _ _ _ _ history.invariant history.power_alignment_invariant run).2.2

theorem Session.Reachable.memo_power_alignment {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : PowerAlignment value :=
  ((history.invariant.2 node value found).satisfies_at history.power_alignment_invariant).2

/-- The actual successful public query discharges every child and cache
premise. An absent alignment remains absent. -/
theorem query_power_alignment (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : PowerAlignment value := by
  rcases query_session_derivation source mode ty value run with ⟨next, event, rest⟩
  exact Session.Reachable.query_power_alignment (Session.Reachable.prepared (source := source)) mode ty value event

theorem query_alignment_nonzero (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) (align : Nat) (present : value.align = some align) : align ≠ 0 :=
  powerOfTwo_nonzero align ((query_power_alignment source mode ty value run) align present).1

/-- Actual compiler histories retain field and enum-row alignment certificates. -/
theorem Session.Reachable.field_alignment_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) :
    session.graph.FieldAlignmentInvariant (2 * session.index.count + 2) := by
  induction history with
  | prepared => exact prepare_field_alignment source
  | queried prior run ih =>
    exact (Session.query_preserves_field_alignment _ _ _ _ _ prior.invariant prior.power_alignment_invariant ih run).1

theorem Session.Reachable.query_field_alignment {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : FieldAlignmentSummary value :=
  (Session.query_preserves_field_alignment _ _ _ _ _ history.invariant history.power_alignment_invariant
    history.field_alignment_invariant run).2

theorem Session.Reachable.memo_field_alignment {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : FieldAlignmentSummary value :=
  (history.invariant.2 node value found).satisfies_contextual
    (history.field_alignment_invariant.contextual history.power_alignment_invariant)

/-- Public success alone establishes powered, aligned physical fields and
aligned enum rows, with the existing direct empty-field cap exception. -/
theorem query_field_alignment (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : FieldAlignmentSummary value := by
  rcases query_session_derivation source mode ty value run with ⟨next, event, rest⟩
  exact Session.Reachable.query_field_alignment (Session.Reachable.prepared (source := source)) mode ty value event

theorem query_layout_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) :
    FinishBounds mode value ∧ StorageGeometry value ∧ PowerAlignment value ∧ FieldAlignmentSummary value :=
  ⟨query_mode_bounds source mode ty value run, query_storage_geometry source mode ty value run,
    query_power_alignment source mode ty value run, query_field_alignment source mode ty value run⟩

theorem query_positive_field_divides (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) (field : Field) (member : field ∈ value.fields)
    (positive : field.size ≠ 0) (align : Nat) (present : value.align = some align) : field.align ∣ align := by
  have fields := (query_field_alignment source mode ty value run).1 field member
  exact powerOfTwo_dvd_of_le fields.1 ((query_power_alignment source mode ty value run) align present).1
    (fields.2.2 align present positive)

theorem query_enum_field_divides (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration) (fields : List Field) (row : fields ∈ enumeration.variants)
    (field : Field) (member : field ∈ fields) : ∃ align, value.align = some align ∧ field.align ∣ align := by
  rcases (query_field_alignment source mode ty value run).2 enumeration present with ⟨align, actual, variants⟩
  have aligned := variants fields row
  exact ⟨align, actual, powerOfTwo_dvd_of_le (aligned.1 field member)
    ((query_power_alignment source mode ty value run) align actual).1 ((aligned.2 field member).2.2 trivial)⟩

theorem Session.Reachable.encoding_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.EncodingInvariant := by
  induction history with
  | prepared => exact prepare_encoding source
  | queried prior run ih => exact (Session.query_preserves_encoding _ _ _ _ _ prior.invariant ih run).1

theorem Session.Reachable.query_encoding_geometry {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : EnumEncodingGeometry value :=
  (Session.query_preserves_encoding _ _ _ _ _ history.invariant history.encoding_invariant run).2

theorem Session.Reachable.memo_encoding_geometry {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : EnumEncodingGeometry value :=
  (history.invariant.2 node value found).satisfies history.encoding_invariant

/-- Actual public success discharges compiler and cache premises for the
physical tag/niche checks. Boolean inhabitedness is not promoted to semantics. -/
theorem query_encoding_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : EnumEncodingGeometry value := by
  rcases query_session_derivation source mode ty value run with ⟨next, event, rest⟩
  exact Session.Reachable.query_encoding_geometry (Session.Reachable.prepared (source := source)) mode ty value event

theorem query_physical_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) :
    FinishBounds mode value ∧ StorageGeometry value ∧ PowerAlignment value ∧
      FieldAlignmentSummary value ∧ EnumEncodingGeometry value :=
  ⟨query_mode_bounds source mode ty value run, query_storage_geometry source mode ty value run,
    query_power_alignment source mode ty value run, query_field_alignment source mode ty value run,
    query_encoding_geometry source mode ty value run⟩

theorem query_direct_tag_geometry (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration) (offset : Nat)
    (encoding : enumeration.encoding = .direct offset) :
    ∃ align, value.align = some align ∧
      EnumLaneBounds value.size align offset (tagBits enumeration.tag / 8) (tagBits enumeration.tag / 8) ∧
      EnumTagSeparated enumeration offset (tagBits enumeration.tag / 8) := by
  have geometry := (query_encoding_geometry source mode ty value run) enumeration present
  rw [encoding] at geometry
  exact geometry

theorem query_niche_carrier (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration) (untagged start stop first offset : Nat) (repr : EnumTagRepr)
    (encoding : enumeration.encoding = .niche untagged start stop first offset repr) :
    EnumNicheCarrier enumeration untagged offset (tagBits repr / 8) := by
  have geometry := (query_encoding_geometry source mode ty value run) enumeration present
  rw [encoding] at geometry
  rcases geometry with ⟨align, actual, lane, count, inside, ordered, upper, firstBound, spanBound, coverage, carrier, separated⟩
  exact carrier

private theorem metadata_contains_append (left right : List Int) (value : Int) :
    (left ++ right).contains value = (left.contains value || right.contains value) := by
  trustIrCompilerProof {
    induction left with
    | nil => simp [List.contains, List.elem]
    | cons first rest ih =>
      cases accepted : value == first <;> simp [List.contains, List.elem, accepted, ih]
  } {
    exact List.contains_append
  }

private theorem metadata_contains_reverse (values : List Int) (value : Int) :
    values.reverse.contains value = values.contains value := by
  trustIrCompilerProof {
    induction values with
    | nil => rfl
    | cons first rest ih =>
      rw [List.reverse_cons, metadata_contains_append]
      cases accepted : value == first <;> simp [List.contains, List.elem, accepted, ih]
  } {
    exact List.contains_reverse
  }

/-- The layout compiler's reversed accumulator computes exactly the effective
logical discriminants used by value evaluation, including explicit resets. -/
theorem discriminants_go_eval (explicit : List (Option Int)) (next : Option Int) (out : List Int) :
    discriminants.go explicit next out = TrustIr.enumEffectiveDiscriminants.go explicit next out.reverse := by
  induction explicit generalizing next out with
  | nil => rfl
  | cons first rest ih =>
    simp only [discriminants.go, TrustIr.enumEffectiveDiscriminants.go]
    cases chosen : first.orElse (fun _ => next) with
    | none => simp [chosen, Bind.bind, Option.bind]
    | some value =>
      simp only [chosen, Bind.bind, Option.bind, metadata_contains_reverse]
      split
      · rfl
      · simpa only [List.reverse_cons, tagBits] using ih
          (if value + 1 < 2 ^ (tagBits .i128 - 1) then some (value + 1) else none) (value :: out)

theorem discriminants_eval (definition : EnumDef) :
    discriminants definition = TrustIr.enumEffectiveDiscriminants definition := by
  exact discriminants_go_eval _ (some 0) []

theorem tagFits_eval (tag : EnumTagRepr) (value : Int) : tagFits tag value = tag.fits value := by
  cases tag <;> rfl

theorem tagBits_eval (tag : EnumTagRepr) : tagBits tag = tag.bitWidth := by
  cases tag <;> rfl

theorem Session.Reachable.metadata_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.MetadataInvariant := by
  induction history with
  | prepared => exact prepare_metadata source
  | queried prior run ih => exact (Session.query_preserves_metadata _ _ _ _ _ prior.invariant ih run).1

theorem Session.Reachable.query_metadata {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value, next)) : EnumMetadata value :=
  (Session.query_preserves_metadata _ _ _ _ _ history.invariant history.metadata_invariant run).2

theorem Session.Reachable.memo_metadata {source : Environment} {session : Session}
    (history : Session.Reachable source session) (node : Nat) (value : Summary)
    (found : session.memo.find node = some value) : EnumMetadata value :=
  (history.invariant.2 node value found).satisfies history.metadata_invariant

/-- Public success aligns logical row, flag and discriminant counts and
establishes unique labels fitting the selected representation. -/
theorem query_metadata (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) : EnumMetadata value := by
  rcases query_session_derivation source mode ty value run with ⟨next, event, rest⟩
  exact Session.Reachable.query_metadata (Session.Reachable.prepared (source := source)) mode ty value event

theorem query_layout_invariants (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) :
    FinishBounds mode value ∧ StorageGeometry value ∧ PowerAlignment value ∧
      FieldAlignmentSummary value ∧ EnumEncodingGeometry value ∧ EnumMetadata value :=
  ⟨query_mode_bounds source mode ty value run, query_storage_geometry source mode ty value run,
    query_power_alignment source mode ty value run, query_field_alignment source mode ty value run,
    query_encoding_geometry source mode ty value run, query_metadata source mode ty value run⟩

theorem query_value_tag_fits (source : Environment) (mode : Mode) (ty : Ty) (value : Summary)
    (run : query source mode ty = .ok value) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration) :
    enumeration.discriminants.all enumeration.tag.fits = true := by
  have fits := ((query_metadata source mode ty value run) enumeration present).2.2.2
  have same : tagFits enumeration.tag = enumeration.tag.fits := by
    funext value
    exact tagFits_eval enumeration.tag value
  rw [same] at fits
  exact fits

namespace SessionControls

private def oldValue : Summary := { size := 7, align := some 1 }
private def newValue : Summary := { size := 8, align := some 8 }
private def staleGraph : Graph := { nodes := NatIndexTree.empty.insert 0 (.done (.ok oldValue)) }
private def stale : Session :=
  { index := Index.ofEnvironment {}, graph := staleGraph, memo := NatIndexTree.empty.insert 0 oldValue }
private def overwritten : Session :=
  { stale with
    graph := { staleGraph with nodes := staleGraph.nodes.insert 0 (.done (.ok newValue)), count := 1, leaves := NatIndexTree.empty.insert 521 0 }
    roots := NatIndexTree.empty.insert (2 * typeBucket .I64 + 1) [(.I64, .execution, 0)] }

/-- Initial memo evidence alone is insufficient when the allocator may reuse
    an existing equation's index. This memo genuinely has a valid derivation. -/
theorem stale_memo_is_derived : MemoDerivation stale.graph stale.memo := by
  change MemoDerivation staleGraph (NatIndexTree.empty.insert 0 oldValue)
  apply MemoDerivation.insert (MemoDerivation.empty _)
  exact .equation (equation := .done (.ok oldValue)) rfl rfl (.nil oldValue) rfl

/-- The real query compiler overwrites slot zero at the stale frontier and
    the existing fast path then returns its old cached value. -/
theorem stale_query_returns_old_cache :
    stale.query .execution .I64 = .ok (oldValue, overwritten) := rfl

/-- The overwritten graph no longer derives that old cache value. -/
theorem overwritten_memo_invalid : ¬ MemoDerivation overwritten.graph overwritten.memo := by
  intro valid
  have derived := valid 0 oldValue rfl
  have result := derived.done_result (show overwritten.graph.nodes.find 0 = some (.done (.ok newValue)) from rfl)
  have values : newValue = oldValue := Except.ok.inj result
  have sizes : (8 : Nat) = 7 := congrArg Summary.size values
  omega

/-- Preparation and the proved lifecycle cannot produce this forged session. -/
theorem stale_not_reachable (source : Environment) : ¬ Session.Reachable source stale := by
  intro history
  have absent := history.invariant.1.1 0 (Nat.le_refl _)
  cases absent

private def start : Session := prepare {}
private def checkedSession : Session :=
  ((start.query .execution .I64).toOption.getD (newValue, start)).2

theorem normal_first_query : start.query .execution .I64 = .ok (newValue, checkedSession) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem normal_repeat_query :
    checkedSession.query .execution .I64 = .ok (newValue, checkedSession) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem normal_repeat_invariant : checkedSession.DerivationInvariant :=
  (Session.query_preserves_derivation start .execution .I64 newValue checkedSession
    (prepare_derivation {}) normal_first_query).1

end SessionControls
namespace WordInvariantControls

private def oversized : Summary := { size := word64Limit, align := some 1 }
private def emptyGraph : Graph := {}
private def forged : Memo := NatIndexTree.empty.insert 0 oversized

theorem oversized_not_bounded : ¬ WordBounds 1 oversized := by
  intro bounded
  have positive : 0 < word64Limit := Nat.pow_pos (by decide)
  have smaller : word64Max < word64Limit := Nat.sub_lt positive (by decide)
  have bound : word64Limit ≤ word64Max := by
    simpa only [oversized, Nat.one_mul] using bounded.1
  exact Nat.not_le_of_gt smaller bound

theorem empty_graph_invariant : emptyGraph.WordInvariant :=
  Graph.SummaryInvariant.empty _ _

/-- Equation safety alone cannot license a caller-forged memo. -/
theorem forged_oversized_returned :
    solve emptyGraph .empty 0 forged = .ok (oversized, forged) :=
  solve_cached _ _ _ _ _ rfl

theorem forged_memo_invalid : ¬ MemoDerivation emptyGraph forged := by
  intro valid
  exact oversized_not_bounded ((valid 0 oversized rfl).satisfies empty_graph_invariant)

private def cyclic : Graph := { nodes := NatIndexTree.empty.insert 0 (Equation.alias 0), count := 1 }

theorem cyclic_alias_invariant : cyclic.WordInvariant := by
  intro node equation found
  change (NatIndexTree.empty.insert 0 (Equation.alias 0)).find node = some equation at found
  rw [NatIndexTree.find_insert] at found
  cases Nat.decEq node 0 with
  | isTrue same =>
    simp only [if_pos same] at found
    cases found
    exact .alias 0
  | isFalse different =>
    simp only [if_neg different] at found
    cases found

theorem cyclic_alias_refuses : cyclic.query 0 = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end WordInvariantControls

namespace IndexedInvariantControls

private def byteOnly : Summary := { size := word64Max, align := none }

theorem byte_only_execution : FinishBounds .execution byteOnly := by
  refine ⟨?_, ?_⟩
  · simp [WordBounds, byteOnly]
  · intro impossible
    cases impossible

theorem byte_only_not_shape : ¬ FinishBounds .shape byteOnly := by
  intro safe
  have positive : 0 < word64Max := by
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by decide : (64 : Nat) ≠ 0))
  have larger : word64Max < 8 * word64Max := by
    simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right (by decide : 1 < 8) positive
  exact Nat.not_le_of_gt larger ((safe.2 rfl).1)

private def mismatchedModes : Nat → Mode := fun node => if node == 0 then .shape else .execution
private def badAlias : Graph :=
  { nodes := NatIndexTree.empty.insert 1 (Equation.done (.ok byteOnly)) |>.insert 0 (Equation.alias 1)
    count := 2 }

/-- An execution-sized result really passes through an unguarded alias. -/
theorem wrong_mode_alias_returns : badAlias.query 0 = .ok byteOnly := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- Byte bounds at a child do not license bit bounds at a different root. -/
theorem wrong_mode_alias_has_no_invariant : ¬ badAlias.ModeInvariant mismatchedModes := by
  intro valid
  exact byte_only_not_shape (badAlias.query_mode_bounds mismatchedModes valid 0 byteOnly
    wrong_mode_alias_returns)

private def cyclic : Graph := { nodes := NatIndexTree.empty.insert 0 (Equation.alias 0), count := 1 }

theorem cyclic_mode_invariant : cyclic.ModeInvariant (fun _ => .shape) :=
  (Graph.IndexedInvariant.empty _ 1).insert 0 (Equation.alias 0)
    (Equation.mode_alias _ 0 0 rfl)

theorem cyclic_mode_refuses : cyclic.query 0 = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end IndexedInvariantControls

namespace ScalarInvariantControls

private def requested : Summary := { size := 2, align := some 2 }
private def counterfeit : Summary := { size := 1, align := some 66 }

theorem requested_scalar : ScalarSummary ByteModel.le64.pointerBytes requested :=
  .plain 2 (Or.inr (Or.inl rfl))

theorem arbitrary_key_collision : scalarKey counterfeit = scalarKey requested := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem colliding_values_differ : counterfeit ≠ requested := by
  intro same
  have sizes := congrArg Summary.size same
  exact (by decide : (1 : Nat) ≠ 2) sizes

/-- Bounds alone cannot distinguish the two different metadata records. -/
theorem counterfeit_shape_bounded : FinishBounds .shape counterfeit := by decide

private def forged : Graph :=
  { nodes := NatIndexTree.empty.insert 0 (Equation.done (.ok counterfeit))
    leaves := NatIndexTree.empty.insert (scalarKey requested) 0
    count := 1 }

theorem counterfeit_query_returns : forged.query 0 = .ok counterfeit := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem counterfeit_cache_invalid : ¬ forged.ScalarInvariant 0 ByteModel.le64.pointerBytes := by
  trustIrCompilerProof {
    intro valid
    have same := valid.derivation_value requested_scalar (by rfl)
      (forged.query_derivation 0 counterfeit counterfeit_query_returns)
    exact colliding_values_differ same
  } {
    intro valid
    have same := valid.derivation_value requested_scalar (by trustIrReduce)
      (forged.query_derivation 0 counterfeit counterfeit_query_returns)
    exact colliding_values_differ same
  }

end ScalarInvariantControls

namespace RootOriginControls

private def wide : Summary := { size := 16, align := some 8 }
private def sentinel : Summary := { size := 99, align := some 1 }
private def firstTy : Ty := .FatPtr .Str
private def secondTy : Ty := .FatPtr .ContainerLen
private def start : Session := prepare {}
private def first : Session := ((start.query .execution firstTy).toOption.getD (wide, start)).2
private def second : Session := ((first.query .execution secondTy).toOption.getD (wide, first)).2

theorem different_types_same_bucket : rootBucket .execution firstTy = rootBucket .execution secondTy := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem first_query : start.query .execution firstTy = .ok (wide, first) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem colliding_query : first.query .execution secondTy = .ok (wide, second) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- Sharing a scalar node does not collapse the two full type identities. -/
theorem colliding_entries_retained :
    (second.roots.find (rootBucket .execution firstTy)).getD [] =
      [(secondTy, .execution, 2), (firstTy, .execution, 2)] := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem colliding_history_compiled : second.RootsCompiled {} :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) first_query) colliding_query).roots_compiled

private def forged (bucketMode storedMode : Mode) : Session :=
  { index := Index.ofEnvironment {}
    graph := { count := 2, nodes := NatIndexTree.empty.insert 0 (Equation.done (.ok sentinel)) }
    memo := NatIndexTree.empty.insert 0 sentinel
    roots := NatIndexTree.empty.insert (rootBucket bucketMode firstTy) [(firstTy, storedMode, 0)] }

theorem wrong_type_entry_skipped :
    ((forged .execution .execution).query .execution secondTy).map Prod.fst = .ok wide := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem wrong_mode_entry_skipped :
    ((forged .shape .execution).query .shape firstTy).map Prod.fst = .ok wide := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- Derivation validity alone does not authenticate a root/type association. -/
theorem forged_derivation_valid : (forged .execution .execution).DerivationInvariant := by
  have bounded : (forged .execution .execution).graph.Bounded := by
    intro node outside
    change 2 ≤ node at outside
    change (NatIndexTree.empty.insert 0 (Equation.done (.ok sentinel))).find node = none
    rw [NatIndexTree.find_insert, if_neg (by omega : node ≠ 0)]
    rfl
  have derived : NodeDerivation (forged .execution .execution).graph 0 sentinel :=
    .equation rfl rfl (.nil sentinel) rfl
  exact ⟨⟨bounded, Nat.le_refl _⟩, (MemoDerivation.empty _).insert derived⟩

theorem forged_matching_entry_returned :
    (forged .execution .execution).query .execution firstTy =
      .ok (sentinel, forged .execution .execution) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forged_not_reachable : ¬ Session.Reachable {} (forged .execution .execution) := by
  trustIrCompilerProof {
    intro history
    let initial : Equation :=
      { kind := .unit, initial := .ok (), steps := [], finish := fun _ => .ok { size := 0, align := some 1 } }
    have preserved := history.extends_prepared 0 initial (by rfl)
    have different : Accumulator.summary = Accumulator.unit := congrArg Equation.kind (Option.some.inj preserved)
    cases different
  } {
    intro history
    let initial : Equation :=
      { kind := .unit, initial := .ok (), steps := [], finish := fun _ => .ok { size := 0, align := some 1 } }
    have preserved := history.extends_prepared 0 initial (by trustIrReduce)
    have different : Accumulator.summary = Accumulator.unit := congrArg Equation.kind (Option.some.inj preserved)
    cases different
  }

end RootOriginControls
namespace BuilderModeControls

private def wideStruct : StructDef :=
  { id := ⟨0⟩, name := "wide", fields := [], size := some (2 ^ 61), align := some 1 }
private def source : Environment := { structs := [wideStruct] }
private def wideValue : Summary := { size := 2 ^ 61, align := some 1 }
private def before : Graph := {}
private def built (mode : Mode) : Equation :=
  declaredFields mode "struct" 0 (2 ^ 61) 1 word64Max false []

theorem actual_struct_construction (mode : Mode) :
    StructCompilation (Index.ofEnvironment source) mode wideStruct before (built mode) before := by
  trustIrCompilerProof {
    cases mode <;> rfl
  } {
    cases mode <;> trustIrReduce
  }

theorem actual_struct_guarded (mode : Mode) : (built mode).ModeGuarded mode :=
  (actual_struct_construction mode).mode_guarded

theorem execution_accepts_byte_only : query source .execution (.Struct ⟨0⟩) = .ok wideValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem shape_refuses_byte_only : query source .shape (.Struct ⟨0⟩) = .error .sizeOverflow := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem accepted_not_shape : ¬ FinishBounds .shape wideValue := by
  intro safe
  have overflow := (safe.2 rfl).1
  change 8 * 2 ^ 61 ≤ word64Max at overflow
  have impossible : ¬ (8 * 2 ^ 61 ≤ word64Max) := by decide
  exact impossible overflow

theorem actual_shape_reserved : (Index.ofEnvironment source).nodeMode 0 = .shape := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_execution_reserved : (Index.ofEnvironment source).nodeMode 1 = .execution := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def closureSource : Environment :=
  { hasTargetInfo := true
    closures := [ClosureTy.bare ⟨0⟩]
    closureLayouts := [{ closure := ⟨0⟩, size := 16, align := 8, captureOffsets := [] }] }
private def closureBuilt : Equation := declaredFields .shape "closure" 0 16 8 word64Max false []

theorem actual_closure_construction :
    ClosureCompilation (Index.ofEnvironment closureSource) 0 (ClosureTy.bare ⟨0⟩)
      before closureBuilt before := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_closure_guarded : closureBuilt.ModeGuarded .shape :=
  actual_closure_construction.mode_guarded

theorem shape_closure_accepts :
    query closureSource .shape (.Closure ⟨0⟩) = .ok { size := 16, align := some 8 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem execution_closure_refuses :
    query closureSource .execution (.Closure ⟨0⟩) = .error (.unsupported (.Closure ⟨0⟩)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end BuilderModeControls
namespace ShapeModeControls

private def scalarValue : Summary := { size := 8, align := some 8 }
private def start : Session := prepare {}
private def execution : Session := ((start.query .execution .I64).toOption.getD (scalarValue, start)).2
private def shaped : Session := ((execution.query .shape .I64).toOption.getD (scalarValue, execution)).2

theorem execution_first : start.query .execution .I64 = .ok (scalarValue, execution) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem shared_scalar_shape : execution.query .shape .I64 = .ok (scalarValue, shaped) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem shape_repeated : shaped.query .shape .I64 = .ok (scalarValue, shaped) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem shared_history_modes : shaped.graph.ModeInvariant shaped.index.nodeMode :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).mode_invariant

theorem shared_root_retained :
    (shaped.roots.find (rootBucket .shape .I64)).getD [] = [(.I64, .shape, 2)] := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem typed_cached_shape_bounds : FinishBounds .shape scalarValue := by
  trustIrCompilerProof {
    let history : Session.Reachable {} shaped :=
      .queried (.queried (.prepared) execution_first) shared_scalar_shape
    exact history.cached_root_mode_bounds (rootBucket .shape .I64) .I64 .shape 2 scalarValue
      (by rw [shared_root_retained]; exact (trustIrListMemConsSelf _ _)) (by rfl)
  } {
    let history : Session.Reachable {} shaped :=
      .queried (.queried (.prepared) execution_first) shared_scalar_shape
    exact history.cached_root_mode_bounds (rootBucket .shape .I64) .I64 .shape 2 scalarValue
      (by rw [shared_root_retained]; exact (trustIrListMemConsSelf _ _)) (by trustIrReduce)
  }

private def unitValue : Summary := { size := 0, align := some 1 }
private def tupled : Session := ((start.query .shape (.Tuple [])).toOption.getD (unitValue, start)).2

theorem dynamic_shape_query : start.query .shape (.Tuple []) = .ok (unitValue, tupled) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem dynamic_index_obligation : tupled.index.nodeMode 2 = .execution := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem dynamic_local_shape_guard : ShapeRoot tupled.index tupled.graph 2 := by
  trustIrCompilerProof {
    exact Or.inr ⟨canonicalFields .shape "tuple" 0 [], rfl, Equation.ModeGuarded.canonicalFields _ _ _ _⟩
  } {
    exact Or.inr ⟨canonicalFields .shape "tuple" 0 [], (by trustIrReduce), Equation.ModeGuarded.canonicalFields _ _ _ _⟩
  }

theorem dynamic_result_bounds : FinishBounds .shape unitValue :=
  Session.Reachable.query_mode_bounds (.prepared) .shape (.Tuple []) unitValue dynamic_shape_query

private def sparse : Environment :=
  { structs := [{ id := ⟨99⟩, name := "sparse", fields := [], size := some 8, align := some 8 }] }

theorem sparse_shape : query sparse .shape (.Struct ⟨99⟩) = .ok scalarValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem sparse_missing_refuses : query sparse .shape (.Struct ⟨0⟩) = .error (.missingStruct 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def cyclic : Environment := { types := [some (.Array ⟨0⟩ 1)] }

theorem cyclic_preparation_modes : (prepare cyclic).graph.ModeInvariant (prepare cyclic).index.nodeMode :=
  prepare_modes cyclic

theorem cyclic_shape_refuses : query cyclic .shape (.Refine ⟨0⟩ ⟨0⟩) = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem shared_history_storage : shaped.graph.StorageInvariant (2 * shaped.index.count + 2) :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).storage_invariant

theorem repeated_cached_storage : StorageGeometry scalarValue :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).query_storage_geometry .shape .I64 scalarValue shape_repeated

theorem shared_memo_storage : StorageGeometry scalarValue := by
  trustIrCompilerProof {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_storage_geometry 2 scalarValue (by rfl)
  } {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_storage_geometry 2 scalarValue (by trustIrReduce)
  }

theorem dynamic_result_storage : StorageGeometry unitValue :=
  Session.Reachable.query_storage_geometry (.prepared) .shape (.Tuple []) unitValue dynamic_shape_query

theorem shared_history_power_alignment : shaped.graph.PowerAlignmentInvariant :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).power_alignment_invariant

theorem repeated_cached_power_alignment : PowerAlignment scalarValue :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).query_power_alignment
    .shape .I64 scalarValue shape_repeated

theorem shared_memo_power_alignment : PowerAlignment scalarValue := by
  trustIrCompilerProof {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_power_alignment
      2 scalarValue (by rfl)
  } {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_power_alignment
      2 scalarValue (by trustIrReduce)
  }

theorem dynamic_result_power_alignment : PowerAlignment unitValue :=
  Session.Reachable.query_power_alignment (.prepared) .shape (.Tuple []) unitValue dynamic_shape_query

theorem shared_history_field_alignment : shaped.graph.FieldAlignmentInvariant (2 * shaped.index.count + 2) :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).field_alignment_invariant

theorem repeated_cached_field_alignment : FieldAlignmentSummary scalarValue :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).query_field_alignment
    .shape .I64 scalarValue shape_repeated

theorem shared_memo_field_alignment : FieldAlignmentSummary scalarValue := by
  trustIrCompilerProof {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_field_alignment
      2 scalarValue (by rfl)
  } {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_field_alignment
      2 scalarValue (by trustIrReduce)
  }

theorem shared_history_encoding : shaped.graph.EncodingInvariant :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).encoding_invariant

theorem repeated_cached_encoding : EnumEncodingGeometry scalarValue :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).query_encoding_geometry
    .shape .I64 scalarValue shape_repeated

theorem shared_memo_encoding : EnumEncodingGeometry scalarValue := by
  trustIrCompilerProof {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_encoding_geometry
      2 scalarValue (by rfl)
  } {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_encoding_geometry
      2 scalarValue (by trustIrReduce)
  }

theorem shared_history_metadata : shaped.graph.MetadataInvariant :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).metadata_invariant

theorem repeated_cached_metadata : EnumMetadata scalarValue :=
  (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).query_metadata
    .shape .I64 scalarValue shape_repeated

theorem shared_memo_metadata : EnumMetadata scalarValue := by
  trustIrCompilerProof {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_metadata
      2 scalarValue (by rfl)
  } {
    exact (Session.Reachable.queried (Session.Reachable.queried (.prepared) execution_first) shared_scalar_shape).memo_metadata
      2 scalarValue (by trustIrReduce)
  }

end ShapeModeControls
namespace GeometryControls

private def pairTy : Ty := .Tuple [.I32, .I32]
private def pairSource (offsets : List Nat) : Environment :=
  { hasTargetInfo := true, types := [some pairTy]
    tupleLayouts := [{ tupleType := ⟨0⟩, size := 8, align := 4, fieldOffsets := offsets }] }
private def pairValue : Summary :=
  { size := 8, align := some 4
    fields := [{ ty := .I32, offset := 0, size := 4, align := 4 },
      { ty := .I32, offset := 4, size := 4, align := 4 }] }

theorem touching_shape_accepts : query (pairSource [0, 4]) .shape pairTy = .ok pairValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem touching_execution_accepts : query (pairSource [0, 4]) .execution pairTy = .ok pairValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem overlapping_refuses : query (pairSource [0, 0]) .shape pairTy = .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem out_of_range_refuses : query (pairSource [0, 12]) .shape pairTy = .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def zeroTy : Ty := .Tuple [.I64, .Unit]
private def zeroSource : Environment :=
  { hasTargetInfo := true, types := [some zeroTy]
    tupleLayouts := [{ tupleType := ⟨0⟩, size := 8, align := 8, fieldOffsets := [0, 4] }] }

theorem empty_inside_storage_accepts : query zeroSource .shape zeroTy = .ok
    { size := 8, align := some 8
      fields := [{ ty := .I64, offset := 0, size := 8, align := 8 },
        { ty := .Unit, offset := 4, size := 0, align := 1 }] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def omittedSource : Environment :=
  { structs :=
      [{ id := ⟨0⟩, name := "outer", fields := [{ name := "empty", ty := .Struct ⟨1⟩, offset := none }],
         size := some 0, align := some 1 },
       { id := ⟨1⟩, name := "empty", fields := [], size := some 0, align := some 8 }] }
private def omittedValue : Summary :=
  { size := 0, align := some 1, fields := [{ ty := .Struct ⟨1⟩, offset := 0, size := 0, align := 8 }] }

theorem omitted_empty_execution_accepts : query omittedSource .execution (.Struct ⟨0⟩) = .ok omittedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem omitted_empty_shape_refuses :
    query omittedSource .shape (.Struct ⟨0⟩) = .error (.incoherent "struct" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem unconditional_alignment_bound_false :
    ¬ (∀ field, field ∈ omittedValue.fields → field.align ≤ omittedValue.align.getD 1) := by
  intro bound
  have impossible : 8 ≤ 1 := bound _ ((trustIrListMemConsSelf _ _))
  omega

theorem canonical_padding_accepts : query {} .execution (.Tuple [.I8, .I64, .I8]) = .ok
    { size := 24, align := some 8
      fields := [{ ty := .I8, offset := 0, size := 1, align := 1 },
        { ty := .I64, offset := 8, size := 8, align := 8 },
        { ty := .I8, offset := 16, size := 1, align := 1 }] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def pairStruct : StructDef :=
  { id := ⟨0⟩, name := "pair"
    fields := [{ name := "x", ty := .I32, offset := some 0 }, { name := "y", ty := .I32, offset := some 4 }]
    size := some 8, align := some 4 }
private def scalar : Summary := { size := 4, align := some 4 }
private def before : Graph := {}
private def after : Graph :=
  { count := 1, nodes := NatIndexTree.empty.insert 0 (Equation.done (.ok scalar))
    leaves := NatIndexTree.empty.insert (scalarKey scalar) 0 }
private def pairEquation (mode : Mode) (kind : String) : Equation :=
  declaredFields mode kind 0 8 4 word64Max false [(.I32, some 0, 0), (.I32, some 4, 0)]
private def pairGraph (kind : String) : Graph :=
  { after with count := 2, nodes := after.nodes.insert 1 (pairEquation .shape kind) }

theorem actual_struct_pair (mode : Mode) :
    StructCompilation (Index.ofEnvironment {}) mode pairStruct before (pairEquation mode "struct") after := by
  trustIrCompilerProof {
    cases mode <;> rfl
  } {
    cases mode <;> trustIrReduce
  }

theorem actual_struct_derivation : (pairGraph "struct").query 1 = .ok pairValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_struct_geometry : FieldGeometry pairValue := by
  trustIrCompilerProof {
    exact (actual_struct_pair .shape).derivation_geometry (by rfl)
      ((pairGraph "struct").query_derivation 1 pairValue actual_struct_derivation)
  } {
    exact (actual_struct_pair .shape).derivation_geometry (by trustIrReduce)
      ((pairGraph "struct").query_derivation 1 pairValue actual_struct_derivation)
  }

private def closure : ClosureTy := { func := ⟨0⟩, captures := [.I32, .I32] }
private def closureSource : Environment :=
  { hasTargetInfo := true, closures := [closure]
    closureLayouts := [{ closure := ⟨0⟩, size := 8, align := 4, captureOffsets := [0, 4] }] }

theorem actual_closure_pair : ClosureCompilation (Index.ofEnvironment closureSource) 0 closure before
    (pairEquation .shape "closure") after := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_closure_derivation : (pairGraph "closure").query 1 = .ok pairValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_closure_geometry : FieldGeometry pairValue := by
  trustIrCompilerProof {
    exact actual_closure_pair.derivation_geometry (by rfl)
      ((pairGraph "closure").query_derivation 1 pairValue actual_closure_derivation)
  } {
    exact actual_closure_pair.derivation_geometry (by trustIrReduce)
      ((pairGraph "closure").query_derivation 1 pairValue actual_closure_derivation)
  }

theorem actual_closure_query : query closureSource .shape (.Closure ⟨0⟩) = .ok pairValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def omittedPositive : Environment :=
  { structs := [{ id := ⟨0⟩, name := "missing", fields := [{ name := "x", ty := .I32, offset := none }], size := some 4, align := some 4 }] }

theorem omitted_positive_refuses :
    query omittedPositive .execution (.Struct ⟨0⟩) = .error (.incoherent "struct" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def forgedPlacement : PlacementState :=
  { cursor := 8, align := 4, fields := [{ ty := .I32, offset := 16, size := 4, align := 4 }] }
private def forgedValue : Summary := { size := 8, align := some 4, fields := forgedPlacement.fields }

theorem canonical_finalizer_accepts_forged_state :
    (canonicalFields .shape "tuple" 0 []).finish forgedPlacement = .ok forgedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forged_geometry_false : ¬ FieldGeometry forgedValue := by
  intro geometry
  have impossible : 20 ≤ 8 := geometry.2 _ ((trustIrListMemConsSelf _ _))
  omega

theorem canonical_finalizer_alone_insufficient :
    ¬ (canonicalFields .shape "tuple" 0 []).Finalizes FieldGeometry := by
  intro finalizer
  exact forged_geometry_false (finalizer forgedPlacement forgedValue canonical_finalizer_accepts_forged_state)

theorem forged_placement_not_derived (graph : Graph) :
    ¬ StepsDerivation graph (canonicalFields .shape "tuple" 0 []).steps ({} : PlacementState) forgedPlacement := by
  intro steps
  cases steps

end GeometryControls
namespace AlignmentControls

theorem zero_divisor_refuses : alignUp 1 0 = .error (.incoherent "alignment" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem rounding_overflow_refuses : alignUp word64Max 8 = .error .sizeOverflow := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem non_power_divisor_rounds : alignUp 10 3 = .ok 12 := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def tupleSource (ty : Ty) (size align : Nat) (offsets : List Nat) : Environment :=
  { hasTargetInfo := true, types := [some ty]
    tupleLayouts := [{ tupleType := ⟨0⟩, size, align, fieldOffsets := offsets }] }

theorem misaligned_field_refuses :
    query (tupleSource (.Tuple [.I32]) 8 4 [2]) .shape (.Tuple [.I32]) =
      .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem excessive_field_alignment_refuses :
    query (tupleSource (.Tuple [.I64]) 8 4 [0]) .shape (.Tuple [.I64]) =
      .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem nonmultiple_size_refuses :
    query (tupleSource (.Tuple [.I32]) 6 4 [0]) .shape (.Tuple [.I32]) =
      .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem zero_aggregate_alignment_refuses :
    query (tupleSource (.Tuple []) 0 0 []) .shape (.Tuple []) = .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem nonpower_aggregate_alignment_refuses :
    query (tupleSource (.Tuple []) 0 3 []) .shape (.Tuple []) = .error (.incoherent "tuple" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def packed : StructDef :=
  { id := ⟨0⟩, name := "packed", fields := [{ name := "x", ty := .I64, offset := some 0 }]
    size := some 8, align := some 1, repr := .packed 1 }
private def packedValue : Summary :=
  { size := 8, align := some 1, fields := [{ ty := .I64, offset := 0, size := 8, align := 1 }] }
private def scalar : Summary := { size := 8, align := some 8 }
private def scalarGraph : Graph :=
  { count := 1, nodes := NatIndexTree.empty.insert 0 (Equation.done (.ok scalar))
    leaves := NatIndexTree.empty.insert (scalarKey scalar) 0 }
private def packedEquation (mode : Mode) : Equation :=
  declaredFields mode "struct" 0 8 1 1 false [(.I64, some 0, 0)]
private def packedGraph : Graph :=
  { scalarGraph with count := 2, nodes := scalarGraph.nodes.insert 1 (packedEquation .shape) }

theorem packed_query_accepts : query { structs := [packed] } .shape (.Struct ⟨0⟩) = .ok packedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_packed_construction (mode : Mode) :
    StructCompilation (Index.ofEnvironment {}) mode packed {} (packedEquation mode) scalarGraph := by
  trustIrCompilerProof {
    cases mode <;> rfl
  } {
    cases mode <;> trustIrReduce
  }

theorem actual_packed_derivation : packedGraph.query 1 = .ok packedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_packed_alignment : AlignmentGeometry (fun _ => True) packedValue := by
  trustIrCompilerProof {
    exact ((actual_packed_construction .shape).derivation_alignment (by rfl)
      (packedGraph.query_derivation 1 packedValue actual_packed_derivation)).weaken
        (fun _ _ => Or.inr (Or.inl rfl))
  } {
    exact ((actual_packed_construction .shape).derivation_alignment (by trustIrReduce)
      (packedGraph.query_derivation 1 packedValue actual_packed_derivation)).weaken
        (fun _ _ => Or.inr (Or.inl rfl))
  }

private def omittedStruct : StructDef :=
  { id := ⟨0⟩, name := "outer", fields := [{ name := "empty", ty := .Struct ⟨1⟩, offset := none }]
    size := some 0, align := some 1 }
private def emptyStruct : StructDef :=
  { id := ⟨1⟩, name := "empty", fields := [], size := some 0, align := some 8 }
private def omittedSource : Environment := { structs := [omittedStruct, emptyStruct] }
private def omittedValue : Summary :=
  { size := 0, align := some 1, fields := [{ ty := .Struct ⟨1⟩, offset := 0, size := 0, align := 8 }] }
private def before : Graph :=
  { count := 6, nodes := NatIndexTree.empty.insert 3 (Equation.done (.ok { size := 0, align := some 8 })) }
private def omittedEquation : Equation :=
  declaredFields .execution "struct" 0 0 1 word64Max false [(.Struct ⟨1⟩, none, 3)]
private def omittedGraph : Graph := { before with count := 7, nodes := before.nodes.insert 6 omittedEquation }

theorem omitted_query_accepts : query omittedSource .execution (.Struct ⟨0⟩) = .ok omittedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_omitted_construction :
    StructCompilation (Index.ofEnvironment omittedSource) .execution omittedStruct before omittedEquation before := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_omitted_derivation : omittedGraph.query 6 = .ok omittedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem omitted_alignment_preserved :
    AlignmentGeometry (FieldAlignmentRequired .execution "struct") omittedValue := by
  trustIrCompilerProof {
    exact actual_omitted_construction.derivation_alignment (by rfl)
      (omittedGraph.query_derivation 6 omittedValue actual_omitted_derivation)
  } {
    exact actual_omitted_construction.derivation_alignment (by trustIrReduce)
      (omittedGraph.query_derivation 6 omittedValue actual_omitted_derivation)
  }

theorem omitted_unconditional_cap_false :
    ¬ (∀ field, field ∈ omittedValue.fields → field.align ≤ omittedValue.align.getD 1) :=
  GeometryControls.unconditional_alignment_bound_false

theorem closure_all_fields_aligned : AlignmentGeometry (fun _ => True)
    { size := 8, align := some 4
      fields := [{ ty := .I32, offset := 0, size := 4, align := 4 },
        { ty := .I32, offset := 4, size := 4, align := 4 }] } := by
  trustIrCompilerProof {
    exact GeometryControls.actual_closure_pair.derivation_alignment (by rfl)
      (Graph.query_derivation _ _ _ GeometryControls.actual_closure_derivation)
  } {
    exact GeometryControls.actual_closure_pair.derivation_alignment (by trustIrReduce)
      (Graph.query_derivation _ _ _ GeometryControls.actual_closure_derivation)
  }

theorem packed_public_layout_geometry :
    FinishBounds .shape packedValue ∧ StorageGeometry packedValue ∧ PowerAlignment packedValue ∧ FieldAlignmentSummary packedValue :=
  query_layout_geometry { structs := [packed] } .shape (.Struct ⟨0⟩) packedValue packed_query_accepts

end AlignmentControls
namespace EnumGeometryControls

set_option maxRecDepth 8192

private def definition : EnumDef :=
  { id := ⟨0⟩, name := "union", variants := [{ name := "small", fields := [.I32] }, { name := "wide", fields := [.I64] }] }
private def small : Summary :=
  { size := 4, align := some 4, fields := [{ ty := .I32, offset := 0, size := 4, align := 4 }] }
private def wide : Summary :=
  { size := 8, align := some 8, fields := [{ ty := .I64, offset := 0, size := 8, align := 8 }] }
private def result : Summary :=
  { size := 16, align := some 8
    enumeration := some { tag := .u8, discriminants := [0, 1], encoding := .direct 0, variants := [[{ ty := .I32, offset := 8, size := 4, align := 4 }], [{ ty := .I64, offset := 8, size := 8, align := 8 }]], uninhabited := [false, false] } }
private def graph : Graph :=
  { count := 3, nodes := ((NatIndexTree.empty.insert 0 (Equation.done (.ok small))).insert 1
      (Equation.done (.ok wide))).insert 2 (enumEquation .shape definition [false, false] [0, 1]) }

private theorem single_geometry (ty : Ty) (size align : Nat) :
    FieldGeometry { size, align := some align, fields := [{ ty, offset := 0, size, align }] } := by
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · intro field impossible; cases impossible
  · intro field member
    cases member with
    | head => change 0 + size ≤ size; omega
    | tail _ impossible => cases impossible

private theorem done_value {graph : Graph} {node : Nat} {value expected : Summary}
    (found : graph.nodes.find node = some (Equation.done (.ok expected)))
    (derived : NodeDerivation graph node value) : value = expected := by
  cases derived with
  | equation actual initial steps finished =>
    rw [found] at actual
    cases actual
    cases steps
    exact (Except.ok.inj (initial.trans finished)).symm

theorem variant_children_geometry (node : Nat) (member : node ∈ [0, 1]) (value : Summary)
    (derived : NodeDerivation graph node value) : FieldGeometry value := by
  cases member with
  | head =>
    have same := done_value (by rfl : graph.nodes.find 0 = some (Equation.done (.ok small))) derived
    rw [same]
    exact single_geometry _ _ _
  | tail _ member =>
    cases member with
    | head =>
      have same := done_value (by rfl : graph.nodes.find 1 = some (Equation.done (.ok wide))) derived
      rw [same]
      exact single_geometry _ _ _
    | tail _ impossible => cases impossible

theorem actual_graph_query : graph.query 2 = .ok result := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_graph_geometry : EnumerationGeometry result := by
  trustIrCompilerProof {
    exact NodeDerivation.canonicalEnum_geometry .shape definition [false, false] [0, 1] rfl variant_children_geometry
      (by rfl) (graph.query_derivation 2 result actual_graph_query)
  } {
    exact NodeDerivation.canonicalEnum_geometry .shape definition [false, false] [0, 1] rfl variant_children_geometry
      (by trustIrReduce) (graph.query_derivation 2 result actual_graph_query)
  }

theorem actual_graph_tag_separated :
    ∀ enumeration, result.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap 0 (tagBits enumeration.tag / 8) field.offset field.size = false := by
  trustIrCompilerProof {
    exact NodeDerivation.canonicalEnum_tag_separated .shape definition [false, false] [0, 1] rfl
      (by rfl) (graph.query_derivation 2 result actual_graph_query)
  } {
    exact NodeDerivation.canonicalEnum_tag_separated .shape definition [false, false] [0, 1] rfl
      (by trustIrReduce) (graph.query_derivation 2 result actual_graph_query)
  }

theorem source_shape_query : query { enums := [definition] } .shape (.Enum ⟨0⟩) = .ok result := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem source_execution_query : query { enums := [definition] } .execution (.Enum ⟨0⟩) = .ok result := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem mutually_exclusive_variants_share_storage : overlap 8 4 8 8 = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def corrupt : Summary :=
  { size := 1, align := some 1, fields := [{ ty := .I8, offset := 8, size := 1, align := 1 }] }
private def corruptResult : Summary :=
  { size := 2, align := some 1
    enumeration := some { tag := .u8, discriminants := [0], encoding := .direct 0, variants := [[{ ty := .I8, offset := 9, size := 1, align := 1 }]], uninhabited := [false] } }
private def single : EnumDef := { id := ⟨0⟩, name := "bad", variants := [{ name := "only", fields := [.I8] }] }

theorem raw_finalizer_accepts_corrupt_child :
    EnumConstruction .shape single .u8 [0] [false] [corrupt] corruptResult := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem corrupt_child_geometry_false : ¬ FieldGeometry corrupt := by
  intro geometry
  have impossible : 9 ≤ 1 := geometry.2 _ ((trustIrListMemConsSelf _ _))
  omega

theorem corrupt_enum_geometry_false : ¬ EnumerationGeometry corruptResult := by
  intro geometry
  have fields := geometry _ rfl _ ((trustIrListMemConsSelf _ _))
  have impossible : 10 ≤ 2 := fields.2 _ ((trustIrListMemConsSelf _ _))
  omega

theorem corrupt_tag_still_separated :
    ∀ enumeration, corruptResult.enumeration = some enumeration →
      ∀ fields, fields ∈ enumeration.variants → ∀ field, field ∈ fields →
        overlap 0 1 field.offset field.size = false :=
  raw_finalizer_accepts_corrupt_child.canonical_tag_separated rfl

theorem canonical_public_storage : StorageGeometry result :=
  query_storage_geometry { enums := [definition] } .shape (.Enum ⟨0⟩) result source_shape_query

theorem canonical_public_power_alignment : PowerAlignment result :=
  query_power_alignment { enums := [definition] } .shape (.Enum ⟨0⟩) result source_shape_query

theorem canonical_public_field_alignment : FieldAlignmentSummary result :=
  query_field_alignment { enums := [definition] } .shape (.Enum ⟨0⟩) result source_shape_query

theorem canonical_public_encoding : EnumEncodingGeometry result :=
  query_encoding_geometry { enums := [definition] } .shape (.Enum ⟨0⟩) result source_shape_query

theorem canonical_public_metadata : EnumMetadata result :=
  query_metadata { enums := [definition] } .shape (.Enum ⟨0⟩) result source_shape_query

end EnumGeometryControls
namespace DescriptorEnumControls

set_option maxRecDepth 8192

private def direct : EnumLayoutDescriptor :=
  { encoding := .direct 0, size := 8, align := 4, variantFieldOffsets := [[4], []] }
private def definition (descriptor : EnumLayoutDescriptor) : EnumDef :=
  { id := ⟨0⟩, name := "descriptor", variants := [{ name := "some", fields := [.I32] }, { name := "none", fields := [] }], layout := some descriptor }
private def small : Summary :=
  { size := 8, align := some 4, fields := [{ ty := .I32, offset := 4, size := 4, align := 4 }] }
private def empty : Summary := { size := 8, align := some 4 }
private def directValue : Summary :=
  { size := 8, align := some 4
    enumeration := some { tag := .u8, discriminants := [0, 1], encoding := .direct 0, variants := [small.fields, []], uninhabited := [false, false] } }
private def directGraph : Graph :=
  { count := 3, nodes := ((NatIndexTree.empty.insert 0 (Equation.done (.ok small))).insert 1
      (Equation.done (.ok empty))).insert 2 (enumEquation .shape (definition direct) [false, false] [0, 1]) }

private theorem done_value {graph : Graph} {node : Nat} {value expected : Summary}
    (found : graph.nodes.find node = some (Equation.done (.ok expected)))
    (derived : NodeDerivation graph node value) : value = expected := by
  cases derived with
  | equation actual initial steps finished =>
    rw [found] at actual
    cases actual
    cases steps
    exact (Except.ok.inj (initial.trans finished)).symm

private theorem one_field (ty : Ty) (offset size align parent : Nat) (bound : offset + size ≤ parent) :
    FieldsSeparated [{ ty, offset, size, align }] ∧ FieldsContained parent [{ ty, offset, size, align }] := by
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · intro field impossible; cases impossible
  · intro field member
    cases member with
    | head => exact bound
    | tail _ impossible => cases impossible

theorem direct_children (node : Nat) (member : node ∈ [0, 1]) (value : Summary)
    (derived : NodeDerivation directGraph node value) :
    FieldsSeparated value.fields ∧ FieldsContained direct.size value.fields := by
  cases member with
  | head =>
    rw [done_value (by rfl : directGraph.nodes.find 0 = some (Equation.done (.ok small))) derived]
    exact one_field _ _ _ _ _ (by decide)
  | tail _ member =>
    cases member with
    | head =>
      rw [done_value (by rfl : directGraph.nodes.find 1 = some (Equation.done (.ok empty))) derived]
      exact ⟨trivial, by intro field impossible; cases impossible⟩
    | tail _ impossible => cases impossible

theorem direct_graph_query : directGraph.query 2 = .ok directValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem direct_geometry : EnumerationGeometry directValue := by
  trustIrCompilerProof {
    exact NodeDerivation.descriptorEnum_geometry .shape (definition direct) [false, false] [0, 1] direct rfl
      direct_children (by rfl) (directGraph.query_derivation 2 directValue direct_graph_query)
  } {
    exact NodeDerivation.descriptorEnum_geometry .shape (definition direct) [false, false] [0, 1] direct rfl
      direct_children (by trustIrReduce) (directGraph.query_derivation 2 directValue direct_graph_query)
  }

theorem direct_source_shape : query { enums := [definition direct] } .shape (.Enum ⟨0⟩) = .ok directValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem direct_source_execution : query { enums := [definition direct] } .execution (.Enum ⟨0⟩) = .ok directValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem direct_overlap_refuses :
    query { enums := [definition { direct with variantFieldOffsets := [[0], []] }] } .shape (.Enum ⟨0⟩) =
      .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def emptyDefinition (offset : Nat) : EnumDef :=
  { id := ⟨0⟩, name := "lane", variants := [{ name := "a", fields := [] }, { name := "b", fields := [] }]
    tagRepr := some .u32, layout := some { encoding := .direct offset, size := 8, align := 4, variantFieldOffsets := [[], []] } }

theorem unaligned_tag_refuses :
    query { enums := [emptyDefinition 1] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem out_of_range_tag_refuses :
    query { enums := [emptyDefinition 8] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def niche : EnumLayoutDescriptor :=
  { encoding := .niche 0 1 1 0 0 .u8, size := 1, align := 1, variantFieldOffsets := [[0], []] }
private def nicheDefinition (descriptor : EnumLayoutDescriptor) : EnumDef :=
  { id := ⟨0⟩, name := "niche", variants := [{ name := "carrier", fields := [.I8] }, { name := "empty", fields := [] }], layout := some descriptor }
private def carrier : Summary :=
  { size := 1, align := some 1, fields := [{ ty := .I8, offset := 0, size := 1, align := 1 }] }
private def nicheValue : Summary :=
  { size := 1, align := some 1
    enumeration := some { tag := .u8, discriminants := [0, 1], encoding := .niche 0 1 1 0 0 .u8, variants := [carrier.fields, []], uninhabited := [false, false] } }

theorem niche_construction : EnumConstruction .shape (nicheDefinition niche) .u8 [0, 1] [false, false]
    [carrier, { size := 1, align := some 1 }] nicheValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem niche_source_shape : query { enums := [nicheDefinition niche] } .shape (.Enum ⟨0⟩) = .ok nicheValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem niche_source_execution : query { enums := [nicheDefinition niche] } .execution (.Enum ⟨0⟩) = .ok nicheValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem niche_lane_within_parent : EnumLaneBounds 1 1 0 1 1 :=
  niche_construction.niche_lane niche rfl 0 1 1 0 0 .u8 rfl

theorem niche_carrier_witness : ∃ field, field ∈ carrier.fields ∧ field.size ≠ 0 ∧ field.offset ≤ 0 ∧ 1 ≤ field.offset + field.size :=
  niche_construction.niche_carrier niche rfl 0 1 1 0 0 .u8 rfl _ rfl

theorem niche_invalid_interval_refuses :
    query { enums := [nicheDefinition { niche with encoding := .niche 0 2 1 0 0 .u8 }] } .shape (.Enum ⟨0⟩) =
      .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem niche_mask_overflow_refuses :
    query { enums := [nicheDefinition { niche with encoding := .niche 0 1 1 256 0 .u8 }] } .shape (.Enum ⟨0⟩) =
      .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def noCarrier : EnumDef :=
  { id := ⟨0⟩, name := "missing", variants := [{ name := "a", fields := [] }, { name := "b", fields := [] }]
    layout := some { niche with variantFieldOffsets := [[], []] } }

theorem missing_carrier_refuses :
    query { enums := [noCarrier] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def overlappingNiche : EnumDef :=
  { id := ⟨0⟩, name := "collision", variants := [{ name := "a", fields := [.I8] }, { name := "b", fields := [.I8] }]
    layout := some { niche with variantFieldOffsets := [[0], [0]] } }

theorem encoded_payload_overlap_refuses :
    query { enums := [overlappingNiche] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def uncovered : EnumDef :=
  { id := ⟨0⟩, name := "uncovered", variants := [{ name := "a", fields := [.I8] }, { name := "b", fields := [] }, { name := "c", fields := [] }]
    layout := some { niche with variantFieldOffsets := [[0], [], []] } }

theorem uncovered_inhabited_row_refuses :
    query { enums := [uncovered] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    simp only [query, prepare, Session.query]
    rfl
  } {
    trustIrReduce
  }

private def single : EnumDef :=
  { id := ⟨0⟩, name := "single", variants := [{ name := "a", fields := [.I8] }, { name := "impossible", fields := [.Never] }]
    layout := some { encoding := .singleInhabited 0, size := 1, align := 1, variantFieldOffsets := [[0], []] } }
private def singleValue : Summary :=
  { size := 1, align := some 1
    enumeration := some { tag := .u8, discriminants := [0, 1], encoding := .singleInhabited 0, variants := [carrier.fields, []], uninhabited := [false, true] } }

theorem single_inhabited_preserves_rows : query { enums := [single] } .shape (.Enum ⟨0⟩) = .ok singleValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def badSingle : EnumDef :=
  { single with layout := some { encoding := .singleInhabited 0, size := 1, align := 1, variantFieldOffsets := [[0], [0]] } }

set_option maxHeartbeats 1000000 in
theorem inactive_offsets_refuse :
    query { enums := [badSingle] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def untagged : EnumDef :=
  { id := ⟨0⟩, name := "untagged", variants := [{ name := "a", fields := [.I8] }]
    layout := some { encoding := .untagged, size := 1, align := 1, variantFieldOffsets := [[0]] } }
private def untaggedValue : Summary :=
  { size := 1, align := some 1
    enumeration := some { tag := .u8, discriminants := [0], encoding := .untagged, variants := [carrier.fields], uninhabited := [false] } }

theorem one_untagged_row_accepts : query { enums := [untagged] } .shape (.Enum ⟨0⟩) = .ok untaggedValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem multiple_untagged_rows_refuse :
    query { enums := [definition { encoding := .untagged, size := 8, align := 4, variantFieldOffsets := [[4], []] }] } .shape (.Enum ⟨0⟩) =
      .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def wide : Summary :=
  { size := 8, align := some 8, fields := [{ ty := .I64, offset := 0, size := 8, align := 8 }] }
private def tooSmall : EnumDef :=
  { id := ⟨0⟩, name := "small", variants := [{ name := "wide", fields := [.I64] }]
    layout := some { encoding := .untagged, size := 1, align := 1, variantFieldOffsets := [[0]] } }
private def tooSmallValue : Summary :=
  { size := 1, align := some 1
    enumeration := some { tag := .u8, discriminants := [0], encoding := .untagged, variants := [wide.fields], uninhabited := [false] } }

theorem own_child_geometry : FieldGeometry wide := one_field _ _ _ _ _ (by decide)

theorem raw_accepts_parent_mismatch : EnumConstruction .shape tooSmall .u8 [0] [false] [wide] tooSmallValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem parent_geometry_false : ¬ EnumerationGeometry tooSmallValue := by
  intro geometry
  have row := geometry _ rfl _ ((trustIrListMemConsSelf _ _))
  have impossible : 8 ≤ 1 := row.2 _ ((trustIrListMemConsSelf _ _))
  omega

theorem public_parent_mismatch_refuses :
    query { enums := [tooSmall] } .shape (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def nicheGraph : Graph :=
  { count := 3, nodes := ((NatIndexTree.empty.insert 0 (Equation.done (.ok carrier))).insert 1
      (Equation.done (.ok { size := 1, align := some 1 }))).insert 2
      (enumEquation .shape (nicheDefinition niche) [false, false] [0, 1]) }

theorem niche_graph_query : nicheGraph.query 2 = .ok nicheValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem niche_node_carrier : ∃ field, field ∈ carrier.fields ∧ field.size ≠ 0 ∧ field.offset ≤ 0 ∧ 1 ≤ field.offset + field.size := by
  trustIrCompilerProof {
    exact NodeDerivation.descriptorEnum_niche_carrier .shape (nicheDefinition niche) [false, false] [0, 1]
      niche rfl 0 1 1 0 0 .u8 rfl (by rfl) (nicheGraph.query_derivation 2 nicheValue niche_graph_query) _ rfl
  } {
    exact NodeDerivation.descriptorEnum_niche_carrier .shape (nicheDefinition niche) [false, false] [0, 1]
      niche rfl 0 1 1 0 0 .u8 rfl (by trustIrReduce) (nicheGraph.query_derivation 2 nicheValue niche_graph_query) _ rfl
  }

private def nonemptyEncoded : EnumDef :=
  { id := ⟨0⟩, name := "payload", variants := [{ name := "a", fields := [.I8] }, { name := "b", fields := [.I8] }]
    layout := some { niche with size := 2, variantFieldOffsets := [[0], [1]] } }

theorem nonempty_encoded_payload_accepts : query { enums := [nonemptyEncoded] } .shape (.Enum ⟨0⟩) = .ok
    { size := 2, align := some 1
      enumeration := some { tag := .u8, discriminants := [0, 1], encoding := .niche 0 1 1 0 0 .u8, variants := [carrier.fields, [{ ty := .I8, offset := 1, size := 1, align := 1 }]], uninhabited := [false, false] } } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem direct_certificates : directGraph.ParentFieldCertificates direct.size [0, 1] := by
  intro node member
  cases member with
  | head =>
    refine ⟨Equation.done (.ok small), rfl, Equation.ParentFieldGuarded.done _ _ ?_⟩
    intro value same
    cases same
    exact one_field _ _ _ _ _ (by decide)
  | tail _ member =>
    cases member with
    | head =>
      refine ⟨Equation.done (.ok empty), rfl, Equation.ParentFieldGuarded.done _ _ ?_⟩
      intro value same
      cases same
      exact ⟨trivial, by intro field impossible; cases impossible⟩
    | tail _ impossible => cases impossible

theorem direct_contextual_rule :
    (enumEquation .shape (definition direct) [false, false] [0, 1]).ContextualRule directGraph
      (fun _ value => FieldGeometry value ∧ EnumerationGeometry value) 2 :=
  Equation.ContextualRule.descriptorEnum_geometry directGraph 2 .shape (definition direct)
    [false, false] [0, 1] direct rfl direct_certificates

theorem parent_mismatch_certificate_refuses :
    ¬ (Equation.done (.ok wide)).ParentFieldGuarded 1 := by
  intro safe
  have child := safe ({} : Graph) wide ⟨wide, wide, rfl, .nil wide, rfl⟩
  have impossible : 8 ≤ 1 := child.2 _ ((trustIrListMemConsSelf _ _))
  omega

theorem declared_variant_parent_contract :
    (declaredFields .shape "enum" 0 direct.size direct.align word64Max false
      [(.I32, some 4, 0)]).ParentFieldGuarded direct.size :=
  Equation.ParentFieldGuarded.declaredFields _ _ _ _ _ _ _ _

theorem direct_public_storage : StorageGeometry directValue :=
  query_storage_geometry { enums := [definition direct] } .shape (.Enum ⟨0⟩) directValue direct_source_shape

theorem niche_public_storage : StorageGeometry nicheValue :=
  query_storage_geometry { enums := [nicheDefinition niche] } .shape (.Enum ⟨0⟩) nicheValue niche_source_shape

theorem single_public_storage : StorageGeometry singleValue :=
  query_storage_geometry { enums := [single] } .shape (.Enum ⟨0⟩) singleValue single_inhabited_preserves_rows

theorem untagged_public_storage : StorageGeometry untaggedValue :=
  query_storage_geometry { enums := [untagged] } .shape (.Enum ⟨0⟩) untaggedValue one_untagged_row_accepts

theorem direct_public_power_alignment : PowerAlignment directValue :=
  query_power_alignment { enums := [definition direct] } .shape (.Enum ⟨0⟩) directValue direct_source_shape

theorem niche_public_power_alignment : PowerAlignment nicheValue :=
  query_power_alignment { enums := [nicheDefinition niche] } .shape (.Enum ⟨0⟩) nicheValue niche_source_shape

theorem direct_public_field_alignment : FieldAlignmentSummary directValue :=
  query_field_alignment { enums := [definition direct] } .shape (.Enum ⟨0⟩) directValue direct_source_shape

theorem niche_public_field_alignment : FieldAlignmentSummary nicheValue :=
  query_field_alignment { enums := [nicheDefinition niche] } .shape (.Enum ⟨0⟩) nicheValue niche_source_shape

theorem direct_public_encoding : EnumEncodingGeometry directValue :=
  query_encoding_geometry { enums := [definition direct] } .shape (.Enum ⟨0⟩) directValue direct_source_shape

theorem niche_public_encoding : EnumEncodingGeometry nicheValue :=
  query_encoding_geometry { enums := [nicheDefinition niche] } .shape (.Enum ⟨0⟩) nicheValue niche_source_shape

theorem single_public_encoding : EnumEncodingGeometry singleValue :=
  query_encoding_geometry { enums := [single] } .shape (.Enum ⟨0⟩) singleValue single_inhabited_preserves_rows

theorem untagged_public_encoding : EnumEncodingGeometry untaggedValue :=
  query_encoding_geometry { enums := [untagged] } .shape (.Enum ⟨0⟩) untaggedValue one_untagged_row_accepts

private def wrapping : EnumDef :=
  { id := ⟨0⟩, name := "wrap", variants := [{ name := "carrier", fields := [.I8] }, { name := "a", fields := [] }, { name := "b", fields := [] }]
    layout := some { encoding := .niche 0 1 2 255 0 .u8, size := 1, align := 1, variantFieldOffsets := [[0], [], []] } }
private def wrappingValue : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .u8, discriminants := [0, 1, 2], encoding := .niche 0 1 2 255 0 .u8, variants := [[{ ty := .I8, offset := 0, size := 1, align := 1 }], [], []], uninhabited := [false, false, false] } }

theorem wrapping_start_accepts : query { enums := [wrapping] } .shape (.Enum ⟨0⟩) = .ok wrappingValue := by
  trustIrCompilerProof {
    simp only [query, prepare, Session.query]
    rfl
  } {
    trustIrReduce
  }

theorem wrapping_geometry : EnumEncodingGeometry wrappingValue :=
  query_encoding_geometry { enums := [wrapping] } .shape (.Enum ⟨0⟩) wrappingValue wrapping_start_accepts

theorem wrapping_sum_exceeds_mask : 255 + (2 - 1) > 2 ^ tagBits .u8 - 1 := by decide

private def forgedTag : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .u8, discriminants := [0], encoding := .direct 0, variants := [[{ ty := .I8, offset := 0, size := 1, align := 1 }]], uninhabited := [false] } }

theorem forged_tag_storage_valid : StorageGeometry forgedTag := by
  constructor
  · exact ⟨trivial, by intro field impossible; cases impossible⟩
  · intro enumeration actual fields member
    cases actual
    cases member with
    | head => exact one_field _ _ _ _ _ (by decide)
    | tail _ impossible => cases impossible

theorem forged_tag_geometry_false : ¬ EnumEncodingGeometry forgedTag := by
  intro safe
  rcases safe _ rfl with ⟨align, present, lane, separated⟩
  have impossible : overlap 0 1 0 1 = false := separated _ ((trustIrListMemConsSelf _ _)) _ ((trustIrListMemConsSelf _ _))
  cases impossible

theorem direct_public_metadata : EnumMetadata directValue :=
  query_metadata { enums := [definition direct] } .shape (.Enum ⟨0⟩) directValue direct_source_shape

theorem niche_public_metadata : EnumMetadata nicheValue :=
  query_metadata { enums := [nicheDefinition niche] } .shape (.Enum ⟨0⟩) nicheValue niche_source_shape

theorem single_public_metadata : EnumMetadata singleValue :=
  query_metadata { enums := [single] } .shape (.Enum ⟨0⟩) singleValue single_inhabited_preserves_rows

end DescriptorEnumControls
namespace PowerAlignmentControls

private def forged : Summary := { size := 3, align := some 3 }
private def forgedResult : Summary :=
  { size := 3, align := some 3, fields := [{ ty := .I8, offset := 0, size := 3, align := 3 }] }
private def forgedGraph : Graph :=
  { count := 2, nodes := (NatIndexTree.empty.insert 0 (Equation.done (.ok forged))).insert 1
      (canonicalFields .execution "tuple" 0 [(.I8, 0)]) }

theorem forged_child_accepts : forgedGraph.query 1 = .ok forgedResult := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forged_child_power_false : ¬ PowerAlignment forgedResult := by
  intro safe
  have impossible : powerOfTwo 3 = true := (safe 3 rfl).1
  cases impossible

private def indivisible : Summary := { size := 3, align := some 2 }
private def scaledGraph : Graph :=
  { count := 2, nodes := (NatIndexTree.empty.insert 0 (Equation.done (.ok indivisible))).insert 1
      (scaled .execution 1 0) }

theorem forged_scaled_accepts : scaledGraph.query 1 = .ok indivisible := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forged_scaled_multiple_false : ¬ PowerAlignment indivisible := by
  intro safe
  have impossible : 3 % 2 = 0 := (safe 2 rfl).2
  cases impossible

theorem never_alignment_absent : query {} .shape .Never = .ok { size := 0, align := none } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem never_power_alignment : PowerAlignment { size := 0, align := none } :=
  query_power_alignment {} .shape .Never _ never_alignment_absent

theorem power_six_refuses : powerOfTwo 6 = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem power_eight_divides_sixty_four : 8 ∣ 64 :=
  powerOfTwo_dvd_of_le (by decide) (by decide) (by decide)

end PowerAlignmentControls

namespace FieldAlignmentControls

private def child : Summary :=
  { size := 0, align := some 1, fields := [{ ty := .Struct ⟨1⟩, offset := 0, size := 0, align := 8 }] }
private def outer : StructDef :=
  { id := ⟨0⟩, name := "outer", fields := [{ name := "empty", ty := .Struct ⟨1⟩, offset := none }], size := some 0, align := some 1 }
private def inner : StructDef := { id := ⟨1⟩, name := "inner", fields := [], size := some 0, align := some 8 }
private def definition : EnumDef := { id := ⟨0⟩, name := "enum", variants := [{ name := "only", fields := [.Struct ⟨0⟩] }] }
private def source : Environment := { structs := [outer, inner], enums := [definition] }
private def rawValue : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .u8, discriminants := [0], encoding := .direct 0, variants := [[{ ty := .Struct ⟨1⟩, offset := 1, size := 0, align := 8 }]], uninhabited := [false] } }
private def actualValue : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .u8, discriminants := [0], encoding := .direct 0, variants := [[{ ty := .Struct ⟨0⟩, offset := 1, size := 0, align := 1 }]], uninhabited := [false] } }

theorem actual_empty_child_query : query source .execution (.Struct ⟨0⟩) = .ok child := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_empty_child_alignment : FieldAlignmentSummary child :=
  query_field_alignment source .execution (.Struct ⟨0⟩) child actual_empty_child_query

theorem actual_empty_child_power : PowerAlignment child :=
  query_power_alignment source .execution (.Struct ⟨0⟩) child actual_empty_child_query

theorem raw_enum_empty_shift_accepts : EnumConstruction .execution definition .u8 [0] [false] [child] rawValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem raw_enum_empty_shift_false : ¬ FieldAlignmentSummary rawValue := by
  intro safe
  rcases safe.2 _ rfl with ⟨align, actual, rows⟩
  cases actual
  have row := rows _ ((trustIrListMemConsSelf _ _))
  have impossible : 1 % 8 = 0 := (row.2 _ ((trustIrListMemConsSelf _ _))).2.1
  cases impossible

theorem actual_enum_empty_shift_query : query source .execution (.Enum ⟨0⟩) = .ok actualValue := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_enum_empty_shift_alignment : FieldAlignmentSummary actualValue :=
  query_field_alignment source .execution (.Enum ⟨0⟩) actualValue actual_enum_empty_shift_query

theorem empty_child_cap_exception : ¬ (∀ field, field ∈ child.fields → field.align ≤ 1) := by
  intro cap
  have impossible : 8 ≤ 1 := cap _ ((trustIrListMemConsSelf _ _))
  omega

private def badClamp : Environment := { structs := [{ outer with repr := .packed 3 }, inner] }

theorem invalid_packed_clamp_refuses :
    query badClamp .execution (.Struct ⟨0⟩) = .error (.incoherent "struct" 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end FieldAlignmentControls

namespace EnumMetadataControls

private def definition : EnumDef :=
  { id := ⟨0⟩, name := "labels", variants := [{ name := "a", fields := [] }, { name := "b", fields := [] }, { name := "c", fields := [] }], discriminants := [some (-2), none, some 7] }

theorem mixed_effective_labels : discriminants definition = some [-2, -1, 7] := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem mixed_value_agreement : TrustIr.enumEffectiveDiscriminants definition = some [-2, -1, 7] := by
  rw [← discriminants_eval definition]
  exact mixed_effective_labels

theorem signed_tag_selected : canonicalTag definition = some .i8 := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem mixed_labels_unique : UniqueDiscriminants [-2, -1, 7] :=
  (discriminants_facts definition _ mixed_effective_labels).2

private def collision : EnumDef := { definition with discriminants := [some 7, none, some 8] }

theorem implicit_explicit_collision_refuses : discriminants collision = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem collision_value_refuses : TrustIr.enumEffectiveDiscriminants collision = none := by
  rw [← discriminants_eval collision]
  exact implicit_explicit_collision_refuses

theorem exhausted_implicit_refuses : discriminants.go [none] none [] = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem explicit_reset_after_exhaustion : discriminants.go [some (-1)] none [] = some [-1] := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def badTag : EnumDef := { definition with tagRepr := some .u8 }

theorem unsigned_tag_negative_refuses : canonicalTag badTag = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def value : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .i8, discriminants := [-2, -1, 7], encoding := .direct 0, variants := [[], [], []], uninhabited := [false, false, false] } }

set_option maxRecDepth 8192 in
theorem actual_query : query { enums := [definition] } .execution (.Enum ⟨0⟩) = .ok value := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_metadata : EnumMetadata value :=
  query_metadata { enums := [definition] } .execution (.Enum ⟨0⟩) value actual_query

private def unit : Summary := { size := 0, align := some 1 }
private def wrongRows : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .i8, discriminants := [-2, -1, 7], encoding := .direct 0, variants := [[]], uninhabited := [false, false, false] } }
private def wrongRowGraph : Graph :=
  { count := 2, nodes := (NatIndexTree.empty.insert 0 (Equation.done (.ok unit))).insert 1
      (enumEquation .execution definition [false, false, false] [0]) }

theorem raw_wrong_row_count_accepts : wrongRowGraph.query 1 = .ok wrongRows := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem raw_wrong_row_metadata_false : ¬ EnumMetadata wrongRows := by
  intro safe
  have impossible : 3 = 1 := (safe _ rfl).1
  cases impossible

private def wrongFlags : Summary :=
  { size := 1, align := some 1, enumeration := some { tag := .i8, discriminants := [-2, -1, 7], encoding := .direct 0, variants := [[], [], []], uninhabited := [] } }

theorem raw_wrong_flag_count_accepts :
    EnumConstruction .execution definition .i8 [-2, -1, 7] [] [unit, unit, unit] wrongFlags := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem raw_wrong_flag_metadata_false : ¬ EnumMetadata wrongFlags := by
  intro safe
  have impossible : 0 = 3 := (safe _ rfl).2.1
  cases impossible

end EnumMetadataControls

end TrustIr.SourceLayout
