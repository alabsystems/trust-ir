-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.LocalTypes

namespace TrustIr.LocalTypeInference

/-- Agreement at every original identifier, allowing one genuinely fresh
    declaration to be introduced by a source transformation. -/
def AgreesExcept {α : Type} (fresh : Nat) (source target : NatIndex α) : Prop :=
  ∀ query, query ≠ fresh → source.find? query = target.find? query

theorem AgreesExcept.insert_same {α : Type} {fresh : Nat}
    {source target : NatIndex α} (agree : AgreesExcept fresh source target)
    (id : Nat) (entry : α) :
    AgreesExcept fresh (source.insert id entry) (target.insert id entry) := by
  intro query original
  simp only [NatIndex.find?_insert]
  split
  · rfl
  · exact agree query original

theorem AgreesExcept.insert_fresh {α : Type} {fresh : Nat}
    {source target : NatIndex α} (agree : AgreesExcept fresh source target) (entry : α) :
    AgreesExcept fresh source (target.insert fresh entry) := by
  intro query original
  rw [NatIndex.find?_insert_ne _ _ _ _ original]
  exact agree query original

theorem AgreesExcept.trans {α : Type} {fresh : Nat} {first second third : NatIndex α}
    (left : AgreesExcept fresh first second) (right : AgreesExcept fresh second third) :
    AgreesExcept fresh first third := fun query original =>
  (left query original).trans (right query original)

theorem fillPath_agreesExcept (root : Ty) (path : List ValueId) (fresh : Nat)
    (source target : ResolutionIndex) (agree : AgreesExcept fresh source target) :
    AgreesExcept fresh
      (path.foldl (fun table id => table.insert id.index (.resolved (borrowedLocalType root))) source)
      (path.foldl (fun table id => table.insert id.index (.resolved (borrowedLocalType root))) target) := by
  induction path generalizing source target with
  | nil => exact agree
  | cons id _rest ih =>
    exact ih _ _ (agree.insert_same id.index _)

theorem fillPath_preserves_fresh (root : Ty) (path : List ValueId) (fresh : Nat)
    (memo : ResolutionIndex) (original : ∀ id ∈ path, id.index ≠ fresh) :
    (path.foldl (fun table id => table.insert id.index (.resolved (borrowedLocalType root))) memo).find?
      fresh = memo.find? fresh := by
  induction path generalizing memo with
  | nil => rfl
  | cons id rest ih =>
    have head : id.index ≠ fresh := original id ((trustIrListMemConsSelf _ _))
    have tail : ∀ item ∈ rest, item.index ≠ fresh :=
      fun item member => original item (List.mem_cons_of_mem id member)
    rw [List.foldl_cons, ih _ tail, NatIndex.find?_insert_ne _ _ _ _ (Ne.symm head)]

theorem finishPath_agreesExcept (root : Ty) (path : List ValueId) (fresh : Nat)
    (source target : ResolutionIndex) (sourceWork targetWork : LocalTypeWork)
    (agree : AgreesExcept fresh source target) :
    AgreesExcept fresh (finishLocalTypePath root path source sourceWork).fst
      (finishLocalTypePath root path target targetWork).fst :=
  fillPath_agreesExcept root path fresh source target agree

theorem finishPath_preserves_fresh (root : Ty) (path : List ValueId) (fresh : Nat)
    (memo : ResolutionIndex) (work : LocalTypeWork)
    (original : ∀ id ∈ path, id.index ≠ fresh) :
    (finishLocalTypePath root path memo work).fst.find? fresh = memo.find? fresh :=
  fillPath_preserves_fresh root path fresh memo original

/-- If a source resolution actually succeeds, adding a disjoint declaration
    cannot change it or make it fail. The target may have a larger source-size
    recursion bound. Both memo agreement and the new cell's exact preservation
    are proved; no successful target run or inferred-table law is assumed. -/
theorem resolve_fresh_extension
    (sourceDecls targetDecls : DeclarationIndex) (fresh : Nat)
    (declsAgree : AgreesExcept fresh sourceDecls targetDecls)
    (borrowOriginal : ∀ id operand,
      sourceDecls.find? id = some (.borrow operand) → operand.index ≠ fresh)
    (fuel extra : Nat) (id : ValueId) (path : List ValueId)
    (sourceMemo targetMemo : ResolutionIndex) (sourceWork targetWork : LocalTypeWork)
    (result : ResolutionIndex) (resultWork : LocalTypeWork)
    (idOriginal : id.index ≠ fresh)
    (pathOriginal : ∀ item ∈ path, item.index ≠ fresh)
    (memoAgree : AgreesExcept fresh sourceMemo targetMemo)
    (sourceRun : resolveLocalType sourceDecls fuel id path sourceMemo sourceWork =
      .ok (result, resultWork)) :
    ∃ targetResult targetResultWork,
      resolveLocalType targetDecls (fuel + extra) id path targetMemo targetWork =
        .ok (targetResult, targetResultWork) ∧
      AgreesExcept fresh result targetResult ∧
      targetResult.find? fresh = targetMemo.find? fresh := by
  induction fuel generalizing id path sourceMemo targetMemo sourceWork targetWork result resultWork with
  | zero => cases sourceRun
  | succ fuel ih =>
    have memoLookup := memoAgree id.index idOriginal
    cases found : sourceMemo.find? id.index with
    | some resolution =>
      cases resolution with
      | visiting => simp only [resolveLocalType, found] at sourceRun <;> try contradiction
      | resolved ty =>
        simp only [resolveLocalType, found] at sourceRun <;> try contradiction
        have output := Except.ok.inj sourceRun
        refine ⟨(finishLocalTypePath ty path targetMemo
          {targetWork with memoLookups := targetWork.memoLookups + 1}).fst,
          (finishLocalTypePath ty path targetMemo
          {targetWork with memoLookups := targetWork.memoLookups + 1}).snd, ?_, ?_, ?_⟩
        · rw [Nat.succ_add, resolveLocalType, ← memoLookup, found]
        · have resultEq := congrArg Prod.fst output
          dsimp only at resultEq
          rw [← resultEq]
          exact finishPath_agreesExcept ty path fresh sourceMemo targetMemo _ _ memoAgree
        · exact finishPath_preserves_fresh ty path fresh targetMemo _ pathOriginal
    | none =>
      have declLookup := declsAgree id.index idOriginal
      cases declared : sourceDecls.find? id.index with
      | none => simp only [resolveLocalType, found, declared] at sourceRun <;> try contradiction
      | some source =>
        cases source with
        | declared ty =>
          simp only [resolveLocalType, found, declared] at sourceRun <;> try contradiction
          have output := Except.ok.inj sourceRun
          refine ⟨(finishLocalTypePath ty path (targetMemo.insert id.index (.resolved ty))
            {targetWork with
              memoLookups := targetWork.memoLookups + 1
              declarationLookups := targetWork.declarationLookups + 1
              resolvedDeclarations := targetWork.resolvedDeclarations + 1}).fst,
            (finishLocalTypePath ty path (targetMemo.insert id.index (.resolved ty))
            {targetWork with
              memoLookups := targetWork.memoLookups + 1
              declarationLookups := targetWork.declarationLookups + 1
              resolvedDeclarations := targetWork.resolvedDeclarations + 1}).snd, ?_, ?_, ?_⟩
          · rw [Nat.succ_add, resolveLocalType, ← memoLookup, found, ← declLookup, declared]
          · have resultEq := congrArg Prod.fst output
            dsimp only at resultEq
            rw [← resultEq]
            exact finishPath_agreesExcept ty path fresh _ _ _ _ (memoAgree.insert_same id.index _)
          · rw [finishPath_preserves_fresh ty path fresh _ _ pathOriginal,
              NatIndex.find?_insert_ne _ _ _ _ (Ne.symm idOriginal)]
        | borrow operand =>
          simp only [resolveLocalType, found, declared] at sourceRun <;> try contradiction
          have operandOriginal := borrowOriginal id.index operand declared
          have extendedPath : ∀ item ∈ id :: path, item.index ≠ fresh := by
            intro item member
            rcases List.mem_cons.mp member with same | old
            · subst item; exact idOriginal
            · exact pathOriginal item old
          obtain ⟨targetResult, targetResultWork, targetRun, outputAgree, outputFresh⟩ :=
            ih operand (id :: path) (sourceMemo.insert id.index .visiting)
              (targetMemo.insert id.index .visiting) _ _ result resultWork
              operandOriginal extendedPath (memoAgree.insert_same id.index _) sourceRun
          refine ⟨targetResult, targetResultWork, ?_, outputAgree, ?_⟩
          · rw [Nat.succ_add, resolveLocalType, ← memoLookup, found, ← declLookup, declared]
            exact targetRun
          · rw [outputFresh, NatIndex.find?_insert_ne _ _ _ _ (Ne.symm idOriginal)]

def FreshMemo (fresh : Nat) (ty : Ty) (memo : ResolutionIndex) : Prop :=
  memo.find? fresh = none ∨ memo.find? fresh = some (.resolved ty)

/-- Resolve a newly introduced directly declared result. The result table is
    derived by the ordinary resolver and preserves every original lookup. -/
theorem resolve_direct_fresh (decls : DeclarationIndex) (fresh : Nat) (ty : Ty)
    (fuel : Nat) (memo : ResolutionIndex) (work : LocalTypeWork)
    (declared : decls.find? fresh = some (.declared ty))
    (freshMemo : FreshMemo fresh ty memo) :
    ∃ result resultWork,
      resolveLocalType decls (fuel + 1) ⟨fresh⟩ [] memo work = .ok (result, resultWork) ∧
      AgreesExcept fresh memo result ∧ result.find? fresh = some (.resolved ty) := by
  rcases freshMemo with missing | cached
  · refine ⟨memo.insert fresh (.resolved ty),
      { work with
        memoLookups := work.memoLookups + 1
        declarationLookups := work.declarationLookups + 1
        resolvedDeclarations := work.resolvedDeclarations + 1 }, ?_, ?_, ?_⟩
    · simp only [resolveLocalType, missing, declared, finishLocalTypePath, List.foldl_nil,
        List.length_nil, Nat.add_zero]
    · intro query original
      exact (NatIndex.find?_insert_ne _ _ _ _ original).symm
    · exact NatIndex.find?_insert_same _ _ _
  · refine ⟨memo, {work with memoLookups := work.memoLookups + 1}, ?_, ?_, cached⟩
    · simp only [resolveLocalType, cached, finishLocalTypePath, List.foldl_nil,
        List.length_nil, Nat.add_zero]
    · intro query _; rfl

def withoutFresh (fresh : Nat) : List ValueId → List ValueId
  | [] => []
  | id :: rest => if id.index = fresh then withoutFresh fresh rest
      else id :: withoutFresh fresh rest

def seenFresh (fresh : Nat) : List ValueId → Bool
  | [] => false
  | id :: rest => if id.index = fresh then true else seenFresh fresh rest

/-- A named view of the exact fold used by inference, not a second resolver. -/
def resolveAll (decls : DeclarationIndex) (fuel : Nat) (ids : List ValueId)
    (state : ResolutionIndex × LocalTypeWork) : Except SemError (ResolutionIndex × LocalTypeWork) :=
  ids.foldlM (fun (memo, work) id => resolveLocalType decls fuel id [] memo work) state

theorem resolveAll_cons (decls : DeclarationIndex) (fuel : Nat) (id : ValueId)
    (ids : List ValueId) (memo : ResolutionIndex) (work : LocalTypeWork) :
    resolveAll decls fuel (id :: ids) (memo, work) =
      (resolveLocalType decls fuel id [] memo work).bind
        (fun state => resolveAll decls fuel ids state) := rfl

/-- Fresh declarations may occur at any position in the serialized traversal.
    Erasing them yields exactly the original resolver sequence. All original
    memo bindings are preserved, and an encountered fresh result is actually
    resolved to its declared type. The target success is a conclusion. -/
theorem resolveAll_fresh_extension
    (sourceDecls targetDecls : DeclarationIndex) (fresh : Nat) (ty : Ty)
    (declsAgree : AgreesExcept fresh sourceDecls targetDecls)
    (borrowOriginal : ∀ id operand,
      sourceDecls.find? id = some (.borrow operand) → operand.index ≠ fresh)
    (declared : targetDecls.find? fresh = some (.declared ty))
    (fuel extra : Nat) (ids : List ValueId)
    (sourceMemo targetMemo : ResolutionIndex) (sourceWork targetWork : LocalTypeWork)
    (result : ResolutionIndex) (resultWork : LocalTypeWork)
    (memoAgree : AgreesExcept fresh sourceMemo targetMemo)
    (freshMemo : FreshMemo fresh ty targetMemo)
    (sourceRun : resolveAll sourceDecls (fuel + 1) (withoutFresh fresh ids)
      (sourceMemo, sourceWork) = .ok (result, resultWork)) :
    ∃ targetResult targetResultWork,
      resolveAll targetDecls (fuel + 1 + extra) ids (targetMemo, targetWork) =
        .ok (targetResult, targetResultWork) ∧
      AgreesExcept fresh result targetResult ∧
      targetResult.find? fresh =
        if seenFresh fresh ids then some (.resolved ty) else targetMemo.find? fresh := by
  induction ids generalizing sourceMemo targetMemo sourceWork targetWork result resultWork with
  | nil =>
    have output : (sourceMemo, sourceWork) = (result, resultWork) := Except.ok.inj sourceRun
    have memoEq := congrArg Prod.fst output
    dsimp only at memoEq
    refine ⟨targetMemo, targetWork, rfl, ?_, rfl⟩
    rw [← memoEq]
    exact memoAgree
  | cons id rest ih =>
    by_cases atFresh : id.index = fresh
    · have idEq : id = ⟨fresh⟩ := by cases id; cases atFresh; rfl
      subst id
      simp only [withoutFresh, if_pos rfl] at sourceRun <;> try contradiction
      obtain ⟨midTarget, midTargetWork, step, midAgree, midFresh⟩ :=
        resolve_direct_fresh targetDecls fresh ty (fuel + extra) targetMemo targetWork declared freshMemo
      have total : fuel + 1 + extra = fuel + extra + 1 := by omega
      rw [← total] at step
      obtain ⟨targetResult, targetResultWork, targetRun, outputAgree, outputFresh⟩ :=
        ih sourceMemo midTarget sourceWork midTargetWork result resultWork
          (memoAgree.trans midAgree) (Or.inr midFresh) sourceRun
      refine ⟨targetResult, targetResultWork, ?_, outputAgree, ?_⟩
      · rw [resolveAll_cons, step]
        exact targetRun
      · simp only [seenFresh, if_pos rfl]
        simpa only [midFresh, ite_self] using outputFresh
    · simp only [withoutFresh, if_neg atFresh, resolveAll_cons] at sourceRun <;> try contradiction
      cases sourceStep : resolveLocalType sourceDecls (fuel + 1) id [] sourceMemo sourceWork with
      | error error => simp only [sourceStep, Except.bind] at sourceRun <;> try contradiction
      | ok midSource =>
        rcases midSource with ⟨midSource, midSourceWork⟩
        simp only [sourceStep, Except.bind] at sourceRun <;> try contradiction
        obtain ⟨midTarget, midTargetWork, targetStep, midAgree, midFresh⟩ :=
          resolve_fresh_extension sourceDecls targetDecls fresh declsAgree borrowOriginal
            (fuel + 1) extra id [] sourceMemo targetMemo sourceWork targetWork midSource midSourceWork
            atFresh (by intro item member; cases member) memoAgree sourceStep
        have nextFresh : FreshMemo fresh ty midTarget := by
          rcases freshMemo with missing | cached
          · exact Or.inl (midFresh.trans missing)
          · exact Or.inr (midFresh.trans cached)
        obtain ⟨targetResult, targetResultWork, targetRun, outputAgree, outputFresh⟩ :=
          ih midSource midTarget midSourceWork midTargetWork result resultWork midAgree nextFresh sourceRun
        refine ⟨targetResult, targetResultWork, ?_, outputAgree, ?_⟩
        · rw [resolveAll_cons, targetStep]
          exact targetRun
        · simpa only [seenFresh, if_neg atFresh, midFresh] using outputFresh

abbrev DeclarationState := DeclarationIndex × List ValueId

/-- The collection result of inserting one new, typed source declaration. -/
structure DeclarationExtension (fresh : Nat) (ty : Ty)
    (source target : DeclarationState) : Prop where
  agree : AgreesExcept fresh source.fst target.fst
  freshBinding : target.fst.find? fresh = some (.declared ty)
  ids : withoutFresh fresh target.snd = source.snd
  seen : seenFresh fresh target.snd = true

theorem addSource_fresh_extension (fresh : Nat) (ty : Ty)
    (source target : DeclarationState) (extension : DeclarationExtension fresh ty source target)
    (id : ValueId) (entry : LocalTypeSource) (result : DeclarationState)
    (original : id.index ≠ fresh)
    (sourceRun : addLocalTypeSource source id entry = .ok result) :
    ∃ targetResult, addLocalTypeSource target id entry = .ok targetResult ∧
      DeclarationExtension fresh ty result targetResult := by
  have lookup := congrArg Option.isSome (extension.agree id.index original)
  change source.fst.contains id.index = target.fst.contains id.index at lookup
  cases present : source.fst.contains id.index with
  | true => simp only [addLocalTypeSource, present, if_true] at sourceRun <;> try contradiction
  | false =>
    have targetAbsent : target.fst.contains id.index = false := lookup.symm.trans present
    simp only [addLocalTypeSource, present, Bool.false_eq_true, if_false] at sourceRun <;> try contradiction
    have output := Except.ok.inj sourceRun
    refine ⟨(target.fst.insert id.index entry, id :: target.snd), ?_, ?_⟩
    · simp only [addLocalTypeSource, targetAbsent, Bool.false_eq_true, if_false]
    · rw [← output]
      refine ⟨extension.agree.insert_same id.index entry, ?_, ?_, ?_⟩
      · rw [NatIndex.find?_insert_ne _ _ _ _ (Ne.symm original)]
        exact extension.freshBinding
      · simp only [withoutFresh, if_neg original, extension.ids]
      · simp only [seenFresh, if_neg original]
        exact extension.seen

theorem addSources_fresh_extension (fresh : Nat) (ty : Ty)
    (entries : List (ValueId × LocalTypeSource))
    (source target : DeclarationState) (extension : DeclarationExtension fresh ty source target)
    (result : DeclarationState) (original : ∀ row ∈ entries, row.fst.index ≠ fresh)
    (sourceRun : entries.foldlM (fun state row => addLocalTypeSource state row.fst row.snd)
      source = .ok result) :
    ∃ targetResult,
      entries.foldlM (fun state row => addLocalTypeSource state row.fst row.snd) target =
        .ok targetResult ∧ DeclarationExtension fresh ty result targetResult := by
  induction entries generalizing source target result with
  | nil =>
    have output : source = result := Except.ok.inj sourceRun
    subst result
    exact ⟨target, rfl, extension⟩
  | cons row rest ih =>
    have head : row.fst.index ≠ fresh := original row ((trustIrListMemConsSelf _ _))
    have tail : ∀ entry ∈ rest, entry.fst.index ≠ fresh :=
      fun entry member => original entry (List.mem_cons_of_mem row member)
    simp only [List.foldlM_cons] at sourceRun <;> try contradiction
    cases step : addLocalTypeSource source row.fst row.snd with
    | error error => simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    | ok midSource =>
      simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      obtain ⟨midTarget, targetStep, midExtension⟩ :=
        addSource_fresh_extension fresh ty source target extension row.fst row.snd midSource head step
      obtain ⟨targetResult, targetRun, outputExtension⟩ :=
        ih midSource midTarget midExtension result tail sourceRun
      refine ⟨targetResult, ?_, outputExtension⟩
      rw [List.foldlM_cons, targetStep]
      exact targetRun

theorem zip_fst_mem {α β : Type} (left : List α) (right : List β)
    (row : α × β) (member : row ∈ left.zip right) : row.fst ∈ left := by
  induction left generalizing right with
  | nil => cases member
  | cons item rest ih =>
    cases right with
    | nil => cases member
    | cons entry entries =>
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with same | old
      · subst row; exact (trustIrListMemConsSelf _ _)
      · exact List.mem_cons_of_mem item (ih entries old)

theorem addNode_fresh_extension (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (ty : Ty) (source target : DeclarationState)
    (extension : DeclarationExtension fresh ty source target)
    (node : Inst × List ValueId) (result : DeclarationState)
    (original : ∀ id ∈ node.snd, id.index ≠ fresh)
    (sourceRun : addLocalTypeNode direct indirect source node = .ok result) :
    ∃ targetResult, addLocalTypeNode direct indirect target node = .ok targetResult ∧
      DeclarationExtension fresh ty result targetResult := by
  unfold addLocalTypeNode at sourceRun ⊢
  cases classified : localResultTypes direct indirect node.fst with
  | error error => simp only [classified, Bind.bind, Except.bind] at sourceRun <;> try contradiction
  | ok types =>
    simp only [classified, Bind.bind, Except.bind] at sourceRun ⊢
    by_cases census : types.length != node.snd.length
    · simp only [census, if_true, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    · simp only [census, Bool.false_eq_true, if_false, Bind.bind, Pure.pure, Except.bind, Except.pure] at sourceRun ⊢
      exact addSources_fresh_extension fresh ty (node.snd.zip types) source target extension result
        (fun row member => original row.fst (zip_fst_mem node.snd types row member)) sourceRun

theorem collectNodes_fresh_extension (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (ty : Ty) (nodes : List (Inst × List ValueId))
    (source target : DeclarationState) (extension : DeclarationExtension fresh ty source target)
    (result : DeclarationState) (original : ∀ node ∈ nodes, ∀ id ∈ node.snd, id.index ≠ fresh)
    (sourceRun : nodes.foldlM (addLocalTypeNode direct indirect) source = .ok result) :
    ∃ targetResult, nodes.foldlM (addLocalTypeNode direct indirect) target = .ok targetResult ∧
      DeclarationExtension fresh ty result targetResult := by
  induction nodes generalizing source target result with
  | nil =>
    have output : source = result := Except.ok.inj sourceRun
    subst result
    exact ⟨target, rfl, extension⟩
  | cons node rest ih =>
    have head : ∀ id ∈ node.snd, id.index ≠ fresh := original node ((trustIrListMemConsSelf _ _))
    have tail : ∀ row ∈ rest, ∀ id ∈ row.snd, id.index ≠ fresh :=
      fun row member => original row (List.mem_cons_of_mem node member)
    simp only [List.foldlM_cons] at sourceRun <;> try contradiction
    cases step : addLocalTypeNode direct indirect source node with
    | error error => simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    | ok midSource =>
      simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      obtain ⟨midTarget, targetStep, midExtension⟩ :=
        addNode_fresh_extension direct indirect fresh ty source target extension node midSource head step
      obtain ⟨targetResult, targetRun, outputExtension⟩ :=
        ih midSource midTarget midExtension result tail sourceRun
      refine ⟨targetResult, ?_, outputExtension⟩
      rw [List.foldlM_cons, targetStep]
      exact targetRun

def SourceAvoids (fresh : Nat) : LocalTypeSource → Prop
  | .declared _ => True
  | .borrow operand => operand.index ≠ fresh

/-- Every use is included in the source freshness domain, not merely result
    declarations. In particular a Borrow cannot acquire a new root. -/
structure OriginalState (fresh : Nat) (state : DeclarationState) : Prop where
  missing : state.fst.find? fresh = none
  ids : ∀ id ∈ state.snd, id.index ≠ fresh
  sources : ∀ query entry, state.fst.find? query = some entry → SourceAvoids fresh entry

theorem original_empty (fresh : Nat) :
    OriginalState fresh (NatIndex.empty, []) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro id member; cases member
  · intro query entry found; cases found

theorem addSource_original (fresh : Nat) (state : DeclarationState)
    (originalState : OriginalState fresh state) (id : ValueId) (entry : LocalTypeSource)
    (result : DeclarationState) (originalId : id.index ≠ fresh)
    (originalEntry : SourceAvoids fresh entry)
    (sourceRun : addLocalTypeSource state id entry = .ok result) : OriginalState fresh result := by
  cases present : state.fst.contains id.index with
  | true => simp only [addLocalTypeSource, present, if_true] at sourceRun <;> try contradiction
  | false =>
    simp only [addLocalTypeSource, present, Bool.false_eq_true, if_false] at sourceRun <;> try contradiction
    have output := Except.ok.inj sourceRun
    rw [← output]
    refine ⟨?_, ?_, ?_⟩
    · rw [NatIndex.find?_insert_ne _ _ _ _ (Ne.symm originalId)]
      exact originalState.missing
    · intro item member
      rcases List.mem_cons.mp member with same | old
      · subst item; exact originalId
      · exact originalState.ids item old
    · intro query source found
      rw [NatIndex.find?_insert] at found
      split at found
      · cases found; exact originalEntry
      · exact originalState.sources query source found

theorem addSources_original (fresh : Nat) (entries : List (ValueId × LocalTypeSource))
    (state result : DeclarationState) (originalState : OriginalState fresh state)
    (originalEntries : ∀ row ∈ entries, row.fst.index ≠ fresh ∧ SourceAvoids fresh row.snd)
    (sourceRun : entries.foldlM (fun acc row => addLocalTypeSource acc row.fst row.snd)
      state = .ok result) : OriginalState fresh result := by
  induction entries generalizing state result with
  | nil =>
    have output : state = result := Except.ok.inj sourceRun
    subst result
    exact originalState
  | cons row rest ih =>
    have head := originalEntries row ((trustIrListMemConsSelf _ _))
    have tail : ∀ entry ∈ rest, entry.fst.index ≠ fresh ∧ SourceAvoids fresh entry.snd :=
      fun entry member => originalEntries entry (List.mem_cons_of_mem row member)
    simp only [List.foldlM_cons] at sourceRun <;> try contradiction
    cases step : addLocalTypeSource state row.fst row.snd with
    | error error => simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    | ok mid =>
      simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      exact ih mid result
        (addSource_original fresh state originalState row.fst row.snd mid head.1 head.2 step)
        tail sourceRun

theorem zip_snd_mem {α β : Type} (left : List α) (right : List β)
    (row : α × β) (member : row ∈ left.zip right) : row.snd ∈ right := by
  induction left generalizing right with
  | nil => cases member
  | cons item rest ih =>
    cases right with
    | nil => cases member
    | cons entry entries =>
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with same | old
      · subst row; exact (trustIrListMemConsSelf _ _)
      · exact List.mem_cons_of_mem entry (ih entries old)

theorem addNode_original (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (state result : DeclarationState) (originalState : OriginalState fresh state)
    (node : Inst × List ValueId) (originalIds : ∀ id ∈ node.snd, id.index ≠ fresh)
    (originalSources : ∀ types, localResultTypes direct indirect node.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry)
    (sourceRun : addLocalTypeNode direct indirect state node = .ok result) :
    OriginalState fresh result := by
  unfold addLocalTypeNode at sourceRun <;> try contradiction
  cases classified : localResultTypes direct indirect node.fst with
  | error error => simp only [classified, Bind.bind, Except.bind] at sourceRun <;> try contradiction
  | ok types =>
    simp only [classified, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    by_cases census : types.length != node.snd.length
    · simp only [census, if_true, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    · simp only [census, Bool.false_eq_true, if_false, Bind.bind, Pure.pure,
        Except.bind, Except.pure] at sourceRun <;> try contradiction
      exact addSources_original fresh (node.snd.zip types) state result originalState
        (fun row member =>
          ⟨originalIds row.fst (zip_fst_mem node.snd types row member),
            originalSources types classified row.snd (zip_snd_mem node.snd types row member)⟩) sourceRun

theorem collectNodes_original (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (nodes : List (Inst × List ValueId)) (state result : DeclarationState)
    (originalState : OriginalState fresh state)
    (originalIds : ∀ node ∈ nodes, ∀ id ∈ node.snd, id.index ≠ fresh)
    (originalSources : ∀ node ∈ nodes, ∀ types,
      localResultTypes direct indirect node.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry)
    (sourceRun : nodes.foldlM (addLocalTypeNode direct indirect) state = .ok result) :
    OriginalState fresh result := by
  induction nodes generalizing state result with
  | nil =>
    have output : state = result := Except.ok.inj sourceRun
    subst result
    exact originalState
  | cons node rest ih =>
    have headIds := originalIds node ((trustIrListMemConsSelf _ _))
    have headSources := originalSources node ((trustIrListMemConsSelf _ _))
    have tailIds : ∀ row ∈ rest, ∀ id ∈ row.snd, id.index ≠ fresh :=
      fun row member => originalIds row (List.mem_cons_of_mem node member)
    have tailSources : ∀ row ∈ rest, ∀ types,
        localResultTypes direct indirect row.fst = .ok types →
        ∀ entry ∈ types, SourceAvoids fresh entry :=
      fun row member => originalSources row (List.mem_cons_of_mem node member)
    simp only [List.foldlM_cons] at sourceRun <;> try contradiction
    cases step : addLocalTypeNode direct indirect state node with
    | error error => simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    | ok mid =>
      simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      exact ih mid result (addNode_original direct indirect fresh state mid originalState node
        headIds headSources step) tailIds tailSources sourceRun

theorem withoutFresh_eq_self (fresh : Nat) (ids : List ValueId)
    (original : ∀ id ∈ ids, id.index ≠ fresh) : withoutFresh fresh ids = ids := by
  induction ids with
  | nil => rfl
  | cons id rest ih =>
    have head := original id ((trustIrListMemConsSelf _ _))
    have tail := fun item member => original item (List.mem_cons_of_mem id member)
    simp only [withoutFresh, if_neg head, ih tail]

theorem freshNode_seed (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (ty : Ty) (state : DeclarationState) (originalState : OriginalState fresh state)
    (inst : Inst) (classified : localResultTypes direct indirect inst = .ok [.declared ty]) :
    addLocalTypeNode direct indirect state (inst, [⟨fresh⟩]) =
      .ok (state.fst.insert fresh (.declared ty), ⟨fresh⟩ :: state.snd) ∧
    DeclarationExtension fresh ty state
      (state.fst.insert fresh (.declared ty), ⟨fresh⟩ :: state.snd) := by
  constructor
  · simp only [addLocalTypeNode, classified, Bind.bind, Pure.pure, Except.bind, Except.pure,
      List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, if_false,
      List.zip_cons_cons, List.zip_nil_left, List.foldlM_cons, List.foldlM_nil,
      addLocalTypeSource, NatIndex.contains, originalState.missing, Option.isSome,
      List.foldl_nil]
  · refine ⟨?_, NatIndex.find?_insert_same _ _ _, ?_, ?_⟩
    · intro query original
      exact (NatIndex.find?_insert_ne _ _ _ _ original).symm
    · simp only [withoutFresh, if_pos rfl]
      exact withoutFresh_eq_self fresh state.snd originalState.ids
    · simp only [seenFresh, if_pos rfl, ite_true]

theorem withoutFresh_length_le (fresh : Nat) (ids : List ValueId) :
    (withoutFresh fresh ids).length ≤ ids.length := by
  induction ids with
  | nil => exact Nat.le_refl _
  | cons id rest ih =>
    simp only [withoutFresh]
    split <;> simp only [List.length_cons] <;> omega

theorem DeclarationExtension.length_le {fresh : Nat} {ty : Ty}
    {source target : DeclarationState} (extension : DeclarationExtension fresh ty source target) :
    source.snd.length ≤ target.snd.length := by
  rw [← extension.ids]
  exact withoutFresh_length_le fresh target.snd

theorem addNode_empty (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (state : DeclarationState) (inst : Inst)
    (classified : localResultTypes direct indirect inst = .ok []) :
    addLocalTypeNode direct indirect state (inst, []) = .ok state := by
  simp only [addLocalTypeNode, classified, Bind.bind, Pure.pure, Except.bind, Except.pure,
    List.length_nil, bne_self_eq_false, Bool.false_eq_true, if_false,
    List.zip_nil_left, List.foldlM_nil]

/-- Zero-result source nodes such as CoroSuspend, Return and Store do not
    alter the declaration graph when their actual destination row is empty. -/
theorem collectNodes_insert_empty (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (beforeNodes afterNodes : List (Inst × List ValueId)) (state : DeclarationState) (inst : Inst)
    (classified : localResultTypes direct indirect inst = .ok []) :
    (beforeNodes ++ (inst, []) :: afterNodes).foldlM (addLocalTypeNode direct indirect) state =
      (beforeNodes ++ afterNodes).foldlM (addLocalTypeNode direct indirect) state := by
  simp only [List.foldlM_append, List.foldlM_cons, addNode_empty direct indirect _ inst classified,
    Bind.bind, Except.bind]

theorem addNode_success_census (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (state result : DeclarationState) (node : Inst × List ValueId) (types : List LocalTypeSource)
    (classified : localResultTypes direct indirect node.fst = .ok types)
    (sourceRun : addLocalTypeNode direct indirect state node = .ok result) :
    types.length = node.snd.length := by
  by_cases census : types.length = node.snd.length
  · exact census
  · have mismatch : (types.length != node.snd.length) = true := by simp [census]
    simp only [addLocalTypeNode, classified, Bind.bind, Pure.pure, Except.bind, Except.pure,
      mismatch, if_true] at sourceRun <;> try contradiction

theorem collectParams_original (fresh : Nat) (params : List (ValueId × Ty))
    (state result : DeclarationState) (originalState : OriginalState fresh state)
    (originalIds : ∀ row ∈ params, row.fst.index ≠ fresh)
    (sourceRun : params.foldlM
      (fun acc row => addLocalTypeSource acc row.fst (.declared row.snd)) state = .ok result) :
    OriginalState fresh result := by
  induction params generalizing state result with
  | nil =>
    have output : state = result := Except.ok.inj sourceRun
    subst result
    exact originalState
  | cons row rest ih =>
    have head := originalIds row ((trustIrListMemConsSelf _ _))
    have tail := fun item member => originalIds item (List.mem_cons_of_mem row member)
    simp only [List.foldlM_cons] at sourceRun <;> try contradiction
    cases step : addLocalTypeSource state row.fst (.declared row.snd) with
    | error error => simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    | ok mid =>
      simp only [step, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      exact ih mid result
        (addSource_original fresh state originalState row.fst (.declared row.snd) mid
          head True.intro step) tail sourceRun

def resolvedTable (memo : ResolutionIndex) : LocalTypeTable := fun id =>
  match memo.find? id.index with
  | some (.resolved ty) => some ty
  | _ => none

/-- The exact post-resolution record returned by actual inference. -/
def inferenceRecord (declarations : DeclarationIndex) (memo : ResolutionIndex)
    (work : LocalTypeWork) : LocalTypeInference :=
  { table := resolvedTable memo
    work := { work with declarationDepth := declarations.depth, memoDepth := memo.depth }
    keyBound := memo.keyBound
    outsideBound := by
      intro id bound
      change (match memo.find? id.index with | some (.resolved ty) => some ty | _ => none) = none
      have missing : memo.find? id.index = none := memo.outsideBound id.index bound
      rw [missing] }

/-- A named tail view of the actual collection/resolution computation. -/
def collectedInference (state : DeclarationState) : Except SemError LocalTypeInference := do
  let (memo, work) ← resolveAll state.fst (state.snd.length + 1) state.snd
    (NatIndex.empty, {declarations := state.snd.length})
  pure (inferenceRecord state.fst memo work)

/-- This equality anchors the named proof views to the real implementation,
    including every original collection or resolution refusal and its order. -/
theorem inference_eq_collection (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId)) :
    inferLocalTypesWithEvidence direct indirect params nodes = (do
      let initial ← params.foldlM
        (fun acc row => addLocalTypeSource acc row.fst (.declared row.snd)) (NatIndex.empty, [])
      let state ← nodes.foldlM (addLocalTypeNode direct indirect) initial
      collectedInference state) := by
  rfl

theorem collectedInference_fresh_extension (fresh : Nat) (ty : Ty)
    (source target : DeclarationState) (extension : DeclarationExtension fresh ty source target)
    (borrowOriginal : ∀ id operand,
      source.fst.find? id = some (.borrow operand) → operand.index ≠ fresh)
    (inferred : LocalTypeInference) (sourceRun : collectedInference source = .ok inferred) :
    ∃ targetInferred,
      collectedInference target = .ok targetInferred ∧
      targetInferred.table ⟨fresh⟩ = some ty ∧
      (∀ id : ValueId, id.index ≠ fresh → inferred.table id = targetInferred.table id) := by
  unfold collectedInference at sourceRun <;> try contradiction
  cases resolved : resolveAll source.fst (source.snd.length + 1) source.snd
      (NatIndex.empty, {declarations := source.snd.length}) with
  | error error => simp only [resolved, Bind.bind, Except.bind] at sourceRun <;> try contradiction
  | ok result =>
    rcases result with ⟨memo, work⟩
    simp only [resolved, Bind.bind, Pure.pure, Except.bind, Except.pure] at sourceRun <;> try contradiction
    have sourceRecord := Except.ok.inj sourceRun
    have erasedRun : resolveAll source.fst (source.snd.length + 1) (withoutFresh fresh target.snd)
        (NatIndex.empty, {declarations := source.snd.length}) = .ok (memo, work) := by
      rw [extension.ids]
      exact resolved
    let extra := target.snd.length - source.snd.length
    have targetFuel : source.snd.length + 1 + extra = target.snd.length + 1 := by
      have lengthBound := extension.length_le
      dsimp only [extra]
      omega
    obtain ⟨targetMemo, targetWork, targetRun, memoAgree, freshResolved⟩ :=
      resolveAll_fresh_extension source.fst target.fst fresh ty extension.agree borrowOriginal
        extension.freshBinding source.snd.length extra target.snd
        NatIndex.empty NatIndex.empty {declarations := source.snd.length}
        {declarations := target.snd.length} memo work
        (by intro query _; rfl) (Or.inl rfl) erasedRun
    rw [targetFuel] at targetRun
    refine ⟨inferenceRecord target.fst targetMemo targetWork, ?_, ?_, ?_⟩
    · simp only [collectedInference, targetRun, Bind.bind, Pure.pure, Except.bind, Except.pure]
    · simp only [extension.seen, if_true] at freshResolved
      change (match targetMemo.find? fresh with | some (.resolved ty) => some ty | _ => none) = some ty
      rw [freshResolved]
    · intro id original
      rw [← sourceRecord]
      change (match memo.find? id.index with | some (.resolved ty) => some ty | _ => none) =
        (match targetMemo.find? id.index with | some (.resolved ty) => some ty | _ => none)
      rw [memoAgree id.index original]

/-- Inserting a source-classified fresh result at any serialization position
    succeeds in the ACTUAL inference implementation and preserves every old
    binding. Freshness covers parameters, destinations and Borrow uses. This
    is an algorithm theorem, not a caller-supplied metadata agreement. -/
theorem infer_insert_fresh (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (beforeNodes afterNodes : List (Inst × List ValueId))
    (fresh : Nat) (ty : Ty) (inst : Inst)
    (classified : localResultTypes direct indirect inst = .ok [.declared ty])
    (originalParams : ∀ row ∈ params, row.fst.index ≠ fresh)
    (originalIds : ∀ node ∈ beforeNodes ++ afterNodes, ∀ id ∈ node.snd, id.index ≠ fresh)
    (originalSources : ∀ node ∈ beforeNodes ++ afterNodes, ∀ types,
      localResultTypes direct indirect node.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry)
    (inferred : LocalTypeInference)
    (sourceRun : inferLocalTypesWithEvidence direct indirect params
      (beforeNodes ++ afterNodes) = .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect params
        (beforeNodes ++ (inst, [⟨fresh⟩]) :: afterNodes) = .ok targetInferred ∧
      targetInferred.table ⟨fresh⟩ = some ty ∧
      (∀ id : ValueId, id.index ≠ fresh → inferred.table id = targetInferred.table id) := by
  have beforeIds : ∀ node ∈ beforeNodes, ∀ id ∈ node.snd, id.index ≠ fresh :=
    fun node member => originalIds node (trustIrListMemAppendLeft afterNodes member)
  have afterIds : ∀ node ∈ afterNodes, ∀ id ∈ node.snd, id.index ≠ fresh :=
    fun node member => originalIds node (trustIrListMemAppendRight beforeNodes member)
  have beforeSources : ∀ node ∈ beforeNodes, ∀ types,
      localResultTypes direct indirect node.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry :=
    fun node member => originalSources node (trustIrListMemAppendLeft afterNodes member)
  have afterSources : ∀ node ∈ afterNodes, ∀ types,
      localResultTypes direct indirect node.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry :=
    fun node member => originalSources node (trustIrListMemAppendRight beforeNodes member)
  rw [inference_eq_collection] at sourceRun <;> try contradiction
  cases paramsRun : params.foldlM
      (fun acc row => addLocalTypeSource acc row.fst (.declared row.snd)) (NatIndex.empty, []) with
  | error error => simp only [paramsRun, Bind.bind, Except.bind] at sourceRun <;> try contradiction
  | ok initial =>
    simp only [paramsRun, Bind.bind, Except.bind, List.foldlM_append] at sourceRun <;> try contradiction
    have initialOriginal := collectParams_original fresh params (NatIndex.empty, []) initial
      (original_empty fresh) originalParams paramsRun
    cases beforeRun : beforeNodes.foldlM (addLocalTypeNode direct indirect) initial with
    | error error => simp only [beforeRun, Bind.bind, Except.bind] at sourceRun <;> try contradiction
    | ok middle =>
      simp only [beforeRun, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      have middleOriginal := collectNodes_original direct indirect fresh beforeNodes initial middle
        initialOriginal beforeIds beforeSources beforeRun
      cases afterRun : afterNodes.foldlM (addLocalTypeNode direct indirect) middle with
      | error error => simp only [afterRun, Bind.bind, Except.bind] at sourceRun <;> try contradiction
      | ok sourceFinal =>
        simp only [afterRun, Bind.bind, Except.bind] at sourceRun <;> try contradiction
        have finalOriginal := collectNodes_original direct indirect fresh afterNodes middle sourceFinal
          middleOriginal afterIds afterSources afterRun
        obtain ⟨newNodeRun, seed⟩ :=
          freshNode_seed direct indirect fresh ty middle middleOriginal inst classified
        obtain ⟨targetFinal, targetAfterRun, extended⟩ :=
          collectNodes_fresh_extension direct indirect fresh ty afterNodes middle
            (middle.fst.insert fresh (.declared ty), ⟨fresh⟩ :: middle.snd) seed
            sourceFinal afterIds afterRun
        have borrowOriginal : ∀ id operand,
            sourceFinal.fst.find? id = some (.borrow operand) → operand.index ≠ fresh :=
          fun id operand found => finalOriginal.sources id (.borrow operand) found
        obtain ⟨targetInferred, targetTail, freshType, preserved⟩ :=
          collectedInference_fresh_extension fresh ty sourceFinal targetFinal extended
            borrowOriginal inferred sourceRun
        refine ⟨targetInferred, ?_, freshType, preserved⟩
        simp only [inference_eq_collection, paramsRun, List.foldlM_append, beforeRun,
          List.foldlM_cons, newNodeRun, targetAfterRun, Bind.bind, Except.bind]
        exact targetTail


theorem resolve_preserves_fresh (decls : DeclarationIndex) (fresh : Nat)
    (borrowOriginal : ∀ id operand,
      decls.find? id = some (.borrow operand) → operand.index ≠ fresh)
    (fuel : Nat) (id : ValueId) (path : List ValueId)
    (memo result : ResolutionIndex) (work resultWork : LocalTypeWork)
    (originalId : id.index ≠ fresh) (originalPath : ∀ item ∈ path, item.index ≠ fresh)
    (run : resolveLocalType decls fuel id path memo work = .ok (result, resultWork)) :
    result.find? fresh = memo.find? fresh := by
  obtain ⟨targetResult, targetWork, targetRun, _, freshEq⟩ :=
    resolve_fresh_extension decls decls fresh (by intro query _; rfl) borrowOriginal
      fuel 0 id path memo memo work work result resultWork originalId originalPath
      (by intro query _; rfl) run
  simp only [Nat.add_zero] at targetRun
  have resultEq := congrArg Prod.fst (Except.ok.inj (run.symm.trans targetRun))
  dsimp only at resultEq
  rw [← resultEq] at freshEq
  exact freshEq

theorem resolveAll_preserves_fresh (decls : DeclarationIndex) (fresh : Nat)
    (borrowOriginal : ∀ id operand,
      decls.find? id = some (.borrow operand) → operand.index ≠ fresh)
    (fuel : Nat) (ids : List ValueId) (memo result : ResolutionIndex)
    (work resultWork : LocalTypeWork)
    (originalIds : ∀ id ∈ ids, id.index ≠ fresh)
    (run : resolveAll decls fuel ids (memo, work) = .ok (result, resultWork)) :
    result.find? fresh = memo.find? fresh := by
  induction ids generalizing memo result work resultWork with
  | nil =>
    have resultEq := congrArg Prod.fst (Except.ok.inj run)
    dsimp only at resultEq
    rw [← resultEq]
  | cons id rest ih =>
    have head := originalIds id ((trustIrListMemConsSelf _ _))
    have tail := fun item member => originalIds item (List.mem_cons_of_mem id member)
    simp only [resolveAll_cons] at run <;> try contradiction
    cases step : resolveLocalType decls fuel id [] memo work with
    | error error => simp only [step, Bind.bind, Except.bind] at run <;> try contradiction
    | ok mid =>
      rcases mid with ⟨midMemo, midWork⟩
      simp only [step, Bind.bind, Except.bind] at run <;> try contradiction
      have stepFresh := resolve_preserves_fresh decls fresh borrowOriginal fuel id [] memo midMemo
        work midWork head (by intro item member; cases member) step
      have restFresh := ih midMemo result midWork resultWork tail run
      exact restFresh.trans stepFresh

theorem collectedInference_missing (fresh : Nat) (state : DeclarationState)
    (original : OriginalState fresh state) (inferred : LocalTypeInference)
    (run : collectedInference state = .ok inferred) : inferred.table ⟨fresh⟩ = none := by
  unfold collectedInference at run <;> try contradiction
  cases resolved : resolveAll state.fst (state.snd.length + 1) state.snd
      (NatIndex.empty, {declarations := state.snd.length}) with
  | error error => simp only [resolved, Bind.bind, Except.bind] at run <;> try contradiction
  | ok result =>
    rcases result with ⟨memo, work⟩
    simp only [resolved, Bind.bind, Pure.pure, Except.bind, Except.pure] at run <;> try contradiction
    have record := Except.ok.inj run
    have borrowOriginal : ∀ id operand,
        state.fst.find? id = some (.borrow operand) → operand.index ≠ fresh :=
      fun id operand found => original.sources id (.borrow operand) found
    have missing := resolveAll_preserves_fresh state.fst fresh borrowOriginal
      (state.snd.length + 1) state.snd NatIndex.empty memo {declarations := state.snd.length}
      work original.ids resolved
    rw [NatIndex.find?_empty] at missing
    rw [← record]
    change (match memo.find? fresh with | some (.resolved ty) => some ty | _ => none) = none
    rw [missing]

theorem infer_missing (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId)) (fresh : Nat)
    (originalParams : ∀ row ∈ params, row.fst.index ≠ fresh)
    (originalIds : ∀ node ∈ nodes, ∀ id ∈ node.snd, id.index ≠ fresh)
    (originalSources : ∀ node ∈ nodes, ∀ types,
      localResultTypes direct indirect node.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry)
    (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect params nodes = .ok inferred) :
    inferred.table ⟨fresh⟩ = none := by
  rw [inference_eq_collection] at run <;> try contradiction
  cases paramsRun : params.foldlM
      (fun acc row => addLocalTypeSource acc row.fst (.declared row.snd)) (NatIndex.empty, []) with
  | error error => simp only [paramsRun, Bind.bind, Except.bind] at run <;> try contradiction
  | ok initial =>
    simp only [paramsRun, Bind.bind, Except.bind] at run <;> try contradiction
    have initialOriginal := collectParams_original fresh params (NatIndex.empty, []) initial
      (original_empty fresh) originalParams paramsRun
    cases nodesRun : nodes.foldlM (addLocalTypeNode direct indirect) initial with
    | error error => simp only [nodesRun, Bind.bind, Except.bind] at run <;> try contradiction
    | ok finalState =>
      simp only [nodesRun, Bind.bind, Except.bind] at run <;> try contradiction
      have finalOriginal := collectNodes_original direct indirect fresh nodes initial finalState
        initialOriginal originalIds originalSources nodesRun
      exact collectedInference_missing fresh finalState finalOriginal inferred run

/-- An explicit header-indexed form also covers direct and indirect calls in
    arbitrary, possibly unreached, source blocks. -/
structure InputAvoids (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId)) : Prop where
  params : ∀ row ∈ params, row.fst.index ≠ fresh
  destinations : ∀ node ∈ nodes, ∀ id ∈ node.snd, id.index ≠ fresh
  sources : ∀ node ∈ nodes, ∀ types,
    localResultTypes direct indirect node.fst = .ok types →
    ∀ entry ∈ types, SourceAvoids fresh entry

theorem append_member_cases {α : Type} (before after : List α) (item : α)
    (member : item ∈ before ++ after) : item ∈ before ∨ item ∈ after := by
  induction before with
  | nil => exact Or.inr member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | old
    · exact Or.inl (List.mem_cons.mpr (Or.inl same))
    · rcases ih old with left | right
      · exact Or.inl (List.mem_cons_of_mem head left)
      · exact Or.inr right

theorem InputAvoids.insert_declared
    {direct : FuncId → Option FuncTyDef} {indirect : FuncTyTable}
    {fresh : Nat} {params : List (ValueId × Ty)} {before after : List (Inst × List ValueId)}
    (original : InputAvoids direct indirect fresh params (before ++ after))
    (inst : Inst) (dest : ValueId) (ty : Ty) (different : dest.index ≠ fresh)
    (classified : localResultTypes direct indirect inst = .ok [.declared ty]) :
    InputAvoids direct indirect fresh params (before ++ (inst, [dest]) :: after) := by
  refine ⟨original.params, ?_, ?_⟩
  · intro node member id inDests
    rcases append_member_cases before ((inst, [dest]) :: after) node member with left | right
    · exact original.destinations node (trustIrListMemAppendLeft after left) id inDests
    · rcases List.mem_cons.mp right with same | old
      · subst node
        rcases List.mem_cons.mp inDests with same | empty
        · subst id; exact different
        · cases empty
      · exact original.destinations node (trustIrListMemAppendRight before old) id inDests
  · intro node member types found entry inTypes
    rcases append_member_cases before ((inst, [dest]) :: after) node member with left | right
    · exact original.sources node (trustIrListMemAppendLeft after left) types found entry inTypes
    · rcases List.mem_cons.mp right with same | old
      · subst node
        have actual := Except.ok.inj (classified.symm.trans found)
        subst types
        rcases List.mem_cons.mp inTypes with same | empty
        · subst entry; trivial
        · cases empty
      · exact original.sources node (trustIrListMemAppendRight before old) types found entry inTypes

theorem infer_insert_of_avoid (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (before after : List (Inst × List ValueId))
    (fresh : Nat) (ty : Ty) (inst : Inst)
    (classified : localResultTypes direct indirect inst = .ok [.declared ty])
    (original : InputAvoids direct indirect fresh params (before ++ after))
    (inferred : LocalTypeInference)
    (sourceRun : inferLocalTypesWithEvidence direct indirect params (before ++ after) = .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect params
        (before ++ (inst, [⟨fresh⟩]) :: after) = .ok targetInferred ∧
      targetInferred.table ⟨fresh⟩ = some ty ∧
      (∀ id : ValueId, id.index ≠ fresh → inferred.table id = targetInferred.table id) :=
  infer_insert_fresh direct indirect params before after fresh ty inst classified
    original.params original.destinations original.sources inferred sourceRun

theorem collectNodes_success_census (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (nodes : List (Inst × List ValueId)) (state result : DeclarationState)
    (node : Inst × List ValueId) (types : List LocalTypeSource) (member : node ∈ nodes)
    (classified : localResultTypes direct indirect node.fst = .ok types)
    (run : nodes.foldlM (addLocalTypeNode direct indirect) state = .ok result) :
    types.length = node.snd.length := by
  induction nodes generalizing state result with
  | nil => cases member
  | cons head rest ih =>
    simp only [List.foldlM_cons] at run <;> try contradiction
    cases step : addLocalTypeNode direct indirect state head with
    | error error => simp only [step, Bind.bind, Except.bind] at run <;> try contradiction
    | ok mid =>
      simp only [step, Bind.bind, Except.bind] at run <;> try contradiction
      rcases List.mem_cons.mp member with same | old
      · subst node
        exact addNode_success_census direct indirect state mid head types classified step
      · exact ih mid result old run

theorem infer_success_census (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (nodes : List (Inst × List ValueId))
    (node : Inst × List ValueId) (types : List LocalTypeSource) (member : node ∈ nodes)
    (classified : localResultTypes direct indirect node.fst = .ok types)
    (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect params nodes = .ok inferred) :
    types.length = node.snd.length := by
  rw [inference_eq_collection] at run <;> try contradiction
  cases paramsRun : params.foldlM
      (fun acc row => addLocalTypeSource acc row.fst (.declared row.snd)) (NatIndex.empty, []) with
  | error error => simp only [paramsRun, Bind.bind, Except.bind] at run <;> try contradiction
  | ok initial =>
    simp only [paramsRun, Bind.bind, Except.bind] at run <;> try contradiction
    cases nodesRun : nodes.foldlM (addLocalTypeNode direct indirect) initial with
    | error error => simp only [nodesRun, Bind.bind, Except.bind] at run <;> try contradiction
    | ok finalState =>
      exact collectNodes_success_census direct indirect nodes initial finalState node types member classified nodesRun

theorem infer_insert_empty (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (before after : List (Inst × List ValueId))
    (inst : Inst) (classified : localResultTypes direct indirect inst = .ok []) :
    inferLocalTypesWithEvidence direct indirect params (before ++ (inst, []) :: after) =
      inferLocalTypesWithEvidence direct indirect params (before ++ after) := by
  rw [inference_eq_collection, inference_eq_collection]
  cases initialRun : params.foldlM
      (fun acc row => addLocalTypeSource acc row.fst (.declared row.snd)) (NatIndex.empty, []) with
  | error error => simp only [initialRun, Bind.bind, Except.bind]
  | ok initial =>
    simp only [initialRun, Bind.bind, Except.bind]
    rw [collectNodes_insert_empty direct indirect before after initial inst classified]

/-- Compose three actual source insertions. Every destination type is derived
    from its instruction classifier; no target table is supplied. -/
theorem infer_insert_three (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (params : List (ValueId × Ty)) (before after : List (Inst × List ValueId))
    (first second third : Nat) (firstTy secondTy thirdTy : Ty)
    (firstInst secondInst thirdInst : Inst)
    (firstClass : localResultTypes direct indirect firstInst = .ok [.declared firstTy])
    (secondClass : localResultTypes direct indirect secondInst = .ok [.declared secondTy])
    (thirdClass : localResultTypes direct indirect thirdInst = .ok [.declared thirdTy])
    (firstSecond : first ≠ second) (firstThird : first ≠ third) (secondThird : second ≠ third)
    (avoidFirst : InputAvoids direct indirect first params (before ++ after))
    (avoidSecond : InputAvoids direct indirect second params (before ++ after))
    (avoidThird : InputAvoids direct indirect third params (before ++ after))
    (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect params (before ++ after) = .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect params
        (before ++ (firstInst, [⟨first⟩]) :: (secondInst, [⟨second⟩]) ::
          (thirdInst, [⟨third⟩]) :: after) = .ok targetInferred ∧
      targetInferred.table ⟨first⟩ = some firstTy ∧
      targetInferred.table ⟨second⟩ = some secondTy ∧
      targetInferred.table ⟨third⟩ = some thirdTy ∧
      (∀ id : ValueId, id.index ≠ first → id.index ≠ second → id.index ≠ third →
        inferred.table id = targetInferred.table id) := by
  obtain ⟨afterFirst, firstRun, firstType, firstPreserved⟩ :=
    infer_insert_of_avoid direct indirect params before after first firstTy firstInst
      firstClass avoidFirst inferred run
  have avoidSecondNow := avoidSecond.insert_declared firstInst ⟨first⟩ firstTy firstSecond firstClass
  have avoidThirdNow := avoidThird.insert_declared firstInst ⟨first⟩ firstTy firstThird firstClass
  have firstRun' : inferLocalTypesWithEvidence direct indirect params
      ((before ++ [(firstInst, [⟨first⟩])]) ++ after) = .ok afterFirst := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using firstRun
  have avoidSecondNow' : InputAvoids direct indirect second params
      ((before ++ [(firstInst, [⟨first⟩])]) ++ after) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using avoidSecondNow
  have avoidThirdNow' : InputAvoids direct indirect third params
      ((before ++ [(firstInst, [⟨first⟩])]) ++ after) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using avoidThirdNow
  obtain ⟨afterSecond, secondRun, secondType, secondPreserved⟩ :=
    infer_insert_of_avoid direct indirect params (before ++ [(firstInst, [⟨first⟩])]) after
      second secondTy secondInst secondClass avoidSecondNow' afterFirst firstRun'
  have avoidThirdLast := avoidThirdNow'.insert_declared secondInst ⟨second⟩ secondTy secondThird secondClass
  have secondRun' : inferLocalTypesWithEvidence direct indirect params
      ((before ++ [(firstInst, [⟨first⟩]), (secondInst, [⟨second⟩])]) ++ after) = .ok afterSecond := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using secondRun
  have avoidThirdLast' : InputAvoids direct indirect third params
      ((before ++ [(firstInst, [⟨first⟩]), (secondInst, [⟨second⟩])]) ++ after) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using avoidThirdLast
  obtain ⟨targetInferred, targetRun, thirdType, thirdPreserved⟩ :=
    infer_insert_of_avoid direct indirect params
      (before ++ [(firstInst, [⟨first⟩]), (secondInst, [⟨second⟩])]) after
      third thirdTy thirdInst thirdClass avoidThirdLast' afterSecond secondRun'
  refine ⟨targetInferred, ?_, ?_, ?_, thirdType, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using targetRun
  · exact ((secondPreserved ⟨first⟩ firstSecond).trans
      (thirdPreserved ⟨first⟩ firstThird)).symm.trans firstType
  · exact (thirdPreserved ⟨second⟩ secondThird).symm.trans secondType
  · intro id notFirst notSecond notThird
    exact (firstPreserved id notFirst).trans
      ((secondPreserved id notSecond).trans (thirdPreserved id notThird))

theorem InputAvoids.mono {direct : FuncId → Option FuncTyDef} {indirect : FuncTyTable}
    {fresh : Nat} {params : List (ValueId × Ty)} {source target : List (Inst × List ValueId)}
    (original : InputAvoids direct indirect fresh params source)
    (included : ∀ node ∈ target, node ∈ source) : InputAvoids direct indirect fresh params target :=
  ⟨original.params,
    fun node member => original.destinations node (included node member),
    fun node member => original.sources node (included node member)⟩

theorem InputAvoids.removeNode {direct : FuncId → Option FuncTyDef} {indirect : FuncTyTable}
    {fresh : Nat} {params : List (ValueId × Ty)} {before after : List (Inst × List ValueId)}
    {removed : Inst × List ValueId}
    (original : InputAvoids direct indirect fresh params (before ++ removed :: after)) :
    InputAvoids direct indirect fresh params (before ++ after) := by
  apply original.mono
  intro node member
  rcases append_member_cases before after node member with left | right
  · exact trustIrListMemAppendLeft _ left
  · exact trustIrListMemAppendRight _ (List.mem_cons_of_mem removed right)

end TrustIr.LocalTypeInference
