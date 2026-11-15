-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksPlanner
import TrustIr.Proofs.GenericCoroGraphViews

namespace TrustIr.GenericCoroAllBlocksViews
open GenericCoro GenericCoroFreshCursor GenericCoroAllBlocksPlanner

/-- Exact ordered interface rows follow from the ACTUAL planner relation.
    Labels are not sorted, deduplicated or interpreted as a finite set. -/
theorem interface_rows {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    source.map (fun row => (row.1, GraphViews.blockInterface row.2)) =
      target.map (fun row => (row.1, GraphViews.blockInterface row.2)) := by
  induction plan with
  | nil => rfl
  | keep _ _ _ _ _ _ _ _ _ ih => exact congrArg (_ :: ·) ih
  | expand _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [List.map_cons, GraphViews.expandedEntry_interface]
    exact congrArg (_ :: ·) ih

theorem cfg_interface {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (query : BlockId) :
    (cfgOf source query).map GraphViews.blockInterface =
      (cfgOf target query).map GraphViews.blockInterface :=
  GraphViews.cfgOf_observation_of_rows GraphViews.blockInterface source target
    (interface_rows plan) query

/-- This includes missing blocks and shadowed duplicate labels, rather than
    assuming that a CFG lookup identifies a unique source row. -/
theorem cfg_params {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (query : BlockId) :
    (cfgOf source query).map BasicBlock.params = (cfgOf target query).map BasicBlock.params :=
  GraphViews.params_of_interface_rows source target (interface_rows plan) query

/-- The outer option still records block presence. The inner option still
    distinguishes a present non-pad block from an actual landing pad. -/
theorem padViews {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace) :
    PadViews.PadViewsAgree (cfgOf source) (cfgOf target) :=
  GraphViews.padViews_of_interface_rows source target (interface_rows plan)

theorem semEnterPad_eq {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (exception : Addr) (query : BlockId) :
    semEnterPad (cfgOf source) exception query = semEnterPad (cfgOf target) exception query :=
  PadViews.semEnterPad_congr _ _ _ _ (padViews plan query)

theorem stepTermUnwind_eq {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (term : Inst) (model : ByteModel) :
    stepTermUnwind (cfgOf source) term model = stepTermUnwind (cfgOf target) term model :=
  PadViews.stepTermUnwind_congr _ _ _ _ (padViews plan)

/-- A first-match lookup observes either absence, the exact retained row,
    or that row's actual expansion and its recorded generated names. Trace
    membership alone is not treated as evidence that a shadowed row won. -/
inductive Lookup (query : BlockId) (trace : Trace) : Option BasicBlock → Option BasicBlock → Prop where
  | missing : Lookup query trace none none
  | kept (block : BasicBlock) (notSuspend : isSuspend block.terminator = false) :
      Lookup query trace (some block) (some block)
  | expanded (block : BasicBlock) (names : Names)
      (recorded : (query, names) ∈ trace) (suspend : isSuspend block.terminator = true) :
      Lookup query trace (some block) (some (expandedEntry names block))

theorem Lookup.extend {query : BlockId} {trace : Trace} {source target : Option BasicBlock}
    (view : Lookup query trace source target) (row : BlockId × Names) :
    Lookup query (row :: trace) source target := by
  cases view with
  | missing => exact .missing
  | kept block notSuspend => exact .kept block notSuspend
  | expanded block names recorded suspend =>
    exact .expanded block names (List.mem_cons_of_mem row recorded) suspend

theorem lookup {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (query : BlockId) : Lookup query trace (cfgOf source query) (cfgOf target query) := by
  induction plan with
  | nil => exact .missing
  | keep _ _ id block notSuspend _ _ _ _ ih =>
    cases found : id == query with
    | false =>
      simpa only [cfgOf, List.find?, found, Bool.false_eq_true, if_false, Option.map] using ih
    | true =>
      simp only [cfgOf, List.find?, found, if_true, Option.map]
      exact .kept block notSuspend
  | expand _ _ _ id block suspend names _ _ _ trace _ ih =>
    cases found : id == query with
    | false =>
      simpa only [cfgOf, List.find?, found, Bool.false_eq_true, if_false, Option.map] using
        ih.extend (id, Names.ofTriple names)
    | true =>
      simp only [cfgOf, List.find?, found, if_true, Option.map]
      have same : id = query := of_decide_eq_true found
      apply Lookup.expanded block (Names.ofTriple names)
      · rw [← same]; exact (trustIrListMemConsSelf _ _)
      · exact suspend

theorem lookup_none_iff {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (query : BlockId) : cfgOf source query = none ↔ cfgOf target query = none := by
  have view := lookup plan query
  generalize sourceEq : cfgOf source query = sourceOption at view ⊢
  generalize targetEq : cfgOf target query = targetOption at view ⊢
  cases view <;> simp only [Option.some_ne_none, not_false_eq_true, iff_self]

/-- The source found block is the first matching occurrence. The target
    equation exposes its actual Names in the suspend case without any
    source-success, resource or unique-label premise. -/
theorem lookup_some {domain : Nat} {used : List Nat} {before after : Cursor domain used}
    {source target : Rows} {trace : Trace} (plan : Plans before after source target trace)
    (query : BlockId) (block : BasicBlock) (found : cfgOf source query = some block) :
    (isSuspend block.terminator = false ∧ cfgOf target query = some block) ∨
      ∃ names : Names, (query, names) ∈ trace ∧ isSuspend block.terminator = true ∧
        cfgOf target query = some (expandedEntry names block) := by
  have view := lookup plan query
  rw [found] at view
  generalize targetEq : cfgOf target query = targetOption at view ⊢
  cases view with
  | kept block notSuspend => exact .inl ⟨notSuspend, rfl⟩
  | expanded block names recorded suspend => exact .inr ⟨names, recorded, suspend, rfl⟩

theorem planAllBlocks_ready_params (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (query : BlockId) :
    (cfgOf blocks query).map BasicBlock.params =
      (cfgOf (planAllBlocks blocks).rows query).map BasicBlock.params :=
  cfg_params (lowerRows_ready GenericCoroFreshIds.u32Domain blocks ready) query

theorem planAllBlocks_ready_padViews (blocks : Rows) (ready : Ready (planAllBlocks blocks)) :
    PadViews.PadViewsAgree (cfgOf blocks) (cfgOf (planAllBlocks blocks).rows) :=
  padViews (lowerRows_ready GenericCoroFreshIds.u32Domain blocks ready)

theorem planAllBlocks_ready_lookup (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (query : BlockId) :
    Lookup query (planAllBlocks blocks).trace (cfgOf blocks query)
      (cfgOf (planAllBlocks blocks).rows query) :=
  lookup (lowerRows_ready GenericCoroFreshIds.u32Domain blocks ready) query

namespace Controls

/-- These are concrete ordered-row/planner controls. They carry no Rust
    validation, byte-codec or evaluator-correctness admission claim. -/
def cleanupSuspend : BasicBlock :=
  { params := [(⟨0⟩, .Ptr), (⟨1⟩, .I64)]
    body := [.LandingPad true []]
    terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩ }

def shadow : BasicBlock :=
  { params := [(⟨9⟩, .I32)], body := [.LandingPad false [17]], terminator := .Return [⟨9⟩] }

def emptySuspend : BasicBlock :=
  { params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 23 ⟨1⟩ }

def duplicateRows : Rows := [(⟨7⟩, cleanupSuspend), (⟨7⟩, shadow), (⟨8⟩, emptySuspend)]

private theorem duplicateReady : Ready (planAllBlocks duplicateRows) := True.intro

private theorem duplicatePlan :
    Plans (prepare GenericCoroFreshIds.u32Domain (graphReservations duplicateRows))
      (planAllBlocks duplicateRows).cursor duplicateRows
      (planAllBlocks duplicateRows).rows (planAllBlocks duplicateRows).trace :=
  lowerRows_ready GenericCoroFreshIds.u32Domain duplicateRows duplicateReady

theorem duplicate_first_match_parameters :
    (cfgOf (planAllBlocks duplicateRows).rows ⟨7⟩).map BasicBlock.params =
      some [(⟨0⟩, .Ptr), (⟨1⟩, .I64)] :=
  (cfg_params duplicatePlan ⟨7⟩).symm.trans rfl

theorem duplicate_first_match_pad :
    PadViews.padView (cfgOf (planAllBlocks duplicateRows).rows) ⟨7⟩ = some (some (true, [])) :=
  (padViews duplicatePlan ⟨7⟩).symm.trans rfl

theorem duplicate_first_match_actual_names :
    cfgOf (planAllBlocks duplicateRows).rows ⟨7⟩ =
      some (expandedEntry ⟨⟨2⟩, ⟨3⟩, ⟨4⟩⟩ cleanupSuspend) := rfl

def keptFirstRows : Rows := [(⟨7⟩, shadow), (⟨7⟩, cleanupSuspend)]

private theorem keptFirstReady : Ready (planAllBlocks keptFirstRows) := True.intro

/-- The later occurrence really is expanded with names, but its trace row
    does not make it the first-match block returned by cfgOf. -/
theorem retained_first_row_shadows_later_expansion :
    cfgOf (planAllBlocks keptFirstRows).rows ⟨7⟩ = some shadow ∧
      traceObservation (planAllBlocks keptFirstRows).trace = [(7, [2, 3, 4])] := ⟨rfl, rfl⟩

theorem retained_first_row_lookup_contract :
    Lookup ⟨7⟩ (planAllBlocks keptFirstRows).trace
      (some shadow) (some shadow) :=
  planAllBlocks_ready_lookup keptFirstRows keptFirstReady ⟨7⟩

theorem missing_block_stays_absent : cfgOf (planAllBlocks duplicateRows).rows ⟨42⟩ = none :=
  (lookup_none_iff duplicatePlan ⟨42⟩).mp rfl

theorem empty_body_present_nonpad_stays_distinct_from_absence :
    PadViews.padView (cfgOf (planAllBlocks duplicateRows).rows) ⟨8⟩ = some none ∧
      PadViews.padView (cfgOf (planAllBlocks duplicateRows).rows) ⟨42⟩ = none :=
  ⟨(padViews duplicatePlan ⟨8⟩).symm.trans rfl, (padViews duplicatePlan ⟨42⟩).symm.trans rfl⟩

theorem present_nonpad_is_not_missing :
    PadViews.padView (cfgOf (planAllBlocks duplicateRows).rows) ⟨8⟩ ≠
      PadViews.padView (cfgOf (planAllBlocks duplicateRows).rows) ⟨42⟩ := by
  obtain ⟨present, missing⟩ := empty_body_present_nonpad_stays_distinct_from_absence
  rw [present, missing]
  intro impossible
  cases impossible

theorem actual_cleanup_entry_keeps_selector :
    (Sem.run (semEnterPad (cfgOf (planAllBlocks duplicateRows).rows) 7 ⟨7⟩)
      PadViews.Controls.raised).map (fun result => result.2.inHand) = .ok (some (7, ⟨0⟩, 0)) := by
  rw [← semEnterPad_eq duplicatePlan 7 ⟨7⟩]
  rfl

theorem empty_graph_views :
    PadViews.PadViewsAgree (cfgOf []) (cfgOf (planAllBlocks []).rows) :=
  planAllBlocks_ready_padViews [] True.intro

theorem empty_graph_lookup :
    Lookup ⟨0⟩ (planAllBlocks []).trace none none :=
  planAllBlocks_ready_lookup [] True.intro ⟨0⟩

end Controls

end TrustIr.GenericCoroAllBlocksViews
