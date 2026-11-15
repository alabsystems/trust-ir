-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksPlanner

namespace TrustIr.GenericCoroAllBlocksPlanner
open GenericCoroFreshCursor GenericCoroFreshIds GenericCoro

/-- Every recorded occurrence retains the actual triple's bounds, pairwise
    distinctness and freshness against the original occupied domain. Only
    freshness against the preceding reservation history is forgotten. -/
theorem Plans.traceTriple {domain : Nat} {used : List Nat}
    {before after : Cursor domain used} {source target : Rows} {trace : Trace}
    (plan : Plans before after source target trace) (label : BlockId) (recorded : Names)
    (member : (label, recorded) ∈ trace) :
    ∃ names : Triple domain used, Names.ofTriple names = recorded := by
  induction plan generalizing label recorded with
  | nil _ => cases member
  | keep _ _ _ _ _ _ _ _ _ ih =>
    exact ih label recorded member
  | expand before _ _ _ _ _ names _ _ _ _ _ ih =>
    rcases List.mem_cons.mp member with same | later
    · cases same
      exact ⟨{ names with
        firstUnused := fun occupied => names.firstUnused
          (trustIrListMemAppendRight before.reserved occupied)
        secondUnused := fun occupied => names.secondUnused
          (trustIrListMemAppendRight before.reserved occupied)
        thirdUnused := fun occupied => names.thirdUnused
          (trustIrListMemAppendRight before.reserved occupied) }, rfl⟩
    · exact ih label recorded later

/-- The production all-row planner supplies graph-wide fresh names for
    every recorded occurrence, including non-entry and shadowed rows. This
    consumes the actual ready plan and performs no new reservation. -/
theorem planAllBlocks_traceGraphNames (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (label : BlockId) (recorded : Names)
    (member : (label, recorded) ∈ (planAllBlocks blocks).trace) :
    ∃ names : GraphNames blocks, Names.ofTriple names = recorded :=
  (lowerRows_ready u32Domain blocks ready).traceTriple label recorded member

namespace TraceControls

def entry : BasicBlock :=
  { params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)]
    body := [.Copy .I32 ⟨1⟩]
    bodyResultDests := [[⟨2⟩], [⟨2^32 - 1⟩]]
    terminator := .Br ⟨11⟩ [] }

def suspend : BasicBlock :=
  { params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩ }

/-- Two non-entry occurrences share a label. The original reservation
    census also retains the unused trailing maximum-u32 destination. -/
def sourceRows : Rows := [(⟨0⟩, entry), (⟨11⟩, suspend), (⟨11⟩, suspend)]

theorem actual_duplicate_trace :
    traceObservation (planAllBlocks sourceRows).trace =
      [(11, [3, 4, 5]), (11, [6, 7, 8])] := rfl

theorem actual_first_occurrence_has_original_graph_names :
    ∃ names : GraphNames sourceRows, Names.ofTriple names = ⟨⟨3⟩, ⟨4⟩, ⟨5⟩⟩ := by
  apply planAllBlocks_traceGraphNames sourceRows (by trivial) ⟨11⟩
  exact (trustIrListMemConsSelf _ _)

/-- The second occurrence's witness drops prior-history obligations while
    preserving the same three recorded numbers and all original-source
    freshness, bounds and distinctness fields of GraphNames. -/
theorem actual_later_occurrence_has_original_graph_names :
    ∃ names : GraphNames sourceRows, Names.ofTriple names = ⟨⟨6⟩, ⟨7⟩, ⟨8⟩⟩ := by
  apply planAllBlocks_traceGraphNames sourceRows (by trivial) ⟨11⟩
  exact List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _))

theorem later_witness_retains_recorded_fields :
    ∃ names : GraphNames sourceRows,
      names.first = 6 ∧ names.second = 7 ∧ names.third = 8 := by
  obtain ⟨names, same⟩ := actual_later_occurrence_has_original_graph_names
  exact ⟨names, congrArg (fun value => value.index.index) same,
    congrArg (fun value => value.pointer.index) same,
    congrArg (fun value => value.state.index) same⟩

end TraceControls
end TrustIr.GenericCoroAllBlocksPlanner
