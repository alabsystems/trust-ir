-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroProps
import TrustIr.Proofs.GenericCoroPadViews

namespace TrustIr.GenericCoro.GraphViews

/-- The existing suspend expansion retains the exact unwind observation,
    including an empty original body whose generated first node is a Const. -/
theorem expandedEntry_pad (names : Names) (block : BasicBlock) :
    (expandedEntry names block).body.head?.bind Inst.padClauses =
      block.body.head?.bind Inst.padClauses := by
  cases block with
  | mk params body dests term termDests =>
    cases body <;> cases term <;> rfl

/-- Continuations observe the original block parameters; unwind entry also
    observes its original pad clauses. The complete body may change. -/
def blockInterface (block : BasicBlock) :
    List (ValueId × Ty) × Option (Bool × List Nat) :=
  (block.params, block.body.head?.bind Inst.padClauses)

theorem expandedEntry_interface (names : Names) (block : BasicBlock) :
    blockInterface (expandedEntry names block) = blockInterface block := by
  simp only [blockInterface, expandedEntry_params, expandedEntry_pad]

/-- Projecting a finite graph before its first-match lookup preserves the
    exact observation. Duplicate block identifiers retain their order. -/
theorem cfgOf_observation {α : Type} (observe : BasicBlock → α)
    (blocks : List (BlockId × BasicBlock)) (query : BlockId) :
    (cfgOf blocks query).map observe =
      ((blocks.map (fun row => (row.1, observe row.2))).find?
        (fun row => row.1 == query)).map Prod.snd := by
  induction blocks with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases found : id == query <;>
      simp only [cfgOf, List.map_cons, List.find?, found, Bool.false_eq_true,
        if_false, if_true, Option.map]
    all_goals exact ih

/-- A source-derived traversal can establish equality of projected rows
    without requiring CFG identity or choosing observations of unvisited keys. -/
theorem cfgOf_observation_of_rows {α : Type} (observe : BasicBlock → α)
    (source target : List (BlockId × BasicBlock))
    (rows : source.map (fun row => (row.1, observe row.2)) =
      target.map (fun row => (row.1, observe row.2))) (query : BlockId) :
    (cfgOf source query).map observe = (cfgOf target query).map observe := by
  rw [cfgOf_observation, cfgOf_observation, rows]

theorem expandFirstEntry_observation {α : Type} (observe : BasicBlock → α)
    (names : Names) (entry : BlockId)
    (stable : ∀ block, observe (expandedEntry names block) = observe block)
    (blocks : List (BlockId × BasicBlock)) (query : BlockId) :
    (cfgOf (expandFirstEntry names entry blocks) query).map observe =
      (cfgOf blocks query).map observe := by
  induction blocks with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases expanded : id == entry <;> cases found : id == query <;>
      simp only [expandFirstEntry, expanded, Bool.false_eq_true, if_false, if_true,
        cfgOf, List.find?, found, Option.map]
    all_goals first | exact ih | exact congrArg some (stable block)

/-- Actual selected-entry expansion preserves both continuation and pad
    observations at every lookup, including duplicate and missing block ids. -/
theorem expandedGraph_interface (names : Names)
    (blocks : List (BlockId × BasicBlock)) (entry query : BlockId) :
    (cfgOf (expandedGraph names blocks entry) query).map blockInterface =
      (cfgOf blocks query).map blockInterface :=
  expandFirstEntry_observation blockInterface names entry
    (expandedEntry_interface names) blocks query

theorem expandedGraph_padViews (names : Names)
    (blocks : List (BlockId × BasicBlock)) (entry : BlockId) :
    PadViews.PadViewsAgree (cfgOf blocks) (cfgOf (expandedGraph names blocks entry)) := by
  intro query
  exact (expandFirstEntry_observation (fun block => block.body.head?.bind Inst.padClauses)
    names entry (expandedEntry_pad names) blocks query).symm

theorem expandedGraph_params (names : Names)
    (blocks : List (BlockId × BasicBlock)) (entry query : BlockId) :
    (cfgOf (expandedGraph names blocks entry) query).map BasicBlock.params =
      (cfgOf blocks query).map BasicBlock.params :=
  expandFirstEntry_observation BasicBlock.params names entry
    (expandedEntry_params names) blocks query

/-- Arbitrary whole-graph traversal needs only retain the actual ordered
    interface rows. This is a local observation fact, not a pass theorem. -/
theorem padViews_of_interface_rows (source target : List (BlockId × BasicBlock))
    (rows : source.map (fun row => (row.1, blockInterface row.2)) =
      target.map (fun row => (row.1, blockInterface row.2))) :
    PadViews.PadViewsAgree (cfgOf source) (cfgOf target) := by
  intro query
  have interfaces := cfgOf_observation_of_rows blockInterface source target rows query
  have projected := congrArg (Option.map Prod.snd) interfaces
  simpa only [PadViews.padView, blockInterface, Option.map_map] using projected

theorem params_of_interface_rows (source target : List (BlockId × BasicBlock))
    (rows : source.map (fun row => (row.1, blockInterface row.2)) =
      target.map (fun row => (row.1, blockInterface row.2))) (query : BlockId) :
    (cfgOf source query).map BasicBlock.params = (cfgOf target query).map BasicBlock.params := by
  have interfaces := cfgOf_observation_of_rows blockInterface source target rows query
  have projected := congrArg (Option.map Prod.fst) interfaces
  simpa only [blockInterface, Option.map_map] using projected

end TrustIr.GenericCoro.GraphViews

#trustIrAxiomsExact TrustIr.GenericCoro.GraphViews.blockInterface == []
#trustIrAxiomsExact TrustIr.GenericCoro.GraphViews.expandedEntry_pad == []
