-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYValueProps

namespace TrustIr.TrustIrExpr

private theorem mem_append_iff (name : String) (a b : List String) :
    name ∈ a ++ b ↔ name ∈ a ∨ name ∈ b := by
  constructor
  · induction a with
    | nil => exact fun h => Or.inr h
    | cons head tail ih =>
      intro h
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h =>
        cases ih h with
        | inl h => exact Or.inl (List.Mem.tail _ h)
        | inr h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact trustIrListMemAppendLeft b h
    | inr h => exact trustIrListMemAppendRight a h

private theorem mem_singleton_iff (name value : String) : name ∈ [value] ↔ name = value := by
  constructor
  · intro h
    cases h with
    | head => rfl
    | tail _ h => cases h
  · intro h
    subst name
    exact List.Mem.head _

private theorem variable_residue_congr (width : Nat) (left right : SMTEnv) (name : String)
    (agree : left name % (2 : Int) ^ width = right name % (2 : Int) ^ width) :
    (.var name width : TrustIrExpr).evalAt left width =
      (.var name width : TrustIrExpr).evalAt right width := by
  change ((left name % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width =
    ((right name % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width
  rw [agree]

/-- Sorted evaluation depends on residues of the occurring variables, rather
than equality of their arbitrary integer representatives. -/
theorem SMTSorted.eval_residue_congr {width : Nat} {expr : TrustIrExpr} {sort : SMTSort}
    (typed : SMTSorted width expr sort) (left right : SMTEnv)
    (agree : ∀ name ∈ expr.variables,
      left name % (2 : Int) ^ width = right name % (2 : Int) ^ width) :
    expr.evalAt left width = expr.evalAt right width := by
  induction typed with
  | var name _positive =>
    exact variable_residue_congr width left right name (agree name (List.Mem.head _))
  | _ => simp_all [variables, TrustIrExpr.evalAt, mem_append_iff, mem_singleton_iff,
      or_imp, forall_and]

/-- Actual declared bindings need only agree modulo the request's word size. -/
theorem toSMTRequest_eval_residue_congr (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request)
    (left right : SMTEnv)
    (agree : ∀ name ∈ request.bindings,
      left name % (2 : Int) ^ request.width = right name % (2 : Int) ^ request.width) :
    expr.evalAt left request.width = expr.evalAt right request.width := by
  have typed := toSMTRequest_sorted expr width request built
  have sameWidth := (toSMTRequest_metadata expr width request built).1
  rw [sameWidth] at agree ⊢
  apply typed.eval_residue_congr left right
  intro name member
  exact agree name ((toSMTRequest_binding_iff expr width request built name).mpr member)

/-- Finite declared-word models, extended by zero outside the emitted inventory. -/
def SMTRequest.IsModel (request : SMTRequest) (env : SMTEnv) : Prop :=
  (∀ name, 0 ≤ env name ∧ env name < (2 : Int) ^ request.width) ∧
  (∀ name, name ∉ request.bindings → env name = 0)

/-- Project arbitrary integer assignments to the actual finite declaration domain. -/
def SMTRequest.normalizeEnv (request : SMTRequest) (env : SMTEnv) : SMTEnv :=
  fun name => if name ∈ request.bindings then env name % (2 : Int) ^ request.width else 0

/-- Projection supplies its own range and off-inventory value, without model premises. -/
theorem SMTRequest.normalizeEnv_isModel (request : SMTRequest) (env : SMTEnv) :
    request.IsModel (request.normalizeEnv env) := by
  have positive : (0 : Int) < 2 ^ request.width := by
    have power : (2 : Int) ^ request.width = ((2 ^ request.width : Nat) : Int) :=
      (Int.natCast_pow 2 request.width).symm
    rw [power]
    trustIrCompilerProof
      { exact Int.ofNat_pos.mpr (Nat.two_pow_pos request.width) }
      { have positiveNat := Nat.two_pow_pos request.width; omega }
  constructor
  · intro name
    simp only [normalizeEnv]
    split
    · exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ positive⟩
    · exact ⟨Int.le_refl _, positive⟩
  · intro name absent
    simp [normalizeEnv, absent]

/-- The finite models are exactly the fixed points of the projection. -/
theorem SMTRequest.normalizeEnv_eq_iff (request : SMTRequest) (env : SMTEnv) :
    request.normalizeEnv env = env ↔ request.IsModel env := by
  constructor
  · intro fixed
    have model := request.normalizeEnv_isModel env
    rwa [fixed] at model
  · rintro ⟨range, outside⟩
    funext name
    simp only [normalizeEnv]
    split
    · exact Int.emod_eq_of_lt (range name).1 (range name).2
    · rename_i absent
      exact (outside name absent).symm

/-- Projection is idempotent on the entire environment, including undeclared names. -/
theorem SMTRequest.normalizeEnv_idempotent (request : SMTRequest) (env : SMTEnv) :
    request.normalizeEnv (request.normalizeEnv env) = request.normalizeEnv env :=
  (request.normalizeEnv_eq_iff _).mpr (request.normalizeEnv_isModel env)

/-- Normalization retains the complete evaluation of a successfully emitted request. -/
theorem toSMTRequest_normalizeEnv_eval (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request) (env : SMTEnv) :
    expr.evalAt (request.normalizeEnv env) request.width = expr.evalAt env request.width := by
  apply toSMTRequest_eval_residue_congr expr width request built
  intro name member
  simp only [SMTRequest.normalizeEnv, if_pos member, Int.emod_emod]

/-- Universal zero evaluation is equivalent on arbitrary integers and finite models. -/
theorem toSMTRequest_unsat_iff_models (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request) :
    (∀ env : SMTEnv, expr.evalAt env request.width = 0) ↔
    (∀ env : SMTEnv, request.IsModel env → expr.evalAt env request.width = 0) := by
  constructor
  · exact fun all env _ => all env
  · intro models env
    have zero := models (request.normalizeEnv env) (request.normalizeEnv_isModel env)
    rwa [toSMTRequest_normalizeEnv_eval expr width request built env] at zero

/-- Any integer countermodel has a finite declared-word countermodel, and conversely. -/
theorem toSMTRequest_sat_iff_models (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request) :
    (∃ env : SMTEnv, expr.evalAt env request.width ≠ 0) ↔
    (∃ env : SMTEnv, request.IsModel env ∧ expr.evalAt env request.width ≠ 0) := by
  constructor
  · rintro ⟨env, nonzero⟩
    refine ⟨request.normalizeEnv env, request.normalizeEnv_isModel env, ?_⟩
    rwa [toSMTRequest_normalizeEnv_eval expr width request built env]
  · rintro ⟨env, _, nonzero⟩
    exact ⟨env, nonzero⟩

end TrustIr.TrustIrExpr


/-- info: 'TrustIr.TrustIrExpr.SMTSorted.eval_residue_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSorted.eval_residue_congr

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_eval_residue_congr == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTRequest.normalizeEnv_isModel == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTRequest.normalizeEnv_eq_iff == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTRequest.normalizeEnv_idempotent == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_normalizeEnv_eval == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_unsat_iff_models == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_sat_iff_models == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

