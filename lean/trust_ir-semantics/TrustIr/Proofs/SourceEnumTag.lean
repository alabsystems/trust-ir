-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutSession

namespace TrustIr.SourceLayout

private def minStep (acc : Option Int) (value : Int) : Option Int :=
  some (match acc with | some first => if value < first then value else first | none => value)
private def maxStep (acc : Option Int) (value : Int) : Option Int :=
  some (match acc with | some first => if first < value then value else first | none => value)

private theorem fold_min_bounds (first : Int) (rest : List Int) :
    ∃ lower, rest.foldl minStep (some first) = some lower ∧ lower ∈ first :: rest ∧
      ∀ value ∈ first :: rest, lower ≤ value := by
  induction rest generalizing first with
  | nil =>
    refine ⟨first,rfl,.head _,?_⟩
    intro value member
    have same : value = first := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
    rw [same]
    exact Int.le_refl _
  | cons next rest ih =>
    rw [List.foldl_cons]
    change ∃ lower, rest.foldl minStep (some (if next < first then next else first)) = some lower ∧
      lower ∈ first :: next :: rest ∧ ∀ value ∈ first :: next :: rest, lower ≤ value
    by_cases less : next < first
    · simp only [less,ite_true]
      obtain ⟨lower,run,member,bounds⟩ := ih next
      refine ⟨lower,run,List.mem_cons_of_mem _ member,?_⟩
      intro value included
      rcases List.mem_cons.mp included with same | included
      · rw [same]; have held := bounds next (.head _); omega
      · exact bounds value included
    · simp only [less,ite_false]
      obtain ⟨lower,run,member,bounds⟩ := ih first
      refine ⟨lower,run,?_,?_⟩
      · rcases List.mem_cons.mp member with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
      · intro value included
        rcases List.mem_cons.mp included with same | included
        · rw [same]; exact bounds first (.head _)
        · rcases List.mem_cons.mp included with same | included
          · rw [same]; have held := bounds first (.head _); omega
          · exact bounds value (.tail _ included)

private theorem fold_max_bounds (first : Int) (rest : List Int) :
    ∃ upper, rest.foldl maxStep (some first) = some upper ∧ upper ∈ first :: rest ∧
      ∀ value ∈ first :: rest, value ≤ upper := by
  induction rest generalizing first with
  | nil =>
    refine ⟨first,rfl,.head _,?_⟩
    intro value member
    have same : value = first := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
    rw [same]
    exact Int.le_refl _
  | cons next rest ih =>
    rw [List.foldl_cons]
    change ∃ upper, rest.foldl maxStep (some (if first < next then next else first)) = some upper ∧
      upper ∈ first :: next :: rest ∧ ∀ value ∈ first :: next :: rest, value ≤ upper
    by_cases less : first < next
    · simp only [less,ite_true]
      obtain ⟨upper,run,member,bounds⟩ := ih next
      refine ⟨upper,run,List.mem_cons_of_mem _ member,?_⟩
      intro value included
      rcases List.mem_cons.mp included with same | included
      · rw [same]; have held := bounds next (.head _); omega
      · exact bounds value included
    · simp only [less,ite_false]
      obtain ⟨upper,run,member,bounds⟩ := ih first
      refine ⟨upper,run,?_,?_⟩
      · rcases List.mem_cons.mp member with same | member
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
      · intro value included
        rcases List.mem_cons.mp included with same | included
        · rw [same]; exact bounds first (.head _)
        · rcases List.mem_cons.mp included with same | included
          · rw [same]; have held := bounds first (.head _); omega
          · exact bounds value (.tail _ included)

private theorem fits_between (tag : EnumTagRepr) (lower value upper : Int)
    (lowFits : tag.fits lower = true) (highFits : tag.fits upper = true)
    (low : lower ≤ value) (high : value ≤ upper) : tag.fits value = true := by
  cases tag <;> simp only [EnumTagRepr.fits, Bool.and_eq_true, decide_eq_true_eq] at * <;> omega

private theorem all_fits_extremes (values : List Int) (lower upper : Int)
    (lowMember : lower ∈ values) (highMember : upper ∈ values)
    (low : ∀ value ∈ values, lower ≤ value) (high : ∀ value ∈ values, value ≤ upper)
    (tag : EnumTagRepr) : values.all tag.fits = (tag.fits lower && tag.fits upper) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro all; exact ⟨all lower lowMember,all upper highMember⟩
  · intro ends value member
    exact fits_between tag lower value upper ends.1 ends.2 (low value member) (high value member)

/-- The two real canonical-tag algorithms agree, including default min/max
    selection, explicit representations and all invalid/empty cases. -/
theorem canonicalTag_eval (definition : EnumDef) :
    canonicalTag definition = enumCanonicalTagRepr definition := by
  unfold canonicalTag enumCanonicalTagRepr
  rw [← discriminants_eval]
  cases empty : definition.variants.isEmpty <;> simp only [empty, Bool.false_eq_true, ite_false, ite_true]
  · cases numbered : discriminants definition with
    | none => rfl
    | some values =>
      simp only [Bind.bind,Option.bind]
      have fitting : ∀ tag, values.all (tagFits tag) = values.all tag.fits := by
        intro tag; congr 1; funext value; exact tagFits_eval tag value
      cases authored : definition.tagRepr with
      | some tag => simp only [authored,fitting]
      | none =>
        simp only [authored]
        have length := (discriminants_facts definition values numbered).1
        cases values with
        | nil =>
          have gone : definition.variants = [] := List.eq_nil_of_length_eq_zero length.symm
          rw [gone] at empty
          change true = false at empty
          cases empty
        | cons first rest =>
          obtain ⟨lower,minRun,minMember,minBounds⟩ := fold_min_bounds first rest
          obtain ⟨upper,maxRun,maxMember,maxBounds⟩ := fold_max_bounds first rest
          change rest.foldl minStep (some first) = some lower at minRun
          change rest.foldl maxStep (some first) = some upper at maxRun
          have nonnegative : ((first :: rest).all (fun value => decide (0 ≤ value))) = decide (0 ≤ lower) := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true,decide_eq_true_eq]
            constructor
            · intro all; exact all lower minMember
            · intro held value member; have bound := minBounds value member; omega
          have predicates : (fun tag => (first :: rest).all (tagFits tag)) =
              (fun tag => tag.fits lower && tag.fits upper) := by
            funext tag
            rw [fitting tag]
            exact all_fits_extremes _ lower upper minMember maxMember minBounds maxBounds tag
          rw [nonnegative,predicates]
          change _ = (rest.foldl minStep (some first)).bind (fun min =>
            (rest.foldl maxStep (some first)).bind (fun max => enumSmallestTagRepr min max))
          rw [minRun,maxRun]
          simp only [Option.bind,enumSmallestTagRepr,decide_eq_true_eq]
  · rfl

end TrustIr.SourceLayout
