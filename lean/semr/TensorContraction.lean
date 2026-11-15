/-
  The integer matrix multiply as a tensor contraction equals its loop nest,
  for every shape.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>

  `TensorStatement` is the claim trust-ir's
  `tensor_contraction_equals_loop_nest` test has the Clean kernel check: for
  every pointer width, every integer element type and every shape `m × k` by
  `k × n`, SemR's `TensorContract` of two well-formed integer tensors over
  `lhs` axis 1 and `rhs` axis 0 (no batch axes; `evalContract`, the helper
  SemR's `Step` rule and its executable share) is the `m × n` tensor whose
  elements the textbook loop nest `matmulLoopNest` computes, or the `usize`
  refusal when `m * n` elements do not fit. `tensor_matmul_eq_loopNest`
  proves it. `ForgedTensorStatement` is the same claim with the result's
  extents transposed; `forged_is_false` refutes it on a `1 × 0` by `0 × 2`
  product, so a kernel that accepted the proof of `TensorStatement` as a proof
  of it would have accepted a false statement (the test's negative control).

  Rules of the file are `SemR.lean`'s: it imports only `SemR` (no `Std`), and
  has no `native_decide`, `partial def`, `sorry`, `axiom`,
  `implemented_by` or `extern`.
-/
import SemR

namespace SemR

/-- The loop nest: for each row `i < m` and column `j < n`, the accumulator
    starts at `0` and adds `a[i][p] * b[p][j]` for each `p < k`, the product
    and the sum each wrapping at width `w`; the finished cell is pushed onto
    the output. `a` is `m × k` and `b` is `k × n`, both row-major. -/
def matmulLoopNest (w m k n : Nat) (a b : List Nat) : List Nat :=
  (List.range m).foldl (fun out i =>
    (List.range n).foldl (fun out j =>
      out ++ [(List.range k).foldl (fun acc p =>
        (acc + (getN a (i * k + p) * getN b (p * n + j)) % modulus w) % modulus w) 0]) out) []

/-- For every pointer width `pb`, integer element type `t`, shape `m × k` by
    `k × n` and pair of well-formed operands (extents below `2^pb`, `m * k`
    and `k * n` residues, each in range at `t`'s width), the contraction of
    `a`'s axis 1 with `b`'s axis 0 is the loop nest's `m × n` tensor, or the
    `usize` refusal when its `m * n` elements do not fit. -/
def TensorStatement : Prop :=
  ∀ (pb : Nat) (t : IntTy) (m k n : Nat) (a b : List Nat),
    m < modulus pb → k < modulus pb → n < modulus pb →
    a.length = m * k → b.length = k * n →
    (∀ x, x ∈ a → x < modulus (t.bits pb)) → (∀ x, x ∈ b → x < modulus (t.bits pb)) →
    evalContract pb (.tensor t 2) [] [(1, 0)] (.tensor t [m, k] a) (.tensor t [k, n] b) =
      if m * n < modulus pb then
        .ok (.tensor t [m, n] (matmulLoopNest (t.bits pb) m k n a b))
      else ubR "tensor contraction: the result has more elements than usize holds"

/-- The forged twin: `TensorStatement` with the result's extents transposed. -/
def ForgedTensorStatement : Prop :=
  ∀ (pb : Nat) (t : IntTy) (m k n : Nat) (a b : List Nat),
    m < modulus pb → k < modulus pb → n < modulus pb →
    a.length = m * k → b.length = k * n →
    (∀ x, x ∈ a → x < modulus (t.bits pb)) → (∀ x, x ∈ b → x < modulus (t.bits pb)) →
    evalContract pb (.tensor t 2) [] [(1, 0)] (.tensor t [m, k] a) (.tensor t [k, n] b) =
      if m * n < modulus pb then
        .ok (.tensor t [n, m] (matmulLoopNest (t.bits pb) m k n a b))
      else ubR "tensor contraction: the result has more elements than usize holds"

/-! ### List lemmas -/

theorem upTo_eq_range (n : Nat) : upTo n = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [upTo, ih, List.range_succ]

theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

/-- Pushing one cell per element is appending the mapped list. -/
theorem foldl_push {α β : Type} (f : β → α) (l : List β) (out : List α) :
    l.foldl (fun out x => out ++ [f x]) out = out ++ l.map f := by
  induction l generalizing out with
  | nil => rw [List.foldl_nil, List.map_nil, List.append_nil]
  | cons x xs ih => rw [List.foldl_cons, ih, List.map_cons, List.append_assoc]; rfl

/-- Appending one block per element is appending the flat-mapped list. -/
theorem foldl_append_eq_flatMap {α β : Type} (g : β → List α) (l : List β) (out : List α) :
    l.foldl (fun out x => out ++ g x) out = out ++ l.flatMap g := by
  induction l generalizing out with
  | nil => rw [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons x xs ih => rw [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]

theorem multiIdx_one (n : Nat) : multiIdx [n] = (upTo n).map (fun j => [j]) := by
  rw [multiIdx]
  exact flatMap_singleton_eq_map (fun j => [j]) (upTo n)

theorem multiIdx_two (m n : Nat) :
    multiIdx [m, n] = (upTo m).flatMap (fun i => (upTo n).map (fun j => [i, j])) := by
  rw [multiIdx, multiIdx_one]
  congr 1
  funext i
  rw [List.map_map]
  rfl

/-! ### The contraction's elements on a matrix multiply -/

/-- The elements with the shape bookkeeping evaluated: the result's
    multi-index `o` is `[i, j]`, the contracted one `c` is `[p]`, `a` is read
    at `i * k + p` and `b` at `p * n + j` (before the `* 1` / `+ 0` of the
    row-major offsets are cancelled). -/
theorem contractElems_matmul (w m k n : Nat) (a b : List Nat) :
    contractElems w [] [(1, 0)] [m, k] [k, n] a b =
      (multiIdx [m, n]).map (fun o =>
        (multiIdx [k]).foldl (fun acc c =>
          macR w acc (getN a (getN o 0 * (k * 1) + (getN c 0 * 1 + 0)))
            (getN b (getN c 0 * (n * 1) + (getN o (1 + 0) * 1 + 0)))) 0) := by
  rfl

theorem contractElems_eq_loopNest (w m k n : Nat) (a b : List Nat) :
    contractElems w [] [(1, 0)] [m, k] [k, n] a b = matmulLoopNest w m k n a b := by
  rw [contractElems_matmul, multiIdx_two, multiIdx_one, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, List.foldl_map, getN, Nat.mul_one, Nat.add_zero]
  unfold matmulLoopNest
  simp only [foldl_push, foldl_append_eq_flatMap, List.nil_append, upTo_eq_range, macR]

/-! ### The checks pass on well-formed operands -/

theorem all_lt_of_forall (l : List Nat) (bound : Nat) (h : ∀ x, x ∈ l → x < bound) :
    l.all (fun x => decide (x < bound)) = true := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [List.all_cons, decide_eq_true (h y (List.mem_cons_self ..)),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem tensorWF_matrix (pb : Nat) (t : IntTy) (r c : Nat) (xs : List Nat)
    (hr : r < modulus pb) (hc : c < modulus pb) (hl : xs.length = r * c)
    (hx : ∀ x, x ∈ xs → x < modulus (t.bits pb)) :
    tensorWF pb t [r, c] xs = true := by
  unfold tensorWF
  rw [all_lt_of_forall xs _ hx]
  simp only [List.all_cons, List.all_nil, decide_eq_true hr, decide_eq_true hc, prodL,
    Nat.mul_one, hl, beq_self_eq_true, Bool.and_self]

/-- The contraction of two tensors, its operands' shape read off. -/
theorem evalContract_matmul (pb : Nat) (t : IntTy) (m k n : Nat) (a b : List Nat) :
    evalContract pb (.tensor t 2) [] [(1, 0)] (.tensor t [m, k] a) (.tensor t [k, n] b) =
      if (!(t.code == t.code && t.code == t.code)) = true then
        tyR "TypeError: tensor contraction: an operand's element type is not the result's"
      else if (!contractAxesOk [] [(1, 0)] 2 2) = true then
        tyR "TypeError: tensor contraction: an axis pair is out of range or names an axis twice"
      else if (2 != 0 + (2 - 0 - 1) + (2 - 0 - 1)) = true then
        tyR "TypeError: tensor contraction: the result rank is not the batch and free axes"
      else if (!tensorWF pb t [m, k] a) = true then
        tyR "TypeError: tensor contraction: the left operand is not a well-formed tensor"
      else if (!tensorWF pb t [k, n] b) = true then
        tyR "TypeError: tensor contraction: the right operand is not a well-formed tensor"
      else if (!(k == k && true)) = true then
        ubR "tensor contraction: paired axes have different extents"
      else if modulus pb ≤ m * (n * 1) then
        ubR "tensor contraction: the result has more elements than usize holds"
      else
        .ok (.tensor t [m, n] (contractElems (t.bits pb) [] [(1, 0)] [m, k] [k, n] a b)) := by
  rfl

/-- The claim: the contraction is the loop nest, for every shape. -/
theorem tensor_matmul_eq_loopNest : TensorStatement := by
  intro pb t m k n a b hm hk hn ha hb hxa hxb
  rw [evalContract_matmul, tensorWF_matrix pb t m k a hm hk ha hxa,
    tensorWF_matrix pb t k n b hk hn hb hxb, contractElems_eq_loopNest]
  have hax : contractAxesOk [] [(1, 0)] 2 2 = true := rfl
  rw [hax]
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    Nat.mul_one]
  have hrank : (2 != 0 + (2 - 0 - 1) + (2 - 0 - 1)) = false := rfl
  rw [hrank]
  simp only [Bool.false_eq_true, if_false]
  by_cases h : m * n < modulus pb
  · rw [if_neg (Nat.not_le_of_gt h), if_pos h]
  · rw [if_pos (Nat.le_of_not_gt h), if_neg h]

/-- The forged twin is false: a `1 × 0` by `0 × 2` product is `1 × 2`, not
    `2 × 1`. -/
theorem forged_is_false : ¬ ForgedTensorStatement := by
  intro h
  have hf := h 8 .u8 1 0 2 [] [] (by decide) (by decide) (by decide) rfl rfl
    (fun _ hx => nomatch hx) (fun _ hx => nomatch hx)
  rw [tensor_matmul_eq_loopNest 8 .u8 1 0 2 [] [] (by decide) (by decide) (by decide) rfl rfl
    (fun _ hx => nomatch hx) (fun _ hx => nomatch hx)] at hf
  have hlt : 1 * 2 < modulus 8 := by decide
  rw [if_pos hlt, if_pos hlt] at hf
  cases hf

end SemR
