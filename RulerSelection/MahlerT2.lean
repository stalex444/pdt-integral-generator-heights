module

public import Mathlib

/-!
# From a height bound to a `T₂` bound

For reals `y i ≥ 1`, `∑ y i + 1 ≤ ∏ y i + card` (induction from `a + b ≤ a * b + 1` for
`a, b ≥ 1`). Applied to `y i = max 1 (a i)` this gives, with no sign hypothesis on `a`,
`∑ a i + 1 ≤ ∏ max 1 (a i) + card`. Read with `a i = ‖σ i u‖ ^ 2` over the embeddings of a
number field: a height bound `∏ max 1 ‖σ u‖ ≤ B` forces `T₂ u ≤ B ^ 2 + (n - 1)`.
-/

@[expose] public section

namespace RulerSelection

open Finset

/-- For reals at least one, the sum plus one is at most the product plus the number of terms. -/
theorem sum_add_one_le_prod_add_card {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hy : ∀ i ∈ s, 1 ≤ y i) :
    ∑ i ∈ s, y i + 1 ≤ ∏ i ∈ s, y i + (s.card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have hyj : 1 ≤ y j := hy j (Finset.mem_insert_self j s)
    have hys : ∀ i ∈ s, 1 ≤ y i := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have ih' := ih hys
    have hP : 1 ≤ ∏ i ∈ s, y i := Finset.one_le_prod₀ hys
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 hyj) (sub_nonneg.2 hP)]

/-- **Height-to-sum inequality.** For any reals `a i` (no sign hypothesis),
`∑ a i + 1 ≤ ∏ max 1 (a i) + card s`. -/
theorem sum_add_one_le_prod_max_add_card {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ s, a i + 1 ≤ ∏ i ∈ s, max 1 (a i) + (s.card : ℝ) := by
  have h1 := sum_add_one_le_prod_add_card s (fun i => max 1 (a i))
    (fun i _ => le_max_left _ _)
  have h2 : ∑ i ∈ s, a i ≤ ∑ i ∈ s, max 1 (a i) :=
    Finset.sum_le_sum (fun i _ => le_max_right _ _)
  linarith

/-- **The bound in the requested form.** If `∏ max 1 (a i) ≤ C` then
`∑ a i ≤ C + (card s - 1)`. -/
theorem sum_le_of_prod_max_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (C : ℝ)
    (hC : ∏ i ∈ s, max 1 (a i) ≤ C) :
    ∑ i ∈ s, a i ≤ C + ((s.card : ℝ) - 1) := by
  have := sum_add_one_le_prod_max_add_card s a
  linarith

/-- **Complex form (the `T₂` consequence).** If `∏ max 1 ‖z i‖ ≤ B` then
`∑ ‖z i‖ ^ 2 ≤ B ^ 2 + (card s - 1)`. -/
theorem sum_norm_sq_le_of_prod_max_norm_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) (B : ℝ)
    (hB : ∏ i ∈ s, max 1 ‖z i‖ ≤ B) :
    ∑ i ∈ s, ‖z i‖ ^ 2 ≤ B ^ 2 + ((s.card : ℝ) - 1) := by
  have hsq : ∀ i ∈ s, max 1 (‖z i‖ ^ 2) = (max 1 ‖z i‖) ^ 2 := by
    intro i _
    have h0 : 0 ≤ ‖z i‖ := norm_nonneg _
    rcases le_total 1 ‖z i‖ with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith)]
    · rw [max_eq_left h, max_eq_left (by nlinarith)]
      norm_num
  have hprod : ∏ i ∈ s, max 1 (‖z i‖ ^ 2) = (∏ i ∈ s, max 1 ‖z i‖) ^ 2 := by
    rw [Finset.prod_congr rfl hsq, Finset.prod_pow]
  have hP1 : 1 ≤ ∏ i ∈ s, max 1 ‖z i‖ :=
    Finset.one_le_prod₀ (fun i _ => le_max_left _ _)
  have hle : ∏ i ∈ s, max 1 (‖z i‖ ^ 2) ≤ B ^ 2 := by
    rw [hprod]
    exact pow_le_pow_left₀ (by linarith) hB 2
  exact sum_le_of_prod_max_le s (fun i => ‖z i‖ ^ 2) (B ^ 2) hle

/-- **Control: the bound is attained.** For `C ≥ 1` and the family `(C, 1, …, 1)` on
`Fin (n + 1)`, the product of `max 1 ·` is exactly `C` and the sum is exactly `C + n`,
i.e. `C + (card - 1)`. So `sum_le_of_prod_max_le` is sharp, not slack. -/
theorem sum_le_of_prod_max_le_sharp (n : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    (∏ i : Fin (n + 1), max 1 ((Fin.cons C (fun _ => (1 : ℝ)) : Fin (n + 1) → ℝ) i) = C) ∧
    (∑ i : Fin (n + 1), (Fin.cons C (fun _ => (1 : ℝ)) : Fin (n + 1) → ℝ) i
      = C + (((Finset.univ : Finset (Fin (n + 1))).card : ℝ) - 1)) := by
  constructor
  · rw [Fin.prod_univ_succ]
    simp [max_eq_right hC]
  · rw [Fin.sum_univ_succ]
    simp

/-- **Control: the bound is not automatic.** Without the product hypothesis the sum is
unbounded: two indices with `a = (C + 2, C + 2)` exceed `C + 1` for every `C ≥ 0`. -/
theorem sum_le_needs_prod_hyp (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∑ i : Fin 2, (fun _ => C + 2 : Fin 2 → ℝ) i ≤ C + (((Finset.univ : Finset (Fin 2)).card : ℝ) - 1)) := by
  simp
  linarith

end RulerSelection
