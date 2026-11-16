module

public import Mathlib
public import HeightT2.Instance.EqualityL

/-!
# Statement-review probes for the equality case

* `eq_hK_needed` : without `2 ≤ [K : ℚ]` the universally quantified equivalence is false (in `ℚ`).
* `eq_integer_hK_needed` : the same for the `𝓞 K` form (in `𝓞 ℚ`, at `2`).
* `eq_hK_satisfiable`, `eq_equality_at_neg_one`, `eq_neg_one_values` : the hypotheses are jointly
  satisfiable in `L` and the equality side is inhabited (`x = -1`, both sides equal `12`,
  computed directly, not through the equivalence).
* `eq_rootOfUnity_iff` : the predicate `∃ m, 0 < m ∧ x ^ m = 1` on `𝓞 K` is Mathlib's
  `IsOfFinOrder`.
* `eq_structure_second_nontrivial` : the second conjunct of `eq_case_structure` is not automatic.
* `strict_lemma_*_needed` : each hypothesis of `sum_add_one_lt_prod_add_card` is needed.
-/

@[expose] public section

open NumberField HermiteCompositum.Instance

namespace HeightT2.Review

noncomputable section

/-- Unfolding check: Mathlib's `mulHeight₁` on a number field is the place product. -/
example {K : Type*} [Field K] [NumberField K] (x : K) :
    Height.mulHeight₁ x =
      (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) * ∏ᶠ v : FinitePlace K, max (v x) 1 :=
  NumberField.mulHeight₁_eq x

/-- Deleting `2 ≤ n`: the equivalence fails for some `x` in `ℚ`. -/
theorem eq_hK_needed :
    ¬ ∀ x : ℚ, (∑ σ : ℚ →+* ℂ, ‖σ x‖ ^ 2 =
        Height.mulHeight₁ x ^ 2 + ((Module.finrank ℚ ℚ : ℝ) - 1) ↔
      ∃ m : ℕ, 0 < m ∧ x ^ m = 1) := fun h =>
  HeightT2.control_finrank_two_needed.2 ((h 2).mp HeightT2.control_finrank_two_needed.1)

/-- Deleting `2 ≤ n` in the `𝓞 K` form: the equivalence fails at `2 : 𝓞 ℚ`. -/
theorem eq_integer_hK_needed :
    ¬ ∀ x : 𝓞 ℚ, (∑ σ : ℚ →+* ℂ, ‖σ (x : ℚ)‖ ^ 2 =
        Height.mulHeight₁ (x : ℚ) ^ 2 + ((Module.finrank ℚ ℚ : ℝ) - 1) ↔
      ∃ m : ℕ, 0 < m ∧ x ^ m = 1) := by
  intro h
  have h2 := h 2
  have hc : ((2 : 𝓞 ℚ) : ℚ) = 2 := by rw [RingOfIntegers.coe_eq_algebraMap, map_ofNat]
  rw [hc] at h2
  obtain ⟨m, hm, hxm⟩ := h2.mp HeightT2.control_finrank_two_needed.1
  have := congrArg (algebraMap (𝓞 ℚ) ℚ) hxm
  rw [map_pow, map_one, map_ofNat] at this
  exact HeightT2.control_finrank_two_needed.2 ⟨m, hm, this⟩

/-- The degree hypothesis holds in `L`. -/
theorem eq_hK_satisfiable : 2 ≤ Module.finrank ℚ L := by
  rw [finrank_L]; norm_num

/-- The equality side is inhabited in `L` (at `x = -1`, through the equivalence). -/
theorem eq_equality_at_neg_one :
    ∑ σ : L →+* ℂ, ‖σ (-1 : L)‖ ^ 2 =
      Height.mulHeight₁ (-1 : L) ^ 2 + ((Module.finrank ℚ L : ℝ) - 1) :=
  (HeightT2.sum_norm_sq_eq_mulHeight₁_sq_add_iff eq_hK_satisfiable _).mpr
    ⟨2, by norm_num, by norm_num⟩

/-- Direct computation at `x = -1` in `L`, independent of the equivalence:
`T₂(-1) = 12` and `mulHeight₁(-1)² = 1`, so both sides are `12`. -/
theorem eq_neg_one_values :
    ∑ σ : L →+* ℂ, ‖σ (-1 : L)‖ ^ 2 = 12 ∧ Height.mulHeight₁ (-1 : L) ^ 2 = 1 := by
  constructor
  · simp only [map_neg, map_one, norm_neg, norm_one, one_pow, Finset.sum_const,
      Finset.card_univ, Embeddings.card L ℂ, finrank_L, nsmul_eq_mul, mul_one]
    norm_num
  · rw [← Height.mulHeight₁_pow]
    norm_num

/-- The root-of-unity predicate used on `𝓞 K` is Mathlib's `IsOfFinOrder`. -/
theorem eq_rootOfUnity_iff {K : Type*} [Field K] [NumberField K] (x : 𝓞 K) :
    (∃ m : ℕ, 0 < m ∧ x ^ m = 1) ↔ IsOfFinOrder x :=
  isOfFinOrder_iff_pow_eq_one.symm

/-- The second conjunct of `eq_case_structure` is not automatic: at `x = 2` in `L` it fails. -/
theorem eq_structure_second_nontrivial :
    ¬ ∀ σ τ : L →+* ℂ, σ ≠ τ → ‖σ (2 : L)‖ = 1 ∨ ‖τ (2 : L)‖ = 1 := by
  intro h
  have hcard : 1 < Fintype.card (L →+* ℂ) := by
    rw [Embeddings.card L ℂ, finrank_L]; norm_num
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ := Fintype.exists_ne_of_one_lt_card hcard σ
  have h2 : ∀ φ : L →+* ℂ, ‖φ (2 : L)‖ = 2 := fun φ => by rw [map_ofNat]; norm_num
  rcases h σ τ (Ne.symm hτ) with h' | h' <;> rw [h2] at h' <;> norm_num at h'

/-- `sum_add_one_lt_prod_add_card` without `i ≠ j`: fails at `s = {0}`, `y = 2`. -/
theorem strict_lemma_hij_needed :
    ¬ (∑ k ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (2 : ℝ)) k + 1 <
      ∏ k ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (2 : ℝ)) k +
        ((Finset.univ : Finset (Fin 1)).card : ℝ)) := by
  simp

/-- Without `1 < y j`: fails at `y = (2, 1)` (`4 = 4`). -/
theorem strict_lemma_hyj_needed :
    ¬ (∑ k ∈ (Finset.univ : Finset (Fin 2)), (![2, 1] : Fin 2 → ℝ) k + 1 <
      ∏ k ∈ (Finset.univ : Finset (Fin 2)), (![2, 1] : Fin 2 → ℝ) k +
        ((Finset.univ : Finset (Fin 2)).card : ℝ)) := by
  simp [Fin.sum_univ_two, Fin.prod_univ_two]
  try norm_num

/-- Without `∀ k, 1 ≤ y k`: fails at `y = (2, 2, 0)` (`5` against `3`). -/
theorem strict_lemma_hy_needed :
    ¬ (∑ k ∈ (Finset.univ : Finset (Fin 3)), (![2, 2, 0] : Fin 3 → ℝ) k + 1 <
      ∏ k ∈ (Finset.univ : Finset (Fin 3)), (![2, 2, 0] : Fin 3 → ℝ) k +
        ((Finset.univ : Finset (Fin 3)).card : ℝ)) := by
  simp [Fin.sum_univ_three, Fin.prod_univ_three]
  try norm_num

end

end HeightT2.Review
