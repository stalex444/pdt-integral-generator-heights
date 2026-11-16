module

public import Mathlib
public import HeightT2.Bridge
public import HeightT2.Bound
public import HeightT2.Instance.SmallHeight

/-!
# Statement-review probes for the height bridge, the `T₂` bound and the small-height list

* `mulHeight₁_unfold` : Mathlib's `mulHeight₁` is the product over infinite places (with
  multiplicity, `max (w x) 1`) times the product over finite places; no degree normalisation.
* `mulHeight₁_two_eq_pow` : computed by Mathlib's place-sum route (not the bridge),
  `mulHeight₁ 2 = 2 ^ [K : ℚ]`: the relative height, not the absolute one.
* `prod_embeddings_two` : the bridge's right side at `2` is the same number.
* `mulHeight₁_two_of_finrank_two`, `half_of_finrank_two` : in any quadratic field,
  `mulHeight₁ 2 = 4`; at `1/2`, `T₂ = 1/2`, the embedding product is `1`, the height is `4`.
* `rat_half_mathlib` : in `ℚ`, `mulHeight₁ (1/2) = 2` by Mathlib's `mulHeight₁_eq_max`.
* `small_height_hx_needed` : the small-height equivalence fails at `x = 0`.
-/

@[expose] public section

open NumberField

namespace HeightT2.Review

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Mathlib's definition, unfolded: infinite places with multiplicity, then finite places. -/
theorem mulHeight₁_unfold (x : K) :
    Height.mulHeight₁ x =
      (∏ w : InfinitePlace K, max (w x) 1 ^ w.mult) * ∏ᶠ w : FinitePlace K, max (w x) 1 :=
  NumberField.mulHeight₁_eq x

/-- `mulHeight₁ 2 = 2 ^ [K : ℚ]`, through infinite places and `totalWeight`, independent of
the embedding-product rewrite. -/
theorem mulHeight₁_two_eq_pow :
    Height.mulHeight₁ (2 : K) = 2 ^ Module.finrank ℚ K := by
  rw [NumberField.mulHeight₁_eq]
  have h2 : ∀ w : InfinitePlace K, max (w (2 : K)) 1 ^ w.mult = (2 : ℝ) ^ w.mult := by
    intro w
    have : w (2 : K) = 2 := by
      rw [← InfinitePlace.norm_embedding_eq, map_ofNat]; norm_num
    rw [this]; norm_num
  have hfin := HeightT2.finprod_finitePlace_eq_one (K := K) 2
  have hc : ((2 : 𝓞 K) : K) = 2 := by norm_cast
  rw [hc] at hfin
  rw [Finset.prod_congr rfl (fun w _ => h2 w), hfin, mul_one, Finset.prod_pow_eq_pow_sum,
    ← NumberField.totalWeight_eq_sum_mult, NumberField.totalWeight_eq_finrank]

/-- The embedding product at `2` is `2 ^ [K : ℚ]`. -/
theorem prod_embeddings_two :
    ∏ σ : K →+* ℂ, max 1 ‖σ (2 : K)‖ = 2 ^ Module.finrank ℚ K := by
  have hσ : ∀ σ : K →+* ℂ, max 1 ‖σ (2 : K)‖ = 2 := fun σ => by
    rw [map_ofNat]; norm_num
  rw [Finset.prod_congr rfl (fun σ _ => hσ σ), Finset.prod_const, Finset.card_univ,
    Embeddings.card K ℂ]

/-- In a quadratic field, `mulHeight₁ 2 = 4`. -/
theorem mulHeight₁_two_of_finrank_two (hK : Module.finrank ℚ K = 2) :
    Height.mulHeight₁ (2 : K) = 4 := by
  rw [mulHeight₁_two_eq_pow, hK]; norm_num

/-- In a quadratic field, at `x = 1/2`: `T₂ = 1/2`, the embedding product is `1`, and
`mulHeight₁ = 4`; the bound reads `1/2 ≤ 17`. -/
theorem half_of_finrank_two (hK : Module.finrank ℚ K = 2) :
    ∑ σ : K →+* ℂ, ‖σ (2 : K)⁻¹‖ ^ 2 = 1 / 2 ∧
    ∏ σ : K →+* ℂ, max 1 ‖σ (2 : K)⁻¹‖ = 1 ∧
    Height.mulHeight₁ (2 : K)⁻¹ = 4 ∧
    Height.mulHeight₁ (2 : K)⁻¹ ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) = 17 := by
  have hn : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by rw [norm_inv]; norm_num
  have hcard : (Finset.univ : Finset (K →+* ℂ)).card = 2 := by
    rw [Finset.card_univ, Embeddings.card K ℂ, hK]
  have hH : Height.mulHeight₁ (2 : K)⁻¹ = 4 := by
    rw [Height.mulHeight₁_inv, mulHeight₁_two_of_finrank_two hK]
  refine ⟨?_, ?_, hH, ?_⟩
  · simp only [map_inv₀, map_ofNat, hn, Finset.sum_const, hcard, nsmul_eq_mul]; norm_num
  · refine Finset.prod_eq_one fun σ _ => ?_
    rw [map_inv₀, map_ofNat, hn]; norm_num
  · rw [hH, hK]; norm_num

/-- The bound at `1/2`, as an instance of the general statement (no integrality needed). -/
theorem bound_at_half_of_finrank_two :
    ∑ σ : K →+* ℂ, ‖σ (2 : K)⁻¹‖ ^ 2 ≤
      Height.mulHeight₁ (2 : K)⁻¹ ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) :=
  HeightT2.sum_norm_sq_le_mulHeight₁_sq_add _

/-- At `1/2` in a quadratic field the embedding product is strictly below the height. -/
theorem prod_lt_height_half_of_finrank_two (hK : Module.finrank ℚ K = 2) :
    ∏ σ : K →+* ℂ, max 1 ‖σ (2 : K)⁻¹‖ < Height.mulHeight₁ (2 : K)⁻¹ := by
  obtain ⟨-, h1, h4, -⟩ := half_of_finrank_two hK
  rw [h1, h4]; norm_num

/-- In `ℚ`, Mathlib's own formula gives `mulHeight₁ (1/2) = 2`. -/
theorem rat_half_mathlib : Height.mulHeight₁ (2 : ℚ)⁻¹ = 2 := by
  rw [Rat.mulHeight₁_eq_max]; norm_num

open RulerSelection.Emb HermiteCompositum.Instance

/-- `embHeight` is the embedding product, by definition. -/
theorem embHeight_unfold (x : L) : embHeight x = ∏ σ : L →+* ℂ, max 1 ‖σ x‖ := rfl

/-- **Hypothesis deletion.** Without `x ≠ 0` the small-height equivalence is false: `0` has
height `1 ≤ mulHeight₁ (ρQ)` and is not in the list. -/
theorem small_height_hx_needed :
    ¬ ∀ x : 𝓞 L, Height.mulHeight₁ (x : L) ≤ Height.mulHeight₁ (ρ * Q) ↔
      (x : L) ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
        -(ρ * Q)⁻¹} : Set L) := by
  intro h
  have h0 := (h 0).mp (by
    have hz : ((0 : 𝓞 L) : L) = 0 := by simp
    rw [hz, Height.mulHeight₁_zero]; exact Height.one_le_mulHeight₁ _)
  have hρ := RulerSelection.LaneC.ρ_ne_zero'
  have hQ := RulerSelection.LaneC.Q_ne_zero'
  have hz : ((0 : 𝓞 L) : L) = 0 := by simp
  rw [hz] at h0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
  rcases h0 with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    first
    | exact absurd h.symm one_ne_zero
    | exact absurd h.symm (neg_ne_zero.mpr one_ne_zero)
    | exact absurd h.symm hρ
    | exact absurd h.symm (neg_ne_zero.mpr hρ)
    | exact absurd h.symm (inv_ne_zero hρ)
    | exact absurd h.symm (neg_ne_zero.mpr (inv_ne_zero hρ))
    | exact absurd h.symm hQ
    | exact absurd h.symm (neg_ne_zero.mpr hQ)
    | exact absurd h.symm (inv_ne_zero hQ)
    | exact absurd h.symm (neg_ne_zero.mpr (inv_ne_zero hQ))
    | exact absurd h.symm (mul_ne_zero hρ hQ)
    | exact absurd h.symm (neg_ne_zero.mpr (mul_ne_zero hρ hQ))
    | exact absurd h.symm (inv_ne_zero (mul_ne_zero hρ hQ))
    | exact absurd h.symm (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero hρ hQ)))

end

end HeightT2.Review

#print axioms HeightT2.Review.mulHeight₁_unfold
#print axioms HeightT2.Review.mulHeight₁_two_eq_pow
#print axioms HeightT2.Review.prod_embeddings_two
#print axioms HeightT2.Review.mulHeight₁_two_of_finrank_two
#print axioms HeightT2.Review.half_of_finrank_two
#print axioms HeightT2.Review.bound_at_half_of_finrank_two
#print axioms HeightT2.Review.prod_lt_height_half_of_finrank_two
#print axioms HeightT2.Review.rat_half_mathlib
#print axioms HeightT2.Review.embHeight_unfold
#print axioms HeightT2.Review.small_height_hx_needed
