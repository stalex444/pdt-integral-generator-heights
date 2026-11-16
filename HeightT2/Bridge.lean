module

public import Mathlib

/-!
# Mathlib's multiplicative height and the product over complex embeddings

For a number field `K`, `Height.mulHeight₁ x` is the product, over the infinite places `w` of `K`
counted with multiplicity `w.mult`, of `max (w x) 1`, times the product over the finite places.

* `prod_infinitePlace_eq_prod_embeddings` : the infinite part equals
  `∏ σ : K →+* ℂ, max 1 ‖σ x‖` (each real place is one embedding, each complex place two).
* `prod_embeddings_le_mulHeight₁` : for every `x : K`, `∏ σ, max 1 ‖σ x‖ ≤ mulHeight₁ x`.
* `mulHeight₁_eq_prod_embeddings` : for an algebraic integer `x`, equality holds: every finite
  place contributes the factor `1`.
* `mulHeight₁_eq_prod_embeddings_of_isIntegral` : the same for `x : K` integral over `ℤ`.

Controls: in `ℚ`, `x = 1/2` has `∏ σ, max 1 ‖σ x‖ = 1 < 2 = mulHeight₁ x`, so the integrality
hypothesis cannot be dropped from the equality (`control_bridge_integral_needed`).
-/

@[expose] public section

open NumberField

namespace HeightT2

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The infinite part of `mulHeight₁`, written as a product over complex embeddings. -/
theorem prod_infinitePlace_eq_prod_embeddings (x : K) :
    ∏ w : InfinitePlace K, max (w x) 1 ^ w.mult = ∏ σ : K →+* ℂ, max 1 ‖σ x‖ := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun σ : K →+* ℂ => max 1 ‖σ x‖)]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)),
      max 1 ‖φ x‖ = max (w x) 1 := by
    intro φ hφ
    rw [← (Finset.mem_filter.mp hφ).2, InfinitePlace.apply, max_comm]
  rw [Finset.prod_congr rfl h, Finset.prod_const, InfinitePlace.card_filter_mk_eq]

/-- A finite place takes value at most `1` on an algebraic integer. -/
theorem finitePlace_le_one (w : FinitePlace K) (x : 𝓞 K) : w (x : K) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one K (FinitePlace.maximalIdeal w) x

/-- The finite part of `mulHeight₁` is `1` at an algebraic integer. -/
theorem finprod_finitePlace_eq_one (x : 𝓞 K) :
    ∏ᶠ w : FinitePlace K, max (w (x : K)) 1 = 1 := by
  rw [finprod_congr (fun w => max_eq_right (finitePlace_le_one w x))]
  exact finprod_one

/-- The finite part of `mulHeight₁` is at least `1` at every element. -/
theorem one_le_finprod_finitePlace (x : K) :
    1 ≤ ∏ᶠ w : FinitePlace K, max (w x) 1 :=
  one_le_finprod fun _ => le_max_right _ _

/-- For every `x : K`, the product over complex embeddings is at most `mulHeight₁ x`. -/
theorem prod_embeddings_le_mulHeight₁ (x : K) :
    ∏ σ : K →+* ℂ, max 1 ‖σ x‖ ≤ Height.mulHeight₁ x := by
  rw [NumberField.mulHeight₁_eq, prod_infinitePlace_eq_prod_embeddings]
  exact le_mul_of_one_le_right
    (Finset.prod_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _))
    (one_le_finprod_finitePlace x)

/-- For an algebraic integer, `mulHeight₁` is the product over complex embeddings of
`max 1 ‖σ x‖` (the order `max 1 _` as written here). -/
theorem mulHeight₁_eq_prod_embeddings (x : 𝓞 K) :
    Height.mulHeight₁ (x : K) = ∏ σ : K →+* ℂ, max 1 ‖σ (x : K)‖ := by
  rw [NumberField.mulHeight₁_eq, finprod_finitePlace_eq_one, mul_one,
    prod_infinitePlace_eq_prod_embeddings]

/-- The same for an element of `K` integral over `ℤ`. -/
theorem mulHeight₁_eq_prod_embeddings_of_isIntegral (x : K) (hx : IsIntegral ℤ x) :
    Height.mulHeight₁ x = ∏ σ : K →+* ℂ, max 1 ‖σ x‖ :=
  mulHeight₁_eq_prod_embeddings (⟨x, hx⟩ : 𝓞 K)

/-- In `ℚ`, `mulHeight₁ 2 = 2`. -/
theorem mulHeight₁_rat_two : Height.mulHeight₁ (2 : ℚ) = 2 := by
  have h := mulHeight₁_eq_prod_embeddings (2 : 𝓞 ℚ)
  have h2 : ((2 : 𝓞 ℚ) : ℚ) = 2 := by norm_cast
  rw [h2] at h
  rw [h]
  have hσ : ∀ σ : ℚ →+* ℂ, max 1 ‖σ (2 : ℚ)‖ = 2 := fun σ => by
    rw [map_ofNat]; norm_num
  rw [Finset.prod_congr rfl (fun σ _ => hσ σ), Finset.prod_const, Finset.card_univ,
    Embeddings.card ℚ ℂ, Module.finrank_self, pow_one]

/-- **Control.** The integrality hypothesis cannot be dropped from
`mulHeight₁_eq_prod_embeddings`: in `ℚ`, at `x = 1/2` the product over embeddings is `1`
and `mulHeight₁ x = 2`. -/
theorem control_bridge_integral_needed :
    ∏ σ : ℚ →+* ℂ, max 1 ‖σ (2 : ℚ)⁻¹‖ = 1 ∧ Height.mulHeight₁ (2 : ℚ)⁻¹ = 2 := by
  constructor
  · refine Finset.prod_eq_one fun σ _ => ?_
    rw [map_inv₀, map_ofNat]; norm_num
  · rw [Height.mulHeight₁_inv, mulHeight₁_rat_two]

end

end HeightT2
