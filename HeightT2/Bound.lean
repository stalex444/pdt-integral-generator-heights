module

public import Mathlib
public import HeightT2.Bridge
public import RulerSelection.MahlerT2

/-!
# `T₂` is bounded by the square of Mathlib's multiplicative height

For a number field `K` of degree `n` and every `x ∈ K`,
`T₂(x) = ∑_{σ : K →+* ℂ} ‖σ x‖² ≤ mulHeight₁(x)² + n − 1`
(`sum_norm_sq_le_mulHeight₁_sq_add`). The real inequality used, y₁ + ⋯ + y_k ≤ k − 1 + y₁⋯y_k
for yᵢ ≥ 1, is Lemma 6 of Dubickas (2023); here it is applied with yᵢ = max(1, ‖σᵢ x‖)².
The proof combines `prod_embeddings_le_mulHeight₁` with the complex-family inequality
`RulerSelection.sum_norm_sq_le_of_prod_max_norm_le` and `Embeddings.card`.

Controls: equality holds at `x = 1` in every number field (`control_bound_attained_one`), and at
`x = 2` in `ℚ`, an element with one large conjugate (`control_bound_attained_rat_two`).
-/

@[expose] public section

open NumberField

namespace HeightT2

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- For every `x : K`, `T₂(x) ≤ mulHeight₁(x)² + (n − 1)` with `n = [K : ℚ]`. -/
theorem sum_norm_sq_le_mulHeight₁_sq_add (x : K) :
    ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 ≤ Height.mulHeight₁ x ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) := by
  have h := RulerSelection.sum_norm_sq_le_of_prod_max_norm_le Finset.univ
    (fun σ : K →+* ℂ => σ x) _ (prod_embeddings_le_mulHeight₁ x)
  rwa [Finset.card_univ, Embeddings.card K ℂ] at h

/-- **Control (bound attained).** At `x = 1` both sides equal `n`. -/
theorem control_bound_attained_one :
    ∑ σ : K →+* ℂ, ‖σ (1 : K)‖ ^ 2 =
      Height.mulHeight₁ (1 : K) ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) := by
  simp only [map_one, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
    Embeddings.card K ℂ, Height.mulHeight₁_one, nsmul_eq_mul, mul_one]
  ring

/-- **Control (bound attained, one large conjugate).** In `ℚ`, at `x = 2` both sides equal `4`. -/
theorem control_bound_attained_rat_two :
    ∑ σ : ℚ →+* ℂ, ‖σ (2 : ℚ)‖ ^ 2 =
      Height.mulHeight₁ (2 : ℚ) ^ 2 + ((Module.finrank ℚ ℚ : ℝ) - 1) := by
  have hσ : ∀ σ : ℚ →+* ℂ, ‖σ (2 : ℚ)‖ ^ 2 = 4 := fun σ => by
    rw [map_ofNat]; norm_num
  rw [Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_const, Finset.card_univ,
    Embeddings.card ℚ ℂ, Module.finrank_self, mulHeight₁_rat_two]
  norm_num

end

end HeightT2
