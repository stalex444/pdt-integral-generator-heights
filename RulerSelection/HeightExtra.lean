module

public import Mathlib
public import RulerSelection.Height

/-!
# Converse-direction lemmas, partial (NOT needed for the main theorem; done because time remained)

* `embHeight_neg` : `H(−x) = H(x)`.
* `embHeight_inv_mul` : for `x ≠ 0`, `H(x⁻¹) · ∏_σ ‖σ x‖ = H(x)`.
* `prod_norm_ρQ` : `∏_σ ‖σ(ρQ)‖ = 1`.
* `embHeight_ρQ_inv` : `H((ρQ)⁻¹) = H(ρQ)`; with `embHeight_neg`, all four of `±(ρQ)^(±1)`
  have height `H(ρQ)` (`embHeight_neg_ρQ`, `embHeight_neg_ρQ_inv`).
-/

@[expose] public section

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance

theorem embHeight_neg (x : L) : embHeight (-x) = embHeight x := by
  simp [embHeight, map_neg, norm_neg]

theorem embHeight_inv_mul (x : L) (hx : x ≠ 0) :
    embHeight x⁻¹ * ∏ σ : L →+* ℂ, ‖σ x‖ = embHeight x := by
  rw [embHeight, embHeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have hpos : 0 < ‖σ x‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hx)
  rw [map_inv₀, norm_inv, max_mul_of_nonneg _ _ hpos.le, one_mul, inv_mul_cancel₀ hpos.ne',
    max_comm]

theorem norm_zs0 : ‖zs 0‖ = rhoR := by
  show ‖((rhoR : ℝ) : ℂ)‖ = rhoR
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [rhoR_lo])]
theorem norm_zs1 : ‖zs 1‖ = ‖zC‖ := rfl
theorem norm_zs2 : ‖zs 2‖ = ‖zC‖ := by show ‖star zC‖ = _; rw [norm_star]
theorem norm_ws0 : ‖ws 0‖ = QR := by
  show ‖((QR : ℝ) : ℂ)‖ = QR
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [QR_lo])]
theorem norm_ws1 : ‖ws 1‖ = -qN := by
  show ‖((qN : ℝ) : ℂ)‖ = -qN
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [qN_hi])]
theorem norm_ws2 : ‖ws 2‖ = ‖wC‖ := rfl
theorem norm_ws3 : ‖ws 3‖ = ‖wC‖ := by show ‖star wC‖ = _; rw [norm_star]

/-- `|N(ρQ)| = 1` as a product of the twelve moduli. -/
theorem prod_norm_ρQ : ∏ σ : L →+* ℂ, ‖σ (ρ * Q)‖ = 1 := by
  rw [prod_emb, Fintype.prod_prod_type]
  simp only [map_mul, φL_ρ, φL_Q, norm_mul, Fin.prod_univ_three, Fin.prod_univ_four]
  rw [norm_zs0, norm_zs1, norm_zs2, norm_ws0, norm_ws1, norm_ws2, norm_ws3]
  have h1 : rhoR * ‖zC‖ ^ 2 = 1 := by
    rw [zC_normSq]; linear_combination rhoR_eq
  have h2 : QR * (-qN) * ‖wC‖ ^ 2 = 1 := by
    rw [wC_normSq]; linear_combination -quartic_e2
  calc _ = (rhoR * ‖zC‖ ^ 2) ^ 4 * (QR * (-qN) * ‖wC‖ ^ 2) ^ 3 := by ring
    _ = 1 := by rw [h1, h2]; norm_num

theorem ρQ_ne_zero : ρ * Q ≠ 0 := by
  intro h
  have := congrArg (φL (0, 0)) h
  rw [map_mul, φL_ρ, φL_Q, map_zero] at this
  have h1 : zs 0 ≠ 0 := by
    intro h0; have := congrArg norm h0; rw [norm_zs0, norm_zero] at this; linarith [rhoR_lo]
  have h2 : ws 0 ≠ 0 := by
    intro h0; have := congrArg norm h0; rw [norm_ws0, norm_zero] at this; linarith [QR_lo]
  exact mul_ne_zero h1 h2 this

theorem embHeight_ρQ_inv : embHeight (ρ * Q)⁻¹ = embHeight (ρ * Q) := by
  have := embHeight_inv_mul (ρ * Q) ρQ_ne_zero
  rwa [prod_norm_ρQ, mul_one] at this

theorem embHeight_neg_ρQ : embHeight (-(ρ * Q)) = embHeight (ρ * Q) := embHeight_neg _

theorem embHeight_neg_ρQ_inv : embHeight (-(ρ * Q)⁻¹) = embHeight (ρ * Q) := by
  rw [embHeight_neg, embHeight_ρQ_inv]

end

end RulerSelection.Emb
