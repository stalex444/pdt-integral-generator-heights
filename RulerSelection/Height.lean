module

public import Mathlib
public import RulerSelection.MahlerT2
public import RulerSelection.T2

/-!
# The embedding height on `L`, the S1 instance, and the height of `ρQ` (stage 2, lane A, A4)

`embHeight x = ∏_{σ : L →+* ℂ} max 1 ‖σ x‖` over Mathlib's twelve embeddings of the actual
field `HermiteCompositum.Instance.L`.

* `T2_le_embHeight_sq_add` : `T2 x ≤ embHeight x ^ 2 + 11` (stage 1's `sum_norm_sq_le_of_prod_max_norm_le`
  with `card_emb`).
* `embHeight_ρQ` : `embHeight (ρ * Q) = rhoR² · QR² / (−qN)`, from the twelve moduli
  `|zs i| · |ws j|` compared with `1` (six comparisons, each on rational boxes).
* `embHeight_ρQ_sq_add_lt` : `embHeight (ρ * Q) ^ 2 + 11 < 2403/100` (with stage 1's `threshold`).
* `T2_lt_of_embHeight_le` and `qf_lt_of_embHeight_le` : the composed bound in field and in
  coordinate form.
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance

/-- The height `∏_σ max 1 ‖σ x‖` over all twelve complex embeddings of `L`. -/
def embHeight (x : L) : ℝ := ∏ σ : L →+* ℂ, max 1 ‖σ x‖

theorem one_le_embHeight (x : L) : 1 ≤ embHeight x :=
  Finset.one_le_prod₀ fun _ _ => le_max_left _ _

/-- **S1 on `L`.** `T₂(x) ≤ H(x)² + 11`. -/
theorem T2_le_embHeight_sq_add (x : L) : T2 x ≤ embHeight x ^ 2 + 11 := by
  have h := RulerSelection.sum_norm_sq_le_of_prod_max_norm_le (Finset.univ : Finset (L →+* ℂ))
    (fun σ => σ x) (embHeight x) le_rfl
  rw [Finset.card_univ, card_emb] at h
  unfold T2
  norm_num at h
  linarith

/-- **The height of `ρQ`.** `H(ρQ) = ρ² Q² / |q′|`. -/
theorem embHeight_ρQ : embHeight (ρ * Q) = rhoR ^ 2 * QR ^ 2 / (-qN) := by
  have r_lo := rhoR_lo; have r_hi := rhoR_hi
  have Q_lo := QR_lo; have Q_hi := QR_hi
  have q_lo := qN_lo; have q_hi := qN_hi
  set r := rhoR with hr_def
  set QQ := QR with hQ_def
  set q := qN with hq_def
  set M := ‖zC‖ with hM_def
  set N := ‖wC‖ with hN_def
  have hM : M ^ 2 = r ^ 2 - 1 := zC_normSq
  have hN : N ^ 2 = (QQ + q) ^ 2 - QQ * q := wC_normSq
  have hM0 : 0 ≤ M := norm_nonneg _
  have hN0 : 0 ≤ N := norm_nonneg _
  have hr : r ^ 3 = r + 1 := rhoR_eq
  have e2 : (QQ * q) * ((QQ + q) ^ 2 - QQ * q) = -1 := quartic_e2
  -- rational boxes for the two non-real moduli
  have hM2 : 7548 / 10000 < M ^ 2 := by
    rw [hM]; nlinarith only [mul_pos (by linarith : (0:ℝ) < r - 13247 / 10000) (by linarith : (0:ℝ) < r), r_lo]
  have hM2' : M ^ 2 < 7552 / 10000 := by
    rw [hM]; nlinarith only [mul_pos (by linarith : (0:ℝ) < 13248 / 10000 - r) (by linarith : (0:ℝ) < r), r_hi]
  have hMlo : 86 / 100 < M :=
    lt_of_pow_lt_pow_left₀ 2 hM0 (by linarith only [hM2])
  have hMhi : M < 87 / 100 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by linarith only [hM2'])
  have hp_lo : 8843 / 10000 < -(QQ * q) := by
    nlinarith only [mul_pos (by linarith : (0:ℝ) < QQ - 12207 / 10000)
      (by linarith : (0:ℝ) < -q - 72449 / 100000), Q_lo, q_hi]
  have hp_hi : -(QQ * q) < 885 / 1000 := by
    nlinarith only [mul_pos (by linarith : (0:ℝ) < 12208 / 10000 - QQ)
      (by linarith : (0:ℝ) < -q), Q_hi, q_lo]
  have hs_lo : 4962 / 10000 < QQ + q := by linarith
  have hs_hi : QQ + q < 1 / 2 := by linarith
  have hN2 : 11236 / 10000 < N ^ 2 := by
    rw [hN]; nlinarith only [mul_pos (by linarith : (0:ℝ) < QQ + q - 4962 / 10000)
      (by linarith : (0:ℝ) < QQ + q), hs_lo, hp_lo]
  have hN2' : N ^ 2 < 11449 / 10000 := by
    rw [hN]; nlinarith only [mul_pos (by linarith : (0:ℝ) < 1 / 2 - (QQ + q))
      (by linarith : (0:ℝ) < QQ + q), hs_hi, hp_hi]
  have hN2lo : 106 / 100 < N :=
    lt_of_pow_lt_pow_left₀ 2 hN0 (by linarith only [hN2])
  have hN2hi : N < 107 / 100 :=
    lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by linarith only [hN2'])
  -- the six modulus comparisons
  have h00 : 1 ≤ r * QQ := by
    nlinarith only [mul_pos (by linarith : (0:ℝ) < r - 13247 / 10000)
      (by linarith : (0:ℝ) < QQ - 12207 / 10000), r_lo, Q_lo]
  have h01 : r * (-q) ≤ 1 := by
    nlinarith only [mul_pos (by linarith : (0:ℝ) < 13248 / 10000 - r)
      (by linarith : (0:ℝ) < -q), r_hi, q_lo]
  have h02 : 1 ≤ r * N := by
    nlinarith only [mul_pos (by linarith : (0:ℝ) < r - 13247 / 10000)
      (by linarith : (0:ℝ) < N - 106 / 100), r_lo, hN2lo]
  have h10 : 1 ≤ M * QQ := by
    nlinarith only [mul_pos (by linarith : (0:ℝ) < M - 86 / 100)
      (by linarith : (0:ℝ) < QQ - 12207 / 10000), hMlo, Q_lo]
  have h11 : M * (-q) ≤ 1 := by
    nlinarith only [mul_nonneg (by linarith : (0:ℝ) ≤ 87 / 100 - M) (by linarith : (0:ℝ) ≤ -q),
      q_lo, hMhi, hM0]
  have h12 : M * N ≤ 1 := by
    nlinarith only [mul_nonneg (by linarith : (0:ℝ) ≤ 87 / 100 - M) hN0, hN2hi]
  -- the twelve moduli
  have n0 : ‖zs 0‖ = r := by
    show ‖((rhoR : ℝ) : ℂ)‖ = r
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have n1 : ‖zs 1‖ = M := rfl
  have n2 : ‖zs 2‖ = M := by show ‖star zC‖ = M; rw [norm_star]
  have m0 : ‖ws 0‖ = QQ := by
    show ‖((QR : ℝ) : ℂ)‖ = QQ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have m1 : ‖ws 1‖ = -q := by
    show ‖((qN : ℝ) : ℂ)‖ = -q
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  have m2 : ‖ws 2‖ = N := rfl
  have m3 : ‖ws 3‖ = N := by show ‖star wC‖ = N; rw [norm_star]
  rw [embHeight, prod_emb, Fintype.prod_prod_type]
  simp only [map_mul, φL_ρ, φL_Q, norm_mul, Fin.prod_univ_three, Fin.prod_univ_four]
  rw [n0, n1, n2, m0, m1, m2, m3, max_eq_right h00, max_eq_left h01, max_eq_right h02,
    max_eq_right h10, max_eq_left h11, max_eq_left h12]
  rw [eq_div_iff (by linarith)]
  linear_combination (-q * r ^ 3 * QQ ^ 3 * N ^ 2) * hM + (-q * QQ ^ 3 * N ^ 2 * r ^ 2) * hr
    + (-q * QQ ^ 3 * r ^ 2) * hN + (-r ^ 2 * QQ ^ 2) * e2

/-- `H(ρQ)² + 11 < 24.03` (stage 1's `threshold` at the actual roots). -/
theorem embHeight_ρQ_sq_add_lt : embHeight (ρ * Q) ^ 2 + 11 < 2403 / 100 := by
  rw [embHeight_ρQ]; exact threshold_inst

/-- **Composed bound (field form).** If `H(x) ≤ H(ρQ)` then `T₂(x) < 24.03`. -/
theorem T2_lt_of_embHeight_le (x : L) (h : embHeight x ≤ embHeight (ρ * Q)) :
    T2 x < 2403 / 100 := by
  have h1 := T2_le_embHeight_sq_add x
  have h2 : embHeight x ^ 2 ≤ embHeight (ρ * Q) ^ 2 :=
    pow_le_pow_left₀ (by linarith [one_le_embHeight x]) h 2
  linarith [embHeight_ρQ_sq_add_lt]

/-- **Composed bound (coordinate form).** If `x = ∑ a(i,j) ρ^i Q^j` with integer `a` and
`H(x) ≤ H(ρQ)` then `aᵀ (Smat ρ ⊗ₖ Tmat Q q′) a < 24.03`. -/
theorem qf_lt_of_embHeight_le (a : Fin 3 × Fin 4 → ℤ)
    (h : embHeight (∑ p : Fin 3 × Fin 4, (a p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ))
      ≤ embHeight (ρ * Q)) :
    (fun p => (a p : ℝ)) ⬝ᵥ ((GramCert.Smat rhoR ⊗ₖ GramCert.Tmat QR qN) *ᵥ
        (fun p => (a p : ℝ))) < 2403 / 100 := by
  rw [← T2_coords]; exact T2_lt_of_embHeight_le _ h

/-- **Control.** `H(1) = 1`. -/
theorem embHeight_one : embHeight 1 = 1 := by simp [embHeight]

end

end RulerSelection.Emb
