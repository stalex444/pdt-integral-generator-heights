module

public import Mathlib

/-!
# GramCert — the two positive-semidefiniteness certificates (Stage 1, P2)

`Smat ρ` is the `T₂` Gram of `ℤ[ρ]` in `{1, ρ, ρ²}`; `Tmat Q Q'` the `T₂` Gram of `ℤ[Q]` in
`{1, Q, Q², Q³}` written as a polynomial in the two real roots `Q > 1 > 0 > Q'` of `x⁴ − x − 1`
(the complex pair enters through `z + z̄ = −(Q + Q')`, `z z̄ = −(Q³ − 1)(Q'³ − 1)`, reduced
by `x⁴ = x + 1`; cross-checked numerically against the gate's `kron.py` to 1e-30).
`S0`, `T0` are the two-decimal rational lower forms. Each statement is `∀ v, 0 ≤ vᵀ (M − M₀) v`.
-/

@[expose] public section

namespace RulerSelection.GramCert

open Matrix

noncomputable def Smat (ρ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![(3:ℝ), 0, 2; 0, 3*ρ^2-2, ρ; 2, ρ, -ρ^2+3*ρ+2]

noncomputable def S0 : Matrix (Fin 3) (Fin 3) ℝ := !![(299/100:ℝ), (0:ℝ), (2:ℝ); (0:ℝ), (13/4:ℝ), (33/25:ℝ); (2:ℝ), (33/25:ℝ), (421/100:ℝ)]

noncomputable def Tmat (Q Q' : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(4), (0), (2*Q^3*Q'^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*Q'^1 - 2*Q'^3 + 2*Q'^2 + 2), (-3*Q^3 - 3*Q^2*Q'^1 - 3*Q^1*Q'^2 - 3*Q'^3 + 6); (0), (-2*Q^3*Q'^3 + 2*Q^3 + 1*Q^2 + 2*Q'^3 + 1*Q'^2 - 2), (2*Q^3 + 2*Q'^3 - 2), (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 1*Q^3*Q'^1 + 2*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 - 2*Q^2 - 1*Q^1*Q'^3 + 2*Q^1 + 2*Q'^3 - 2*Q'^2 + 2*Q'^1 - 2); (2*Q^3*Q'^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*Q'^1 - 2*Q'^3 + 2*Q'^2 + 2), (2*Q^3 + 2*Q'^3 - 2), (2*Q^3*Q'^3 - 2*Q^3*Q'^2 - 2*Q^3 - 2*Q^2*Q'^3 + 2*Q^2*Q'^2 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 4), (2*Q^3*Q'^3 - 1*Q^3*Q'^2 - 2*Q^3 - 1*Q^2*Q'^3 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 2); (-3*Q^3 - 3*Q^2*Q'^1 - 3*Q^1*Q'^2 - 3*Q'^3 + 6), (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 1*Q^3*Q'^1 + 2*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 - 2*Q^2 - 1*Q^1*Q'^3 + 2*Q^1 + 2*Q'^3 - 2*Q'^2 + 2*Q'^1 - 2), (2*Q^3*Q'^3 - 1*Q^3*Q'^2 - 2*Q^3 - 1*Q^2*Q'^3 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 2), (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 2*Q^3*Q'^1 + 3*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 + 2*Q^2*Q'^1 - 1*Q^2 - 2*Q^1*Q'^3 + 2*Q^1*Q'^2 - 2*Q^1*Q'^1 + 2*Q^1 + 3*Q'^3 - 1*Q'^2 + 2*Q'^1 - 2)]

noncomputable def T0 : Matrix (Fin 4) (Fin 4) ℝ := !![(399/100:ℝ), (0:ℝ), (0:ℝ), (3:ℝ); (0:ℝ), (427/100:ℝ), (22/25:ℝ), (11/50:ℝ); (0:ℝ), (22/25:ℝ), (126/25:ℝ), (47/25:ℝ); (3:ℝ), (11/50:ℝ), (47/25:ℝ), (317/50:ℝ)]

/-- Enclosure of the real root of `x³ − x − 1`. -/
theorem rho_encl (ρ : ℝ) (h : ρ ^ 3 = ρ + 1) (h1 : 1 < ρ) :
    (13247/10000 : ℝ) < ρ ∧ ρ < 13248/10000 := by
  constructor
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ ρ^2 + ρ * (13247/10000) + (13247/10000)^2 - 1 by nlinarith)]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ ρ^2 + ρ * (13248/10000) + (13248/10000)^2 - 1 by nlinarith)]

/-- **Cubic side.** `S − S₀ ⪰ 0`. -/
theorem cubic_side (ρ : ℝ) (h : ρ ^ 3 = ρ + 1) (h1 : 1 < ρ) (v : Fin 3 → ℝ) :
    0 ≤ v ⬝ᵥ ((Smat ρ - S0) *ᵥ v) := by
  obtain ⟨hlo, hhi⟩ := rho_encl ρ h h1
  have ha : (1449/100000 : ℝ) ≤ 3*ρ^2 - 2 - 325/100 := by nlinarith
  have hc : (927/100000 : ℝ) ≤ -ρ^2 + 3*ρ + 2 - 421/100 := by nlinarith
  have hb1 : (0:ℝ) ≤ ρ - 132/100 := by linarith
  have hb2 : ρ - 132/100 ≤ (48/10000 : ℝ) := by linarith
  set a := 3*ρ^2 - 2 - 325/100 with ha_def
  set c := -ρ^2 + 3*ρ + 2 - 421/100 with hc_def
  set b := ρ - 132/100 with hb_def
  have hdet : 0 ≤ a * c - b ^ 2 := by
    nlinarith [mul_le_mul ha hc (by norm_num) (by linarith), mul_le_mul hb2 hb2 hb1 (by norm_num)]
  have hapos : 0 < a := by linarith
  have key : 0 ≤ a * (a * v 1 ^ 2 + 2 * b * v 1 * v 2 + c * v 2 ^ 2) := by
    nlinarith [sq_nonneg (a * v 1 + b * v 2), mul_nonneg hdet (sq_nonneg (v 2))]
  have q2 : 0 ≤ a * v 1 ^ 2 + 2 * b * v 1 * v 2 + c * v 2 ^ 2 :=
    (mul_nonneg_iff_of_pos_left hapos).mp key
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Smat, S0, Matrix.sub_apply,
    of_apply, cons_val', cons_val_zero, cons_val_succ, empty_val', cons_val_fin_one,
    cons_val_one, cons_val_two, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  rw [ha_def, hb_def, hc_def] at q2
  nlinarith [q2, sq_nonneg (v 0)]

/-- `S₀ ⪰ 0` (rational LDLᵀ). -/
theorem S0_psd (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ (S0 *ᵥ v) := by
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, S0,
    of_apply, cons_val', cons_val_zero, cons_val_succ, empty_val', cons_val_fin_one,
    cons_val_one, cons_val_two, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  linarith [mul_nonneg (show (0:ℝ) ≤ (299:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (200/299:ℝ)*v 2)), mul_nonneg (show (0:ℝ) ≤ (325:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (132/325:ℝ)*v 2)), mul_nonneg (show (0:ℝ) ≤ (1746223/7475:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2))]

/-- `T₀ ⪰ 0` (rational LDLᵀ). -/
theorem T0_psd (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ (T0 *ᵥ v) := by
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, T0,
    of_apply, cons_val', cons_val_zero, cons_val_succ, empty_val', cons_val_fin_one,
    cons_val_one, cons_val_two, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  linarith [mul_nonneg (show (0:ℝ) ≤ (399:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (100/133:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (427:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (88/427:ℝ)*v 2 + (22/427:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (207464/427:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2 + (19585/51866:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (1165876288/3449089:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 3))]

/-- The second real root lies on the cubic cofactor. -/
theorem Qprime_cubic (Q Q' : ℝ) (hQ : Q ^ 4 = Q + 1) (hQ' : Q' ^ 4 = Q' + 1) (hne : Q ≠ Q') :
    Q' ^ 3 + Q * Q' ^ 2 + Q ^ 2 * Q' + Q ^ 3 - 1 = 0 := by
  have hsub : Q - Q' ≠ 0 := sub_ne_zero.2 hne
  have : (Q - Q') * (Q' ^ 3 + Q * Q' ^ 2 + Q ^ 2 * Q' + Q ^ 3 - 1) = 0 := by
    linear_combination hQ - hQ'
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hsub
  · exact h

/-- Enclosures of the two real roots of `x⁴ − x − 1`. -/
theorem Q_encl (Q : ℝ) (hQ : Q ^ 4 = Q + 1) (h1 : 1 < Q) :
    (1220744/1000000 : ℝ) < Q ∧ Q < 1220745/1000000 := by
  constructor
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ Q^3 + Q^2 * (1220744/1000000) + Q * (1220744/1000000)^2 + (1220744/1000000)^3 - 1 by nlinarith)]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ Q^3 + Q^2 * (1220745/1000000) + Q * (1220745/1000000)^2 + (1220745/1000000)^3 - 1 by nlinarith)]

theorem Qp_encl (Q' : ℝ) (hQ' : Q' ^ 4 = Q' + 1) (h0 : Q' < 0) :
    (-724492/1000000 : ℝ) < Q' ∧ Q' < -724491/1000000 := by
  constructor
  · by_contra hc; push Not at hc
    -- Q' ≤ pa < 0: x⁴ − x − 1 is decreasing on (−∞, 0]
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ -(Q'^3 + Q'^2 * (-724492/1000000) + Q' * (-724492/1000000)^2 + (-724492/1000000)^3 - 1) by nlinarith [mul_nonneg (neg_nonneg.2 h0.le) (sq_nonneg Q'), sq_nonneg Q', h0])]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ -(Q'^3 + Q'^2 * (-724491/1000000) + Q' * (-724491/1000000)^2 + (-724491/1000000)^3 - 1) by nlinarith [mul_nonneg (neg_nonneg.2 h0.le) (sq_nonneg Q'), sq_nonneg Q', h0])]

set_option maxHeartbeats 4000000 in
/-- **Quartic side.** `T − T₀ ⪰ 0`. -/
theorem quartic_side (Q Q' : ℝ) (hQ : Q ^ 4 = Q + 1) (h1 : 1 < Q)
    (hQ' : Q' ^ 4 = Q' + 1) (h0 : Q' < 0) (v : Fin 4 → ℝ) :
    0 ≤ v ⬝ᵥ ((Tmat Q Q' - T0) *ᵥ v) := by
  obtain ⟨hQlo, hQhi⟩ := Q_encl Q hQ h1
  obtain ⟨hPlo, hPhi⟩ := Qp_encl Q' hQ' h0
  have hA1 : (152593/125000:ℝ) ≤ Q^1 ∧ Q^1 ≤ (244149/200000:ℝ) := by
    constructor <;> nlinarith [hQlo, hQhi]
  have hA2 : (23284623649/15625000000:ℝ) ≤ Q^2 ∧ Q^2 ≤ (59608734201/40000000000:ℝ) := by
    constructor <;> nlinarith [hQlo, hQhi, hA1.1, hA1.2, mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hQlo.le), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hQhi.le), mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hQhi.le), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hQlo.le)]
  have hA3 : (3553070576471857/1953125000000000:ℝ) ≤ Q^3 ∧ Q^3 ≤ (14553412846439949/8000000000000000:ℝ) := by
    constructor <;> nlinarith [hQlo, hQhi, hA2.1, hA2.2, mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hQlo.le), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hQhi.le), mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hQhi.le), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hQlo.le)]
  have hB1 : (-181123/250000:ℝ) ≤ Q'^1 ∧ Q'^1 ≤ (-724491/1000000:ℝ) := by
    constructor <;> nlinarith [hPlo, hPhi]
  have hB2 : (524887209081/1000000000000:ℝ) ≤ Q'^2 ∧ Q'^2 ≤ (32805541129/62500000000:ℝ) := by
    constructor <;> nlinarith [hPlo, hPhi, hB1.1, hB1.2, mul_nonneg (sub_nonneg.2 hB1.1) (neg_nonneg.2 h0.le), mul_nonneg (sub_nonneg.2 hB1.2) (neg_nonneg.2 h0.le), mul_nonneg (sub_nonneg.2 hB1.1) (sub_nonneg.2 hPlo.le), mul_nonneg (sub_nonneg.2 hB1.2) (sub_nonneg.2 hPhi.le), mul_nonneg (sub_nonneg.2 hB1.1) (sub_nonneg.2 hPhi.le), mul_nonneg (sub_nonneg.2 hB1.2) (sub_nonneg.2 hPlo.le)]
  have hB3 : (-5941838025907867/15625000000000000:ℝ) ≤ Q'^3 ∧ Q'^3 ≤ (-380276058994302771/1000000000000000000:ℝ) := by
    constructor <;> nlinarith [hPlo, hPhi, hB2.1, hB2.2, mul_nonneg (sub_nonneg.2 hB2.1) (neg_nonneg.2 h0.le), mul_nonneg (sub_nonneg.2 hB2.2) (neg_nonneg.2 h0.le), mul_nonneg (sub_nonneg.2 hB2.1) (sub_nonneg.2 hPlo.le), mul_nonneg (sub_nonneg.2 hB2.2) (sub_nonneg.2 hPhi.le), mul_nonneg (sub_nonneg.2 hB2.1) (sub_nonneg.2 hPhi.le), mul_nonneg (sub_nonneg.2 hB2.2) (sub_nonneg.2 hPlo.le)]
  have hM11 : (-44220999327/50000000000:ℝ) ≤ Q^1 * Q'^1 ∧ Q^1 * Q'^1 ≤ (-110552255163/125000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hB1.1), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hB1.2), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hB1.1), mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hB1.2), hA1.1, hA1.2, hB1.1, hB1.2]
  have hM12 : (80094113895297033/125000000000000000:ℝ) ≤ Q^1 * Q'^2 ∧ Q^1 * Q'^2 ≤ (8009440061104221/12500000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hB2.1), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hB2.2), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hB2.1), mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hB2.2), hA1.1, hA1.2, hB2.1, hB2.2]
  have hM13 : (-1450693812187379820183/3125000000000000000000:ℝ) ≤ Q^1 * Q'^3 ∧ Q^1 * Q'^3 ≤ (-58027464670117642735203/125000000000000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hB3.1), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hB3.2), mul_nonneg (sub_nonneg.2 hA1.2) (sub_nonneg.2 hB3.1), mul_nonneg (sub_nonneg.2 hA1.1) (sub_nonneg.2 hB3.2), hA1.1, hA1.2, hB3.1, hB3.2]
  have hM21 : (-10796512764687723/10000000000000000:ℝ) ≤ Q^2 * Q'^1 ∧ Q^2 * Q'^1 ≤ (-16869500272087659/15625000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hB1.1), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hB1.2), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hB1.1), mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hB1.2), hA2.1, hA2.2, hB1.1, hB1.2]
  have hM22 : (12221801121625060156569/15625000000000000000000:ℝ) ≤ Q^2 * Q'^2 ∧ Q^2 * Q'^2 ≤ (1955496781478534452929/2500000000000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hB2.1), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hB2.2), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hB2.1), mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hB2.2), hA2.1, hA2.2, hB2.1, hB2.2]
  have hM23 : (-354185443551736595717859267/625000000000000000000000000:ℝ) ≤ Q^2 * Q'^3 ∧ Q^2 * Q'^3 ≤ (-8854584916407261457892831379/15625000000000000000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hB3.1), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hB3.2), mul_nonneg (sub_nonneg.2 hA2.2) (sub_nonneg.2 hB3.1), mul_nonneg (sub_nonneg.2 hA2.1) (sub_nonneg.2 hB3.2), hA2.1, hA2.2, hB3.1, hB3.2]
  have hM31 : (-2635957794985742882727/2000000000000000000000:ℝ) ≤ Q^3 * Q'^1 ∧ Q^3 * Q'^1 ≤ (-2574167655018672149787/1953125000000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA3.1) (sub_nonneg.2 hB1.1), mul_nonneg (sub_nonneg.2 hA3.2) (sub_nonneg.2 hB1.2), mul_nonneg (sub_nonneg.2 hA3.2) (sub_nonneg.2 hB1.1), mul_nonneg (sub_nonneg.2 hA3.1) (sub_nonneg.2 hB1.2), hA3.1, hA3.2, hB1.1, hB1.2]
  have hM32 : (1864961298552132804471333417/1953125000000000000000000000:ℝ) ≤ Q^3 * Q'^2 ∧ Q^3 * Q'^2 ≤ (477432583701202708148162421/500000000000000000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA3.1) (sub_nonneg.2 hB2.1), mul_nonneg (sub_nonneg.2 hA3.2) (sub_nonneg.2 hB2.2), mul_nonneg (sub_nonneg.2 hA3.2) (sub_nonneg.2 hB2.1), mul_nonneg (sub_nonneg.2 hA3.1) (sub_nonneg.2 hB2.2), hA3.1, hA3.2, hB2.1, hB2.2]
  have hM33 : (-86474021857712938107919622178783/125000000000000000000000000000000:ℝ) ≤ Q^3 * Q'^3 ∧ Q^3 * Q'^3 ≤ (-1351147676149333247644240818615747/1953125000000000000000000000000000:ℝ) := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hA3.1) (sub_nonneg.2 hB3.1), mul_nonneg (sub_nonneg.2 hA3.2) (sub_nonneg.2 hB3.2), mul_nonneg (sub_nonneg.2 hA3.2) (sub_nonneg.2 hB3.1), mul_nonneg (sub_nonneg.2 hA3.1) (sub_nonneg.2 hB3.2), hA3.1, hA3.2, hB3.1, hB3.2]
  have hT00 : (39999/10000:ℝ) ≤ (4) ∧ (4) ≤ (40001/10000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT01 : (-1/10000:ℝ) ≤ (0) ∧ (0) ≤ (1/10000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT02 : (-103/1000000:ℝ) ≤ (2*Q^3*Q'^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*Q'^1 - 2*Q'^3 + 2*Q'^2 + 2) ∧ (2*Q^3*Q'^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*Q'^1 - 2*Q'^3 + 2*Q'^2 + 2) ≤ (97/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT03 : (1499947/500000:ℝ) ≤ (-3*Q^3 - 3*Q^2*Q'^1 - 3*Q^1*Q'^2 - 3*Q'^3 + 6) ∧ (-3*Q^3 - 3*Q^2*Q'^1 - 3*Q^1*Q'^2 - 3*Q'^3 + 6) ≤ (1500047/500000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT10 : (-1/10000:ℝ) ≤ (0) ∧ (0) ≤ (1/10000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT11 : (213819/50000:ℝ) ≤ (-2*Q^3*Q'^3 + 2*Q^3 + 1*Q^2 + 2*Q'^3 + 1*Q'^2 - 2) ∧ (-2*Q^3*Q'^3 + 2*Q^3 + 1*Q^2 + 2*Q'^3 + 1*Q'^2 - 2) ≤ (213829/50000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT12 : (175539/200000:ℝ) ≤ (2*Q^3 + 2*Q'^3 - 2) ∧ (2*Q^3 + 2*Q'^3 - 2) ≤ (175579/200000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT13 : (217709/1000000:ℝ) ≤ (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 1*Q^3*Q'^1 + 2*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 - 2*Q^2 - 1*Q^1*Q'^3 + 2*Q^1 + 2*Q'^3 - 2*Q'^2 + 2*Q'^1 - 2) ∧ (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 1*Q^3*Q'^1 + 2*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 - 2*Q^2 - 1*Q^1*Q'^3 + 2*Q^1 + 2*Q'^3 - 2*Q'^2 + 2*Q'^1 - 2) ≤ (217909/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT20 : (-103/1000000:ℝ) ≤ (2*Q^3*Q'^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*Q'^1 - 2*Q'^3 + 2*Q'^2 + 2) ∧ (2*Q^3*Q'^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*Q'^1 - 2*Q'^3 + 2*Q'^2 + 2) ≤ (97/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT21 : (175539/200000:ℝ) ≤ (2*Q^3 + 2*Q'^3 - 2) ∧ (2*Q^3 + 2*Q'^3 - 2) ≤ (175579/200000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT22 : (5053047/1000000:ℝ) ≤ (2*Q^3*Q'^3 - 2*Q^3*Q'^2 - 2*Q^3 - 2*Q^2*Q'^3 + 2*Q^2*Q'^2 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 4) ∧ (2*Q^3*Q'^3 - 2*Q^3*Q'^2 - 2*Q^3 - 2*Q^2*Q'^3 + 2*Q^2*Q'^2 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 4) ≤ (5053247/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT23 : (1876821/1000000:ℝ) ≤ (2*Q^3*Q'^3 - 1*Q^3*Q'^2 - 2*Q^3 - 1*Q^2*Q'^3 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 2) ∧ (2*Q^3*Q'^3 - 1*Q^3*Q'^2 - 2*Q^3 - 1*Q^2*Q'^3 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 2) ≤ (1877021/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT30 : (1499947/500000:ℝ) ≤ (-3*Q^3 - 3*Q^2*Q'^1 - 3*Q^1*Q'^2 - 3*Q'^3 + 6) ∧ (-3*Q^3 - 3*Q^2*Q'^1 - 3*Q^1*Q'^2 - 3*Q'^3 + 6) ≤ (1500047/500000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT31 : (217709/1000000:ℝ) ≤ (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 1*Q^3*Q'^1 + 2*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 - 2*Q^2 - 1*Q^1*Q'^3 + 2*Q^1 + 2*Q'^3 - 2*Q'^2 + 2*Q'^1 - 2) ∧ (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 1*Q^3*Q'^1 + 2*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 - 2*Q^2 - 1*Q^1*Q'^3 + 2*Q^1 + 2*Q'^3 - 2*Q'^2 + 2*Q'^1 - 2) ≤ (217909/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT32 : (1876821/1000000:ℝ) ≤ (2*Q^3*Q'^3 - 1*Q^3*Q'^2 - 2*Q^3 - 1*Q^2*Q'^3 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 2) ∧ (2*Q^3*Q'^3 - 1*Q^3*Q'^2 - 2*Q^3 - 1*Q^2*Q'^3 + 2*Q^2 + 1*Q^1 - 2*Q'^3 + 2*Q'^2 + 1*Q'^1 + 2) ≤ (1877021/1000000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  have hT33 : (1586239/250000:ℝ) ≤ (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 2*Q^3*Q'^1 + 3*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 + 2*Q^2*Q'^1 - 1*Q^2 - 2*Q^1*Q'^3 + 2*Q^1*Q'^2 - 2*Q^1*Q'^1 + 2*Q^1 + 3*Q'^3 - 1*Q'^2 + 2*Q'^1 - 2) ∧ (-2*Q^3*Q'^3 + 2*Q^3*Q'^2 - 2*Q^3*Q'^1 + 3*Q^3 + 2*Q^2*Q'^3 - 2*Q^2*Q'^2 + 2*Q^2*Q'^1 - 1*Q^2 - 2*Q^1*Q'^3 + 2*Q^1*Q'^2 - 2*Q^1*Q'^1 + 2*Q^1 + 3*Q'^3 - 1*Q'^2 + 2*Q'^1 - 2) ≤ (1586289/250000:ℝ) := by
    constructor <;> linarith [hM11.1, hM11.2, hM12.1, hM12.2, hM13.1, hM13.2, hM21.1, hM21.2, hM22.1, hM22.2, hM23.1, hM23.2, hM31.1, hM31.2, hM32.1, hM32.2, hM33.1, hM33.2, hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2]
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.sum_univ_zero, Tmat, T0, Matrix.sub_apply,
    of_apply, cons_val', cons_val_zero, cons_val_succ, empty_val', cons_val_fin_one,
    cons_val_one, cons_val_two, cons_val_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  linarith [mul_nonneg (show (0:ℝ) ≤ (9/1000:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-1/3000:ℝ)*v 2 + (-1/1500:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (137/25000:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (-441/1096:ℝ)*v 2 + (-2191/5480:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (771294119/68500000000:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2 + (-542602149/1542588238:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (110255771026161/61703529520000000:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 3)), mul_nonneg (sub_nonneg.2 (hT00).1) (sq_nonneg (v 0 + v 0)), mul_nonneg (sub_nonneg.2 (hT00).2) (sq_nonneg (v 0 - v 0)), mul_nonneg (sub_nonneg.2 (hT01).1) (sq_nonneg (v 0 + v 1)), mul_nonneg (sub_nonneg.2 (hT01).2) (sq_nonneg (v 0 - v 1)), mul_nonneg (sub_nonneg.2 (hT02).1) (sq_nonneg (v 0 + v 2)), mul_nonneg (sub_nonneg.2 (hT02).2) (sq_nonneg (v 0 - v 2)), mul_nonneg (sub_nonneg.2 (hT03).1) (sq_nonneg (v 0 + v 3)), mul_nonneg (sub_nonneg.2 (hT03).2) (sq_nonneg (v 0 - v 3)), mul_nonneg (sub_nonneg.2 (hT10).1) (sq_nonneg (v 1 + v 0)), mul_nonneg (sub_nonneg.2 (hT10).2) (sq_nonneg (v 1 - v 0)), mul_nonneg (sub_nonneg.2 (hT11).1) (sq_nonneg (v 1 + v 1)), mul_nonneg (sub_nonneg.2 (hT11).2) (sq_nonneg (v 1 - v 1)), mul_nonneg (sub_nonneg.2 (hT12).1) (sq_nonneg (v 1 + v 2)), mul_nonneg (sub_nonneg.2 (hT12).2) (sq_nonneg (v 1 - v 2)), mul_nonneg (sub_nonneg.2 (hT13).1) (sq_nonneg (v 1 + v 3)), mul_nonneg (sub_nonneg.2 (hT13).2) (sq_nonneg (v 1 - v 3)), mul_nonneg (sub_nonneg.2 (hT20).1) (sq_nonneg (v 2 + v 0)), mul_nonneg (sub_nonneg.2 (hT20).2) (sq_nonneg (v 2 - v 0)), mul_nonneg (sub_nonneg.2 (hT21).1) (sq_nonneg (v 2 + v 1)), mul_nonneg (sub_nonneg.2 (hT21).2) (sq_nonneg (v 2 - v 1)), mul_nonneg (sub_nonneg.2 (hT22).1) (sq_nonneg (v 2 + v 2)), mul_nonneg (sub_nonneg.2 (hT22).2) (sq_nonneg (v 2 - v 2)), mul_nonneg (sub_nonneg.2 (hT23).1) (sq_nonneg (v 2 + v 3)), mul_nonneg (sub_nonneg.2 (hT23).2) (sq_nonneg (v 2 - v 3)), mul_nonneg (sub_nonneg.2 (hT30).1) (sq_nonneg (v 3 + v 0)), mul_nonneg (sub_nonneg.2 (hT30).2) (sq_nonneg (v 3 - v 0)), mul_nonneg (sub_nonneg.2 (hT31).1) (sq_nonneg (v 3 + v 1)), mul_nonneg (sub_nonneg.2 (hT31).2) (sq_nonneg (v 3 - v 1)), mul_nonneg (sub_nonneg.2 (hT32).1) (sq_nonneg (v 3 + v 2)), mul_nonneg (sub_nonneg.2 (hT32).2) (sq_nonneg (v 3 - v 2)), mul_nonneg (sub_nonneg.2 (hT33).1) (sq_nonneg (v 3 + v 3)), mul_nonneg (sub_nonneg.2 (hT33).2) (sq_nonneg (v 3 - v 3)), sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]

end RulerSelection.GramCert
