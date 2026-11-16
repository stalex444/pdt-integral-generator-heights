module

public import RulerSelection.GramCert

/-!
# The threshold step `H(ρQ)² + 11 < 24.03`, with `H(ρQ)` in the closed form `ρ²Q²/|Q'|`.
(That `H(ρQ)` equals this closed form is NOT proved here — bridge B2 territory.)
-/

@[expose] public section

namespace RulerSelection.GramCert

/-- Six-digit enclosure of the real root of `x³ − x − 1`. -/
theorem rho_encl6 (ρ : ℝ) (h : ρ ^ 3 = ρ + 1) (h1 : 1 < ρ) :
    (1324717/1000000 : ℝ) < ρ ∧ ρ < 1324718/1000000 := by
  constructor
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ ρ^2 + ρ * (1324717/1000000) + (1324717/1000000)^2 - 1 by nlinarith)]
  · by_contra hc; push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℝ) ≤ ρ^2 + ρ * (1324718/1000000) + (1324718/1000000)^2 - 1 by nlinarith)]

/-- **Threshold.** `(ρ²Q²/|Q'|)² + 11 < 2403/100`. -/
theorem threshold (ρ Q Q' : ℝ) (hρ : ρ ^ 3 = ρ + 1) (hρ1 : 1 < ρ)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q) (hQ' : Q' ^ 4 = Q' + 1) (h0 : Q' < 0) :
    (ρ ^ 2 * Q ^ 2 / (-Q')) ^ 2 + 11 < 2403 / 100 := by
  obtain ⟨hrlo, hrhi⟩ := rho_encl6 ρ hρ hρ1
  obtain ⟨hqlo, hqhi⟩ := Q_encl Q hQ hQ1
  obtain ⟨hplo, hphi⟩ := Qp_encl Q' hQ' h0
  have hY : (724491/1000000 : ℝ) ^ 2 < Q' ^ 2 := by nlinarith
  have hr2 : ρ ^ 2 < (1324718/1000000 : ℝ) ^ 2 := pow_lt_pow_left₀ hrhi (by linarith) two_ne_zero
  have hq2 : Q ^ 2 < (1220745/1000000 : ℝ) ^ 2 := pow_lt_pow_left₀ hqhi (by linarith) two_ne_zero
  have hX0 : ρ ^ 2 * Q ^ 2 < (1324718/1000000 : ℝ) ^ 2 * (1220745/1000000) ^ 2 :=
    mul_lt_mul'' hr2 hq2 (by positivity) (by positivity)
  have hX : (ρ ^ 2 * Q ^ 2) ^ 2 < ((1324718/1000000 : ℝ) ^ 2 * (1220745/1000000) ^ 2) ^ 2 :=
    pow_lt_pow_left₀ hX0 (by positivity) two_ne_zero
  have hH : (ρ ^ 2 * Q ^ 2 / (-Q')) ^ 2 = (ρ ^ 2 * Q ^ 2) ^ 2 / Q' ^ 2 := by
    rw [div_pow, neg_sq]
  have hYpos : 0 < Q' ^ 2 := by positivity
  have key : (ρ ^ 2 * Q ^ 2) ^ 2 / Q' ^ 2 < 2403 / 100 - 11 := by
    rw [div_lt_iff₀ hYpos]
    nlinarith
  rw [hH]; linarith

end RulerSelection.GramCert
