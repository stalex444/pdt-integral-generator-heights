module

public import Mathlib
public import HeightT2.Equality
public import RulerSelection.Perron

/-!
# The equality case at a concrete element of `L = ℚ(ρ, Q)`

Here `ρ` and `Q` are the adjoined roots of `X³ − X − 1` and `X⁴ − X − 1`, and
`L = ℚ(ρ, Q)` has degree 12 over `ℚ`. The element `ρQ` is an algebraic integer with a real
conjugate greater than `1`, so it is not a root of unity, and the inequality
`T₂(ρQ) ≤ mulHeight₁(ρQ)² + 11` is strict (`control_strict_ρQ`).
-/

@[expose] public section

open NumberField HermiteCompositum.Instance RulerSelection.LaneC

namespace HeightT2

noncomputable section

/-- `ρQ` is not a root of unity. -/
theorem ρQ_not_root_of_unity : ¬ ∃ m : ℕ, 0 < m ∧ (ρ * Q : L) ^ m = 1 := by
  rintro ⟨m, hm, h⟩
  obtain ⟨σ, -, hre, -⟩ := ρQ_perron
  have h1 : ‖σ (ρ * Q)‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  have h2 : ‖σ (ρ * Q)‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h1
  have h3 : |(σ (ρ * Q)).re| ≤ ‖σ (ρ * Q)‖ := Complex.abs_re_le_norm _
  have h4 : (σ (ρ * Q)).re ≤ |(σ (ρ * Q)).re| := le_abs_self _
  linarith

/-- **Control (strict inequality at a concrete integer).** In `L`, at `x = ρQ` the inequality
`T₂(x) ≤ mulHeight₁(x)² + (12 − 1)` is strict. -/
theorem control_strict_ρQ :
    ∑ σ : L →+* ℂ, ‖σ (ρ * Q)‖ ^ 2 <
      Height.mulHeight₁ (ρ * Q) ^ 2 + ((Module.finrank ℚ L : ℝ) - 1) := by
  refine lt_of_le_of_ne (sum_norm_sq_le_mulHeight₁_sq_add _) ?_
  intro h
  exact ρQ_not_root_of_unity
    ((sum_norm_sq_eq_mulHeight₁_sq_add_iff (by rw [finrank_L]; norm_num) _).mp h)

end

end HeightT2
