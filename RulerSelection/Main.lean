module

public import Mathlib
public import RulerSelection.RouteMLink

/-!
# C2. The main theorem (stage 2, lane C)

`small_height` : every nonzero `x ∈ 𝓞 L` with `H(x) ≤ H(ρQ)` is one of the fourteen elements
`±1, ±ρ^{±1}, ±Q^{±1}, ±(ρQ)^{±1}`, where `H(x) = ∏_{σ : L →+* ℂ} max 1 ‖σ x‖` (`embHeight`).

Assembly: lane B's `small_height_cases` (the fifteen listed points or one of the 56 of `rest56`),
C1's `rest56_excl` (each of the 56 has height `> H(ρQ)`), and `x ≠ 0` for the zero point.

`small_height_unit` (C3a) : the same for units.
-/

@[expose] public section

open NumberField

namespace RulerSelection.LaneC

noncomputable section

open RulerSelection.Emb RulerSelection.LaneB HermiteCompositum.Instance

/-- **C2. The selection theorem (small heights).** -/
theorem small_height (x : 𝓞 L) (hx : x ≠ 0) (hH : embHeight (x : L) ≤ embHeight (ρ * Q)) :
    (x : L) ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
      -(ρ * Q)⁻¹} : Set L) := by
  rw [RingOfIntegers.coe_eq_algebraMap] at hH ⊢
  rcases small_height_cases x hH with h | ⟨l, hl, hxl⟩
  · have h0 : algebraMap (𝓞 L) L x ≠ 0 := fun h => hx (RingOfIntegers.coe_eq_zero_iff.1 h)
    simp only [IsListed] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact absurd h h0
    all_goals (rw [h]; simp)
  · rw [hxl] at hH
    exact absurd hH (not_le.2 (rest56_excl l hl))

/-- **C3(a). Units.** -/
theorem small_height_unit (u : (𝓞 L)ˣ) (hH : embHeight ((u : 𝓞 L) : L) ≤ embHeight (ρ * Q)) :
    ((u : 𝓞 L) : L) ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
      -(ρ * Q)⁻¹} : Set L) :=
  small_height u u.ne_zero hH

end

end RulerSelection.LaneC
