module

public import Mathlib
public import HeightT2.Bridge
public import RulerSelection.ControlsC
public import RulerSelection.Units

/-!
# The fourteen integers of small height in `L = ℚ(ρ, Q)`, in Mathlib's height

Here `ρ` and `Q` are the adjoined roots of `X³ − X − 1` and `X⁴ − X − 1`, and
`L = ℚ(ρ, Q)` has degree 12 over `ℚ`.

* `mulHeight₁_eq_embHeight` : on `𝓞 L`, `Height.mulHeight₁` equals the product
  `embHeight x = ∏ σ : L →+* ℂ, max 1 ‖σ x‖`.
* `mulHeight₁_ρQ` : `mulHeight₁ (ρQ) = embHeight (ρQ)`.
* `mulHeight₁_le_mulHeight₁_ρQ_iff` : a nonzero `x ∈ 𝓞 L` has `mulHeight₁ x ≤ mulHeight₁ (ρQ)`
  exactly when `x` is one of `±1, ±ρ^{±1}, ±Q^{±1}, ±(ρQ)^{±1}`.

Controls: the bound is attained (`x = ρQ`), and the integral element `ρ⁻¹Q`, outside the
list, has height strictly above `mulHeight₁ (ρQ)` (`control_mulHeight₁_excluded`).
-/

@[expose] public section

open NumberField

namespace HeightT2

noncomputable section

open RulerSelection.Emb RulerSelection.LaneC HermiteCompositum.Instance

/-- On algebraic integers of `L`, Mathlib's `mulHeight₁` is `embHeight`. -/
theorem mulHeight₁_eq_embHeight (x : 𝓞 L) : Height.mulHeight₁ (x : L) = embHeight (x : L) :=
  mulHeight₁_eq_prod_embeddings x

/-- `mulHeight₁ (ρQ) = embHeight (ρQ)`. -/
theorem mulHeight₁_ρQ : Height.mulHeight₁ (ρ * Q) = embHeight (ρ * Q) := by
  have h := mulHeight₁_eq_embHeight (ρQunit : 𝓞 L)
  rwa [ρQunit_coe] at h

/-- The nonzero algebraic integers `x` of `L` with `mulHeight₁ x ≤ mulHeight₁ (ρQ)` are exactly
the fourteen elements `±1, ±ρ^{±1}, ±Q^{±1}, ±(ρQ)^{±1}`. -/
theorem mulHeight₁_le_mulHeight₁_ρQ_iff (x : 𝓞 L) (hx : x ≠ 0) :
    Height.mulHeight₁ (x : L) ≤ Height.mulHeight₁ (ρ * Q) ↔
      (x : L) ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
        -(ρ * Q)⁻¹} : Set L) := by
  rw [mulHeight₁_eq_embHeight, mulHeight₁_ρQ]
  exact small_height_iff x hx

/-- **Control (bound attained).** `ρQ` is a nonzero algebraic integer of `L` at the bound. -/
theorem control_mulHeight₁_attained :
    ∃ x : 𝓞 L, x ≠ 0 ∧ (x : L) = ρ * Q ∧
      Height.mulHeight₁ (x : L) = Height.mulHeight₁ (ρ * Q) :=
  ⟨ρQunit, ρQunit.ne_zero, ρQunit_coe, by rw [ρQunit_coe]⟩

/-- **Control (an integer just outside).** The algebraic integer `ρ⁻¹Q` is not in the list and
its height exceeds `mulHeight₁ (ρQ)`. -/
theorem control_mulHeight₁_excluded :
    ∃ x : 𝓞 L, x ≠ 0 ∧ (x : L) = ρ⁻¹ * Q ∧
      (x : L) ∉ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
        -(ρ * Q)⁻¹} : Set L) ∧
      Height.mulHeight₁ (ρ * Q) < Height.mulHeight₁ (x : L) := by
  obtain ⟨x, hx0, hxv, hnot, hlt⟩ := control_ii
  exact ⟨x, hx0, hxv, hnot, by rw [mulHeight₁_eq_embHeight, mulHeight₁_ρQ]; exact hlt⟩

end

end HeightT2
