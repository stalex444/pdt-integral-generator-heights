module
public import Mathlib
public import HeightT2.Instance.SmallHeight
public import HeightT2.Instance.Generators
public import HeightT2.Instance.Perron

@[expose] public section
/-!
# Solution

The three statements of `Challenge.lean`, stated identically, each proved by one `exact` of a theorem
of the proof modules: `HeightT2.Instance.SmallHeight` (1), `HeightT2.Instance.Generators` (2) and
`HeightT2.Instance.Perron` (3). The definitions the statements use are those of the imported
modules `HermiteCompositum.Defs` and `HeightT2.Defs`, whose text `Challenge.lean` carries.
This file is generated from `Challenge.lean` by `scripts/make_solution.py`.
-/

set_option autoImplicit false

open NumberField IntermediateField

namespace IntegralGeneratorHeights

open HermiteCompositum.Instance in
/-- **(1) The fourteen elements.** The nonzero algebraic integers `x` of `L` with
`mulHeight₁ x ≤ mulHeight₁ (ρQ)` are exactly `±1, ±ρ^{±1}, ±Q^{±1}, ±(ρQ)^{±1}`. -/
theorem mulHeight₁_le_mulHeight₁_ρQ_iff (x : 𝓞 L) (hx : x ≠ 0) :
    Height.mulHeight₁ (x : L) ≤ Height.mulHeight₁ (ρ * Q) ↔
      (x : L) ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
        -(ρ * Q)⁻¹} : Set L) := by
  exact HeightT2.mulHeight₁_le_mulHeight₁_ρQ_iff x hx

open HermiteCompositum.Instance in
/-- **(2) Least Mahler measure among the integral generators of `L`.** Every algebraic integer
`x` of `L` with `ℚ(x) = L` has `M(ρQ) ≤ M(x)`, with equality exactly when `x` is one of `ρQ`,
`−ρQ`, `(ρQ)⁻¹`, `−(ρQ)⁻¹`. -/
theorem mahlerMeasure_generator_min (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure =
          ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ↔
        (x : L) ∈ ({ρ * Q, -(ρ * Q), (ρ * Q)⁻¹, -(ρ * Q)⁻¹} : Set L)) := by
  exact HeightT2.mahlerMeasure_generator_min x hx

open HermiteCompositum.Instance in
/-- **(3) The Perron selection.** Let `x` be an algebraic integer of `L` with `ℚ(x) = L` such that
`M(x) ≤ M(y)` for every algebraic integer `y` of `L` with `ℚ(y) = L`, and such that `σ(x)` is a
real Perron number for some embedding `σ : L →+* ℂ`; then `x = ρQ`. One direction only: that `ρQ`
satisfies these hypotheses is proved in the repository
(`HeightT2.ρQ_perronNumber_generator_selected`) and not compared. -/
theorem perronNumber_generator_selection (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤)
    (hmin : ∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
      ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure)
    (hP : ∃ σ : L →+* ℂ, ∃ r : ℝ, σ (x : L) = r ∧ HeightT2.IsPerronNumber r) :
    (x : L) = ρ * Q := by
  exact HeightT2.perronNumber_generator_selection x hx hmin hP

end IntegralGeneratorHeights
