module
public import Mathlib
public import HeightT2.Compositum
public import HeightT2.Instance.SmallHeight
public import HeightT2.Instance.Generators
public import HeightT2.Instance.Perron

@[expose] public section
/-!
# Solution

The five statements of `Challenge.lean`, stated identically, each proved by one `exact` of a theorem
of the proof modules: `HeightT2.Compositum` (1, 2), `HeightT2.Instance.SmallHeight` (3),
`HeightT2.Instance.Generators` (4) and `HeightT2.Instance.Perron` (5). The definitions the statements use are those of the imported
modules `HermiteCompositum.Defs` and `HeightT2.Defs`, whose text `Challenge.lean` carries.
This file is generated from `Challenge.lean` by `scripts/make_solution.py`.
-/

set_option autoImplicit false

open NumberField IntermediateField Matrix
open scoped Kronecker

namespace IntegralGeneratorHeights

/-- **(1) The Kronecker identity for `T₂`.** For linearly disjoint subfields `K₁`, `K₂` of a
number field `E` with `K₁ ⊔ K₂ = ⊤`, the `T₂` Gram matrix over `E` of the product family is the
Kronecker product of the `T₂` Gram matrices over `K₁` and `K₂`. -/
theorem t2Gram_compositum {E : Type*} [Field E] [NumberField E] {K₁ K₂ : IntermediateField ℚ E}
    {ι κ : Type*} (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (b : ι → K₁) (c : κ → K₂) :
    HeightT2.t2Gram (fun p : ι × κ => (b p.1 : E) * (c p.2 : E)) =
      HeightT2.t2Gram b ⊗ₖ HeightT2.t2Gram c := by
  exact HeightT2.t2Gram_compositum h₁ h₂ b c

/-- **(2) The coordinate bound.** In the setting of (1) with finite index sets, if `s, t ≥ 0` and
`Re G_b − s E_ii`, `Re G_c − t E_jj` are positive semidefinite, then every rational coefficient
vector `a` satisfies `s t a(i,j)² ≤ ∑_σ ‖σ (∑_p a_p b_{p.1} c_{p.2})‖²`. -/
theorem coord_sq_le_sum_norm_sq {E : Type*} [Field E] [NumberField E]
    {K₁ K₂ : IntermediateField ℚ E} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (b : ι → K₁) (c : κ → K₂)
    (i : ι) (j : κ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hb : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ ((HeightT2.t2GramRe b - diagonal (Pi.single i s)) *ᵥ v))
    (hc : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ ((HeightT2.t2GramRe c - diagonal (Pi.single j t)) *ᵥ w))
    (a : ι × κ → ℚ) :
    s * t * (a (i, j) : ℝ) ^ 2 ≤
      ∑ σ : E →+* ℂ, ‖σ (∑ p, (a p : E) * (b p.1 : E) * (c p.2 : E))‖ ^ 2 := by
  exact HeightT2.coord_sq_le_sum_norm_sq h₁ h₂ b c i j s t hs ht hb hc a

open HermiteCompositum.Instance in
/-- **(3) The fourteen elements.** The nonzero algebraic integers `x` of `L` with
`mulHeight₁ x ≤ mulHeight₁ (ρQ)` are exactly `±1, ±ρ^{±1}, ±Q^{±1}, ±(ρQ)^{±1}`. -/
theorem mulHeight₁_le_mulHeight₁_ρQ_iff (x : 𝓞 L) (hx : x ≠ 0) :
    Height.mulHeight₁ (x : L) ≤ Height.mulHeight₁ (ρ * Q) ↔
      (x : L) ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
        -(ρ * Q)⁻¹} : Set L) := by
  exact HeightT2.mulHeight₁_le_mulHeight₁_ρQ_iff x hx

open HermiteCompositum.Instance in
/-- **(4) Least Mahler measure among the integral generators of `L`.** Every algebraic integer
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
/-- **(5) The Perron selection.** An algebraic integer `x` of `L` with `ℚ(x) = L`, of least
Mahler measure among the algebraic integers generating `L`, that some embedding sends to a real
Perron number, is `ρQ`. -/
theorem perronNumber_generator_selection (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤)
    (hmin : ∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
      ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure)
    (hP : ∃ σ : L →+* ℂ, ∃ r : ℝ, σ (x : L) = r ∧ HeightT2.IsPerronNumber r) :
    (x : L) = ρ * Q := by
  exact HeightT2.perronNumber_generator_selection x hx hmin hP

end IntegralGeneratorHeights
