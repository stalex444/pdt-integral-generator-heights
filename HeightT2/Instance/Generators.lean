module

public import Mathlib
public import RulerSelection.Perron

/-!
# Least Mahler measure among integral generators of `L = ℚ(ρ, Q)`

Here `ρ` and `Q` are the adjoined roots of `X³ − X − 1` and `X⁴ − X − 1`, and
`L = ℚ(ρ, Q)` has degree 12 over `ℚ`. For an algebraic integer `x` write
`M(x)` for the Mahler measure of `minpoly ℤ x`, mapped to `ℂ[X]`.

* `mahlerMeasure_generator_ge` : every algebraic integer `x ∈ 𝓞 L` with `ℚ⟮x⟯ = L` satisfies
  `M(ρQ) ≤ M(x)`.
* `mahlerMeasure_generator_eq_iff` : equality holds exactly for `x ∈ {ρQ, −ρQ, (ρQ)⁻¹, −(ρQ)⁻¹}`.
* `mahlerMeasure_generator_min` : the two together.

No unit hypothesis is made. Controls: the generator hypothesis cannot be dropped (`x = 1`),
the bound is attained (`x = ρQ`), and a non-unit integral generator (`x = 2ρQ`) lies strictly
above the minimum, so the statement covers non-units non-vacuously.
-/

@[expose] public section

open NumberField IntermediateField Polynomial

namespace HeightT2

noncomputable section

open RulerSelection.Emb RulerSelection.LaneC HermiteCompositum.Instance

/-- An element of `L` that generates `L` over `ℚ` is nonzero. -/
theorem ne_zero_of_adjoin_eq_top (x : L) (hx : ℚ⟮x⟯ = ⊤) : x ≠ 0 := by
  rintro rfl
  have h3 : Module.finrank ℚ S₃ < 12 := by rw [finrank_S₃]; norm_num
  exact not_top_of_mem S₃ h3 0 (zero_mem _) hx

/-- Height form: an integral generator of `L` has height at least `H(ρQ)`. -/
theorem embHeight_generator_ge (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    embHeight (ρ * Q) ≤ embHeight (x : L) := by
  have hx0 : x ≠ 0 := fun h => ne_zero_of_adjoin_eq_top _ hx (by simp [h])
  by_contra h
  push Not at h
  have hm := small_height x hx0 h.le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  rotate_left 10
  · rw [h1] at h; exact lt_irrefl _ h
  · rw [h1, embHeight_neg_ρQ] at h; exact lt_irrefl _ h
  · rw [h1, embHeight_ρQ_inv] at h; exact lt_irrefl _ h
  · rw [h1, embHeight_neg_ρQ_inv] at h; exact lt_irrefl _ h
  all_goals
    exact listed_small_not_top (x : L) (by rw [h1]; simp) hx

/-- Height form, equality case. -/
theorem embHeight_generator_eq_iff (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    embHeight (x : L) = embHeight (ρ * Q) ↔
      (x : L) ∈ ({ρ * Q, -(ρ * Q), (ρ * Q)⁻¹, -(ρ * Q)⁻¹} : Set L) := by
  have hx0 : x ≠ 0 := fun h => ne_zero_of_adjoin_eq_top _ hx (by simp [h])
  constructor
  · intro h
    have hm := small_height x hx0 h.le
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    rcases hm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    rotate_left 10
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
    all_goals
      exact absurd hx (listed_small_not_top (x : L) (by rw [h1]; simp))
  · intro hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [embHeight_neg_ρQ]
    · rw [embHeight_ρQ_inv]
    · rw [embHeight_neg_ρQ_inv]

/-- Every algebraic integer of `L` generating `L` over `ℚ` has Mahler measure at least that of
`ρQ`. -/
theorem mahlerMeasure_generator_ge (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
      ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [mahler_ρQ, mahler_eq_embHeight _ hx]; exact embHeight_generator_ge x hx

/-- Equality case: among algebraic integers of `L` generating `L`, the Mahler measure of `ρQ` is
attained exactly at `±(ρQ)^{±1}`. -/
theorem mahlerMeasure_generator_eq_iff (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure =
        ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ↔
      (x : L) ∈ ({ρ * Q, -(ρ * Q), (ρ * Q)⁻¹, -(ρ * Q)⁻¹} : Set L) := by
  rw [mahler_ρQ, mahler_eq_embHeight _ hx]; exact embHeight_generator_eq_iff x hx

/-- **Least Mahler measure among integral generators of `L`.** For every algebraic integer
`x ∈ 𝓞 L` with `ℚ⟮x⟯ = L`, `M(ρQ) ≤ M(x)`, with equality exactly when
`x ∈ {ρQ, −ρQ, (ρQ)⁻¹, −(ρQ)⁻¹}`. -/
theorem mahlerMeasure_generator_min (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure =
          ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ↔
        (x : L) ∈ ({ρ * Q, -(ρ * Q), (ρ * Q)⁻¹, -(ρ * Q)⁻¹} : Set L)) :=
  ⟨mahlerMeasure_generator_ge x hx, mahlerMeasure_generator_eq_iff x hx⟩

/-! ## Controls -/

/-- **Control (hypothesis needed).** Without `ℚ⟮x⟯ = L` the bound fails: `x = 1` has Mahler
measure `1 < M(ρQ)`. -/
theorem control_generator_needed :
    ((minpoly ℤ ((1 : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure <
      ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have h1 : ((1 : 𝓞 L) : L) = 1 := by simp
  have hm1 : minpoly ℤ (1 : L) = X - C 1 := by
    have := minpoly.eq_X_sub_C_of_algebraMap_inj (1 : ℤ) (algebraMap ℤ L).injective_int
    rwa [map_one] at this
  rw [h1, hm1, mahler_ρQ]
  have : (X - C 1 : ℤ[X]).map (Int.castRingHom ℂ) = X - C 1 := by simp
  rw [this, mahlerMeasure_X_sub_C, norm_one, max_self]
  exact one_lt_embHeight_ρQ

/-- **Control (attained).** `ρQ` is an integral generator of `L`, so the minimum is attained. -/
theorem control_generator_attained :
    ℚ⟮((ρQunit : 𝓞 L) : L)⟯ = ⊤ ∧
      ((minpoly ℤ ((ρQunit : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure =
        ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure :=
  ⟨ρQunit_top, by rw [ρQunit_coe]⟩

/-- `ρQ` as a real number is above `1` (its image at the real embedding `φL (0, 0)`). -/
theorem one_lt_rhoR_mul_QR : 1 < rhoR * QR := by nlinarith [rhoR_gt_one, QR_gt_one]

/-- `2ρQ` as an element of `𝓞 L`. -/
def twoρQ : 𝓞 L := 2 * (ρQunit : 𝓞 L)

theorem twoρQ_coe : (twoρQ : L) = 2 * (ρ * Q) := by
  rw [twoρQ, RingOfIntegers.coe_eq_algebraMap, map_mul, map_ofNat,
    ← RingOfIntegers.coe_eq_algebraMap, ρQunit_coe]

theorem twoρQ_top : ℚ⟮(twoρQ : L)⟯ = ⊤ := by
  rw [eq_top_iff, ← HermiteCompositum.Assembly.adjoin_ρQ_eq_top, adjoin_simple_le_iff, twoρQ_coe]
  have hmem := mul_mem (IntermediateField.algebraMap_mem ℚ⟮2 * (ρ * Q)⟯ (1 / 2 : ℚ))
    (mem_adjoin_simple_self ℚ (2 * (ρ * Q)))
  convert hmem using 1
  rw [map_div₀, map_one, map_ofNat]; ring

/-- `2ρQ` is not a unit of `𝓞 L`. -/
theorem twoρQ_not_isUnit : ¬ IsUnit twoρQ := by
  intro hu
  have h2 : IsUnit (2 : 𝓞 L) := isUnit_of_mul_isUnit_left hu
  obtain ⟨y, hy⟩ := h2.exists_right_inv
  have hyL : (y : L) = algebraMap ℚ L (1 / 2) := by
    have := congrArg (fun z : 𝓞 L => (z : L)) hy
    simp only [map_mul, map_ofNat, map_one] at this
    rw [map_div₀, map_one, map_ofNat]
    field_simp
    linear_combination this
  have hint : IsIntegral ℤ (algebraMap ℚ L (1 / 2)) := hyL ▸ RingOfIntegers.isIntegral_coe y
  rw [isIntegral_algebraMap_iff] at hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hn' : (2 * n : ℚ) = 1 := by
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]; norm_num
  have : (2 * n : ℤ) = 1 := by exact_mod_cast hn'
  omega

/-- **Control (non-units are covered).** `2ρQ` is an integral generator of `L`, is not a unit,
and its Mahler measure is strictly above `M(ρQ)`. -/
theorem control_nonunit_generator :
    ℚ⟮(twoρQ : L)⟯ = ⊤ ∧ ¬ IsUnit twoρQ ∧
      ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure <
        ((minpoly ℤ (twoρQ : L)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  refine ⟨twoρQ_top, twoρQ_not_isUnit, lt_of_le_of_ne (mahlerMeasure_generator_ge _ twoρQ_top) ?_⟩
  intro heq
  have hm := (mahlerMeasure_generator_eq_iff _ twoρQ_top).1 heq.symm
  rw [twoρQ_coe] at hm
  have hr := one_lt_rhoR_mul_QR
  have hr0 : 0 < rhoR * QR := by linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h | h | h | h <;>
  · have h' := congrArg (φL (0, 0)) h
    rw [map_mul (φL (0, 0)) (2 : L) (ρ * Q), map_ofNat] at h'
    simp only [map_neg, map_inv₀, φL00_ρQ] at h'
    norm_cast at h'
    have hi : 0 < (rhoR * QR)⁻¹ := inv_pos.2 hr0
    have hc : (rhoR * QR)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    nlinarith

end

end HeightT2
