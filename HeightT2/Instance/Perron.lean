module

public import Mathlib
public import HeightT2.Defs
public import HeightT2.Instance.Generators

/-!
# The Perron selection among integral generators of `L = ℚ(ρ, Q)`

`M(x)` is the Mahler measure of `minpoly ℤ x`, mapped to `ℂ[X]`.

* `perronAt_generator_selection` : an algebraic integer `x ∈ 𝓞 L` generating `L`, of least
  Mahler measure among algebraic integers generating `L`, at which some real image above `1`
  strictly exceeds every other image in modulus (`IsPerronAt`), is `ρQ`.
* `isPerronAt_iff_isPerronNumber` : for an integral generator `x` of `L`, `IsPerronAt x` holds
  exactly when some embedding sends `x` to a real Perron number (`IsPerronNumber`).
* `perronNumber_generator_selection` : the selection with `IsPerronNumber`.
* `perron_selection` : the two-way form.

Non-vacuity: `ρQ` satisfies the hypotheses of both selection statements. Control: the
Perron hypothesis cannot be dropped (`−ρQ` is an integral generator of least Mahler measure).
-/

@[expose] public section

open NumberField IntermediateField Polynomial

namespace HeightT2

noncomputable section

open RulerSelection.Emb RulerSelection.LaneC HermiteCompositum.Instance

/-- **Perron selection (embedding form).** An algebraic integer of `L` generating `L`, of least
Mahler measure among algebraic integers generating `L`, satisfying `IsPerronAt`, is `ρQ`. -/
theorem perronAt_generator_selection (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤)
    (hmin : ∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
      ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure)
    (hP : IsPerronAt (x : L)) : (x : L) = ρ * Q := by
  have h1 := hmin (ρQunit : 𝓞 L) ρQunit_top
  rw [ρQunit_coe] at h1
  have hm := (mahlerMeasure_generator_eq_iff x hx).1
    (le_antisymm h1 (mahlerMeasure_generator_ge x hx))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h | h | h | h
  · exact h
  · rw [h] at hP; exact absurd hP not_perron_neg_ρQ
  · rw [h] at hP; exact absurd hP not_perron_inv_ρQ
  · rw [h] at hP; exact absurd hP not_perron_neg_inv_ρQ

/-- **Non-vacuity.** `ρQ` satisfies the hypotheses of `perronAt_generator_selection`. -/
theorem ρQ_perronAt_generator_selected :
    ℚ⟮((ρQunit : 𝓞 L) : L)⟯ = ⊤ ∧
      (∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
        ((minpoly ℤ ((ρQunit : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
          ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure) ∧
      IsPerronAt ((ρQunit : 𝓞 L) : L) := by
  refine ⟨ρQunit_top, fun y hy => ?_, ?_⟩
  · rw [ρQunit_coe]; exact mahlerMeasure_generator_ge y hy
  · rw [ρQunit_coe]; exact ρQ_perron

/-- `−ρQ` as an element of `𝓞 L`. -/
def negρQ : 𝓞 L := -(ρQunit : 𝓞 L)

theorem negρQ_coe : (negρQ : L) = -(ρ * Q) := by
  rw [negρQ, RingOfIntegers.coe_eq_algebraMap, map_neg, ← RingOfIntegers.coe_eq_algebraMap,
    ρQunit_coe]

theorem negρQ_top : ℚ⟮(negρQ : L)⟯ = ⊤ := by
  rw [eq_top_iff, ← HermiteCompositum.Assembly.adjoin_ρQ_eq_top, adjoin_simple_le_iff, negρQ_coe]
  convert neg_mem (mem_adjoin_simple_self ℚ (-(ρ * Q))) using 1
  rw [neg_neg]

/-- **Control (Perron hypothesis needed).** `−ρQ` is an algebraic integer generating `L`, of
least Mahler measure among those, and is not `ρQ`. -/
theorem control_perron_needed :
    ℚ⟮(negρQ : L)⟯ = ⊤ ∧
      (∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
        ((minpoly ℤ (negρQ : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
          ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure) ∧
      (negρQ : L) ≠ ρ * Q := by
  refine ⟨negρQ_top, fun y hy => ?_, ?_⟩
  · rw [(mahlerMeasure_generator_eq_iff _ negρQ_top).2 (by rw [negρQ_coe]; simp)]
    exact mahlerMeasure_generator_ge y hy
  · rw [negρQ_coe]
    intro h
    have h' := congrArg (φL (0, 0)) h
    simp only [map_neg, φL00_ρQ] at h'
    have := congrArg Complex.re h'
    simp only [Complex.neg_re, Complex.ofReal_re] at this
    linarith [one_lt_rhoR_mul_QR]

/-! ## The `IsPerronNumber` form -/

/-- The complex roots of `minpoly ℤ x`, for an integral generator `x` of `L`, are the twelve values
`σ x`, `σ : L →+* ℂ`, each once. -/
theorem aroots_minpoly_eq (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    (minpoly ℤ (x : L)).aroots ℂ =
      Multiset.map (fun σ : L →+* ℂ => σ (x : L)) Finset.univ.val := by
  have e := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe x)
  rw [aroots_def, ← roots_eq_embeddings _ hx, e, Polynomial.map_map]
  congr 2

/-- If an embedding sends `x ∈ L` to the real number `r`, then `r` and `x` have the same minimal
polynomial over `ℤ`. -/
theorem minpoly_real_eq (x : L) (σ : L →+* ℂ) (r : ℝ) (hσ : σ x = r) :
    minpoly ℤ r = minpoly ℤ x := by
  have h1 : minpoly ℤ ((r : ℂ)) = minpoly ℤ r :=
    minpoly.algHom_eq Complex.ofRealHom.toIntAlgHom Complex.ofReal_injective r
  have h2 : minpoly ℤ (σ x) = minpoly ℤ x :=
    minpoly.algHom_eq σ.toIntAlgHom σ.injective x
  rw [← h1, ← hσ, h2]

/-- **Bridge.** For an algebraic integer `x` generating `L`, `IsPerronAt x` holds exactly when some
embedding of `L` sends `x` to a real Perron number. -/
theorem isPerronAt_iff_isPerronNumber (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    IsPerronAt (x : L) ↔ ∃ σ : L →+* ℂ, ∃ r : ℝ, σ (x : L) = r ∧ IsPerronNumber r := by
  constructor
  · rintro ⟨σ, him, hre, hmax⟩
    have hσ : σ (x : L) = ((σ (x : L)).re : ℂ) := Complex.ext (by simp) (by simp [him])
    refine ⟨σ, (σ (x : L)).re, hσ, ?_, hre.le, fun z hz hne => ?_⟩
    · have hint : IsIntegral ℤ (σ (x : L)) :=
        (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
      rw [hσ] at hint
      exact (isIntegral_algHom_iff Complex.ofRealHom.toIntAlgHom Complex.ofReal_injective).1 hint
    · rw [minpoly_real_eq _ σ _ hσ, aroots_minpoly_eq x hx] at hz
      obtain ⟨τ, -, rfl⟩ := Multiset.mem_map.1 hz
      exact hmax τ (by rw [hσ]; exact hne)
  · rintro ⟨σ, r, hσ, hint, h1, hroots⟩
    rw [minpoly_real_eq _ σ r hσ, aroots_minpoly_eq x hx] at hroots
    have hr1 : r ≠ 1 := by
      rintro rfl
      have hx1 : (x : L) = 1 := σ.injective (by rw [hσ, map_one, Complex.ofReal_one])
      exact listed_small_not_top (x : L) (by rw [hx1]; simp) hx
    refine ⟨σ, by rw [hσ, Complex.ofReal_im],
      by rw [hσ, Complex.ofReal_re]; exact lt_of_le_of_ne h1 (Ne.symm hr1), fun τ hτ => ?_⟩
    rw [hσ, Complex.ofReal_re]
    exact hroots (τ (x : L)) (Multiset.mem_map.2 ⟨τ, Finset.mem_univ_val _, rfl⟩) (hσ ▸ hτ)

/-- **Perron selection (Perron-number form).** An algebraic integer of `L` generating `L`, of least
Mahler measure among algebraic integers generating `L`, that some embedding sends to a real Perron
number, is `ρQ`. -/
theorem perronNumber_generator_selection (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤)
    (hmin : ∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
      ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure)
    (hP : ∃ σ : L →+* ℂ, ∃ r : ℝ, σ (x : L) = r ∧ IsPerronNumber r) : (x : L) = ρ * Q :=
  perronAt_generator_selection x hx hmin ((isPerronAt_iff_isPerronNumber x hx).2 hP)

/-- **Non-vacuity.** `ρQ` satisfies the hypotheses of `perronNumber_generator_selection`. -/
theorem ρQ_perronNumber_generator_selected :
    ℚ⟮((ρQunit : 𝓞 L) : L)⟯ = ⊤ ∧
      (∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
        ((minpoly ℤ ((ρQunit : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
          ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure) ∧
      ∃ σ : L →+* ℂ, ∃ r : ℝ, σ ((ρQunit : 𝓞 L) : L) = r ∧ IsPerronNumber r := by
  obtain ⟨h1, h2, h3⟩ := ρQ_perronAt_generator_selected
  exact ⟨h1, h2, (isPerronAt_iff_isPerronNumber _ h1).1 h3⟩

/-- **Two-way form.** For an algebraic integer `x` generating `L`: `x` has least Mahler measure among
algebraic integers generating `L` and some embedding sends it to a real Perron number, if and only
if `x = ρQ`. -/
theorem perron_selection (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    ((∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
        ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
          ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure) ∧
      ∃ σ : L →+* ℂ, ∃ r : ℝ, σ (x : L) = r ∧ IsPerronNumber r) ↔ (x : L) = ρ * Q := by
  constructor
  · rintro ⟨hmin, hP⟩; exact perronNumber_generator_selection x hx hmin hP
  · intro hxe
    refine ⟨fun y hy => ?_, (isPerronAt_iff_isPerronNumber x hx).1 (by rw [hxe]; exact ρQ_perron)⟩
    rw [hxe]; exact mahlerMeasure_generator_ge y hy

end

end HeightT2
