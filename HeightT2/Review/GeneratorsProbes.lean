module

public import Mathlib
public import HeightT2.Defs
public import HeightT2.Instance.Generators
public import HeightT2.Instance.Perron
public import RulerSelection.ControlsC

/-!
# Statement-review probes for the generator and Perron statements

Hypothesis-deletion witnesses and definition checks for `mahlerMeasure_generator_min`,
`perronAt_generator_selection` and `perronNumber_generator_selection`.

* `adjoin_eq_top_iff_natDegree` : for `x ∈ L`, `ℚ⟮x⟯ = ⊤` exactly when `x` has degree 12.
* `integrality_needed` : over `L` instead of `𝓞 L` the bound fails (`ρQ/2` generates `L`, is not
  integral, and `minpoly ℤ` of it is `0`).
* `hx_needed_perronAt`, `hx_needed_perronNumber` : `x = ρ` satisfies every hypothesis of the two
  selection statements except `ℚ⟮x⟯ = ⊤`, and is not `ρQ`.
* `hmin_needed` : `x = 2ρQ` satisfies every hypothesis except minimality, and is not `ρQ`.
* `aroots_minpoly_nodup` : the complex roots of the minimal polynomial of a real algebraic integer
  are simple, so `z ≠ r` in `IsPerronNumber` ranges over the other conjugates.
* `algEquiv_eq_refl` : `L` has no nontrivial `ℚ`-automorphism, so no conjugate of `ρQ` other than
  `ρQ` itself lies in `L`.
-/

@[expose] public section

open NumberField IntermediateField Polynomial

namespace HeightT2.Review

noncomputable section

open RulerSelection.Emb RulerSelection.LaneC HermiteCompositum.Instance HeightT2

/-! ## The generator hypothesis is the degree-12 condition -/

/-- For `x ∈ L`: `ℚ⟮x⟯ = ⊤` if and only if the minimal polynomial of `x` over `ℚ` has degree 12. -/
theorem adjoin_eq_top_iff_natDegree (x : L) :
    ℚ⟮x⟯ = ⊤ ↔ (minpoly ℚ x).natDegree = 12 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  rw [← adjoin.finrank hint]
  constructor
  · intro h; rw [h, finrank_top', finrank_L]
  · intro h
    exact eq_of_le_of_finrank_eq le_top (by rw [h, finrank_top', finrank_L])

/-! ## Integrality cannot be dropped from the bound -/

theorem half_ρQ_top : ℚ⟮((ρ * Q) / 2 : L)⟯ = ⊤ := by
  rw [eq_top_iff, ← HermiteCompositum.Assembly.adjoin_ρQ_eq_top, adjoin_simple_le_iff]
  have hmem := mul_mem (IntermediateField.algebraMap_mem ℚ⟮(ρ * Q) / 2⟯ (2 : ℚ))
    (mem_adjoin_simple_self ℚ ((ρ * Q) / 2))
  convert hmem using 1
  rw [map_ofNat]; ring

theorem half_ρQ_not_isIntegral : ¬ IsIntegral ℤ ((ρ * Q) / 2 : L) := by
  intro hint
  set u : 𝓞 L := ((ρQunit⁻¹ : (𝓞 L)ˣ) : 𝓞 L)
  have hu : (u : L) * (ρ * Q) = 1 := by
    have h := congrArg (algebraMap (𝓞 L) L) (Units.inv_mul ρQunit)
    rw [map_mul, map_one, ← RingOfIntegers.coe_eq_algebraMap,
      ← RingOfIntegers.coe_eq_algebraMap, ρQunit_coe] at h
    exact h
  have hprod : (ρ * Q) / 2 * (u : L) = algebraMap ℚ L (1 / 2) := by
    rw [map_div₀, map_one, map_ofNat]
    linear_combination hu / 2
  have hi : IsIntegral ℤ (algebraMap ℚ L (1 / 2)) :=
    hprod ▸ hint.mul (RingOfIntegers.isIntegral_coe u)
  rw [isIntegral_algebraMap_iff] at hi
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hn' : (2 * n : ℚ) = 1 := by
    rw [show (n : ℚ) = algebraMap ℤ ℚ n from rfl, hn]; norm_num
  have : (2 * n : ℤ) = 1 := by exact_mod_cast hn'
  omega

/-- **Probe (integrality needed).** Stated over `L` rather than `𝓞 L`, the bound of
`mahlerMeasure_generator_ge` fails: `ρQ/2` generates `L`, is not an algebraic integer, and the
Mahler measure of `minpoly ℤ (ρQ/2)` (which is `0`) is below `M(ρQ)`. -/
theorem integrality_needed :
    ℚ⟮((ρ * Q) / 2 : L)⟯ = ⊤ ∧ ¬ IsIntegral ℤ ((ρ * Q) / 2 : L) ∧
      ((minpoly ℤ ((ρ * Q) / 2 : L)).map (Int.castRingHom ℂ)).mahlerMeasure <
        ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  refine ⟨half_ρQ_top, half_ρQ_not_isIntegral, ?_⟩
  rw [minpoly.eq_zero half_ρQ_not_isIntegral, Polynomial.map_zero, mahlerMeasure_zero, mahler_ρQ]
  linarith [one_lt_embHeight_ρQ]

/-! ## `x = ρ`: every hypothesis of the selection statements except `ℚ⟮x⟯ = ⊤` -/

/-- A complex root of `X³ − X − 1` other than the real root has modulus below the real root. -/
theorem norm_lt_rhoR_of_root (z : ℂ) (hz : z ^ 3 - z - 1 = 0) (hne : z ≠ (rhoR : ℂ)) :
    ‖z‖ < rhoR := by
  have hr := rhoR_eq; have hlo := rhoR_lo
  have hrC : (rhoR : ℂ) ^ 3 = rhoR + 1 := by exact_mod_cast hr
  have hfac : (z - rhoR) * (z ^ 2 + rhoR * z + ((rhoR : ℂ) ^ 2 - 1)) = 0 := by
    linear_combination hz - hrC
  have hq : z ^ 2 + rhoR * z + ((rhoR : ℂ) ^ 2 - 1) = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hn : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h1 := congrArg Complex.re hq
  have h2 := congrArg Complex.im hq
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.one_re, Complex.zero_re, Complex.add_im, Complex.mul_im,
    Complex.sub_im, Complex.one_im, Complex.zero_im] at h1 h2
  have h2' : z.im * (2 * z.re + rhoR) = 0 := by linarith
  have hsq : ‖z‖ ^ 2 < rhoR ^ 2 := by
    rcases mul_eq_zero.1 h2' with hb | ha
    · rw [hb] at h1
      nlinarith [sq_nonneg (z.re + rhoR / 2)]
    · have ha' : z.re = -rhoR / 2 := by linarith
      rw [hn]
      rw [ha'] at h1
      nlinarith
  nlinarith [norm_nonneg z, rhoR_gt_one]

theorem ρ_cube_sub : ρ ^ 3 - ρ - 1 = 0 := by
  have h := aeval_ρ
  simpa [HermiteCompositum.Port014.fρ] using h

theorem φL00_ρ : φL (0, 0) ρ = (rhoR : ℂ) := by
  rw [φL_ρ]; rfl

/-- `ρ` satisfies `IsPerronAt` (at its real embedding). -/
theorem ρ_perronAt : IsPerronAt ρ := by
  refine ⟨φL (0, 0), by rw [φL00_ρ, Complex.ofReal_im], by
    rw [φL00_ρ, Complex.ofReal_re]; exact rhoR_gt_one, fun τ hτ => ?_⟩
  rw [φL00_ρ] at hτ ⊢
  rw [Complex.ofReal_re]
  have h := congrArg τ ρ_cube_sub
  rw [map_sub, map_sub, map_pow, map_one, map_zero] at h
  exact norm_lt_rhoR_of_root _ h hτ

/-- The real root of `X³ − X − 1` is a Perron number. -/
theorem isPerronNumber_rhoR : IsPerronNumber rhoR := by
  have hint : IsIntegral ℤ rhoR := by
    have h := HermiteCompositum.Instance.ρ_isIntegral_int.map (φL (0, 0)).toIntAlgHom
    have h' : IsIntegral ℤ (φL (0, 0) ρ) := h
    rw [φL00_ρ] at h'
    exact (isIntegral_algHom_iff Complex.ofRealHom.toIntAlgHom Complex.ofReal_injective).1 h'
  refine ⟨hint, rhoR_gt_one.le, fun z hz hne => ?_⟩
  have hp : aeval rhoR (X ^ 3 - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    linear_combination rhoR_eq
  have h := aeval_eq_zero_of_mem_aroots_minpoly hint hp hz
  simp only [map_sub, map_pow, aeval_X, map_one] at h
  exact norm_lt_rhoR_of_root z h hne

theorem coe_ρ'_eq : ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L) = ρ := by
  rw [RingOfIntegers.coe_eq_algebraMap, coe_ρ']

theorem minpoly_ρ_map :
    (minpoly ℤ ρ).map (Int.castRingHom ℂ) = (X ^ 3 - X - 1 : ℂ[X]) := by
  have e := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ
    HermiteCompositum.Instance.ρ_isIntegral_int
  rw [RingHom.ext_int (Int.castRingHom ℂ) ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)),
    ← Polynomial.map_map, ← e, minpoly_ρ]
  simp [HermiteCompositum.Port014.fρ]

theorem mahler_ρ_le_three :
    ((minpoly ℤ ρ).map (Int.castRingHom ℂ)).mahlerMeasure ≤ 3 := by
  rw [minpoly_ρ_map]
  refine (mahlerMeasure_le_sum_norm_coeff _).trans (le_of_eq ?_)
  have hdeg : (X ^ 3 - X - 1 : ℂ[X]).natDegree < 4 := by
    have : (X ^ 3 - X - 1 : ℂ[X]).natDegree ≤ 3 := by compute_degree!
    omega
  rw [sum_over_range' _ (fun _ => norm_zero) 4 hdeg]
  simp [Finset.sum_range_succ, coeff_X, coeff_one]
  norm_num

/-- **Probe (`ℚ⟮x⟯ = ⊤` needed in `perronAt_generator_selection`).** `x = ρ` is an algebraic
integer of `L` that does not generate `L`, has Mahler measure at most that of every integral
generator, satisfies `IsPerronAt`, and is not `ρQ`. -/
theorem hx_needed_perronAt :
    ¬ ℚ⟮((HermiteCompositum.Instance.ρ' : 𝓞 L) : L)⟯ = ⊤ ∧
      (∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
        ((minpoly ℤ ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L)).map
            (Int.castRingHom ℂ)).mahlerMeasure ≤
          ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure) ∧
      IsPerronAt ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L) ∧
      ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L) ≠ ρ * Q := by
  rw [coe_ρ'_eq]
  have hnt : ¬ ℚ⟮ρ⟯ = ⊤ := listed_small_not_top ρ (by simp)
  refine ⟨hnt, fun y hy => ?_, ρ_perronAt, fun h => hnt ?_⟩
  · have h1 := mahler_ρ_le_three
    have h2 := H_ge
    have h3 := mahlerMeasure_generator_ge y hy
    rw [mahler_ρQ] at h3
    linarith
  · rw [h, ← ρQunit_coe]; exact ρQunit_top

/-- **Probe (`ℚ⟮x⟯ = ⊤` needed in `perronNumber_generator_selection`).** -/
theorem hx_needed_perronNumber :
    ¬ ℚ⟮((HermiteCompositum.Instance.ρ' : 𝓞 L) : L)⟯ = ⊤ ∧
      (∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
        ((minpoly ℤ ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L)).map
            (Int.castRingHom ℂ)).mahlerMeasure ≤
          ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure) ∧
      (∃ σ : L →+* ℂ, ∃ r : ℝ,
        σ ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L) = r ∧ IsPerronNumber r) ∧
      ((HermiteCompositum.Instance.ρ' : 𝓞 L) : L) ≠ ρ * Q := by
  obtain ⟨h1, h2, -, h4⟩ := hx_needed_perronAt
  refine ⟨h1, h2, ⟨φL (0, 0), rhoR, by rw [coe_ρ'_eq, φL00_ρ], isPerronNumber_rhoR⟩, h4⟩

/-! ## `x = 2ρQ`: every hypothesis except minimality -/

theorem twoρQ_perronAt : IsPerronAt (twoρQ : L) := by
  rw [twoρQ_coe]
  obtain ⟨σ, him, hre, hmax⟩ := ρQ_perron
  have e : ∀ τ : L →+* ℂ, τ (2 * (ρ * Q)) = 2 * τ (ρ * Q) := fun τ => by
    rw [map_mul, map_ofNat]
  refine ⟨σ, ?_, ?_, fun τ hτ => ?_⟩
  · rw [e]; generalize σ (ρ * Q) = w at him; simp [him]
  · rw [e]; generalize σ (ρ * Q) = w at hre; simp; linarith
  · have hne : τ (ρ * Q) ≠ σ (ρ * Q) := fun h => hτ (by rw [e, e, h])
    have h := hmax τ hne
    rw [e, e, norm_mul]
    generalize τ (ρ * Q) = a at h ⊢
    generalize σ (ρ * Q) = w at h ⊢
    simp
    linarith

/-- **Probe (minimality needed).** `2ρQ` generates `L`, satisfies `IsPerronAt` and the
Perron-number hypothesis, and is not `ρQ`. -/
theorem hmin_needed :
    ℚ⟮(twoρQ : L)⟯ = ⊤ ∧ IsPerronAt (twoρQ : L) ∧
      (∃ σ : L →+* ℂ, ∃ r : ℝ, σ (twoρQ : L) = r ∧ IsPerronNumber r) ∧
      (twoρQ : L) ≠ ρ * Q := by
  refine ⟨twoρQ_top, twoρQ_perronAt,
    (isPerronAt_iff_isPerronNumber twoρQ twoρQ_top).1 twoρQ_perronAt, ?_⟩
  rw [twoρQ_coe]
  intro h
  have h0 : ρ * Q = 0 := by linear_combination h
  exact ne_zero_of_adjoin_eq_top (ρ * Q) HermiteCompositum.Assembly.adjoin_ρQ_eq_top h0

/-! ## Definition checks -/

/-- The complex roots of the minimal polynomial over `ℤ` of a real algebraic integer are simple. -/
theorem aroots_minpoly_nodup {r : ℝ} (hr : IsIntegral ℤ r) :
    ((minpoly ℤ r).aroots ℂ).Nodup := by
  have hQ : IsIntegral ℚ r := hr.tower_top
  have e := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hr
  have hsep : ((minpoly ℚ r).map (algebraMap ℚ ℂ)).Separable :=
    (minpoly.irreducible hQ).separable.map
  rw [aroots_def, show algebraMap ℤ ℂ = (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) from
    RingHom.ext_int _ _, ← Polynomial.map_map, ← e]
  exact nodup_roots hsep

example (x : L) : embHeight x = ∏ σ : L →+* ℂ, max 1 ‖σ x‖ := rfl

example (r : ℝ) : IsPerronNumber r ↔
    (IsIntegral ℤ r ∧ 1 ≤ r ∧ ∀ z ∈ (minpoly ℤ r).aroots ℂ, z ≠ (r : ℂ) → ‖z‖ < r) := Iff.rfl

#check @Polynomial.mahlerMeasure
#print Polynomial.mahlerMeasure
#check @Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots

/-! ## No nontrivial automorphism of `L` -/

/-- Every `ℚ`-automorphism of `L` is the identity; in particular the only conjugate of `ρQ` lying
in `L` is `ρQ`. -/
theorem algEquiv_eq_refl (f : L ≃ₐ[ℚ] L) : f = AlgEquiv.refl := by
  have hint : IsIntegral ℤ (f (ρ * Q)) := by
    have h := (RingOfIntegers.isIntegral_coe (ρQunit : 𝓞 L)).map
      (f : L →+* L).toIntAlgHom
    have h' : IsIntegral ℤ ((f : L →+* L) (ρ * Q)) := by
      rw [← ρQunit_coe, RingOfIntegers.coe_eq_algebraMap]; exact h
    exact h'
  set x : 𝓞 L := ⟨f (ρ * Q), hint⟩
  have hxc : (x : L) = f (ρ * Q) := rfl
  have hmZ : minpoly ℤ (x : L) = minpoly ℤ (ρ * Q) := by
    rw [hxc]
    exact minpoly.algHom_eq (f : L →+* L).toIntAlgHom f.injective (ρ * Q)
  have hx : ℚ⟮(x : L)⟯ = ⊤ := by
    rw [adjoin_eq_top_iff_natDegree, hxc, minpoly.algEquiv_eq f (ρ * Q),
      ← adjoin_eq_top_iff_natDegree]
    exact HermiteCompositum.Assembly.adjoin_ρQ_eq_top
  have hmin : ∀ y : 𝓞 L, ℚ⟮(y : L)⟯ = ⊤ →
      ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ (y : L)).map (Int.castRingHom ℂ)).mahlerMeasure := by
    intro y hy; rw [hmZ]; exact mahlerMeasure_generator_ge y hy
  have hP : IsPerronAt (x : L) := by
    obtain ⟨σ, him, hre, hmax⟩ := ρQ_perron
    have hs : (σ.comp (f.symm : L →+* L)) (x : L) = σ (ρ * Q) := by
      rw [hxc, RingHom.comp_apply]; simp
    refine ⟨σ.comp (f.symm : L →+* L), by rw [hs]; exact him, by rw [hs]; exact hre,
      fun τ hτ => ?_⟩
    rw [hs] at hτ ⊢
    have ht : τ (x : L) = (τ.comp (f : L →+* L)) (ρ * Q) := by rw [hxc]; rfl
    rw [ht] at hτ ⊢
    exact hmax _ hτ
  have hfix : f (ρ * Q) = ρ * Q := perronAt_generator_selection x hx hmin hP
  have hadj : Algebra.adjoin ℚ ({ρ * Q} : Set L) = ⊤ :=
    adjoin_eq_top_iff.1 HermiteCompositum.Assembly.adjoin_ρQ_eq_top
  have he : (f : L →ₐ[ℚ] L) = AlgHom.id ℚ L := AlgHom.ext_of_adjoin_eq_top hadj (by
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    simpa using hfix)
  ext y
  have := congrArg (fun g : L →ₐ[ℚ] L => g y) he
  simpa using this

end

end HeightT2.Review
