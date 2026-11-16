module

public import Mathlib
public import HeightT2.Bridge
public import HeightT2.Bound
public import HermiteCompositum.Extras
public import RulerSelection.MahlerT2

/-!
# The equality case of `T₂(x) ≤ mulHeight₁(x)² + n − 1`

For a number field `K` of degree `n ≥ 2` and every `x ∈ K`,
`∑_{σ : K →+* ℂ} ‖σ x‖² = mulHeight₁(x)² + (n − 1)` holds exactly when `x` is a root of unity
(`sum_norm_sq_eq_mulHeight₁_sq_add_iff`); the form for algebraic integers is
`sum_norm_sq_eq_mulHeight₁_sq_add_iff_of_integer`.

Structure of the proof.
* The real-family inequality `∑ y + 1 ≤ ∏ y + card` for `y ≥ 1` is strict as soon as two
  of the `y` exceed `1` (`sum_add_one_lt_prod_add_card`).
* Equality in the `T₂` bound therefore forces: every conjugate has modulus at least `1`, at most
  one conjugate has modulus greater than `1`, and the finite part of the height is `1`, so `x` is
  integral (`eq_case_structure`).
* If no conjugate lies outside the unit circle, Kronecker's theorem
  (`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`) gives a root of unity.
* If exactly one conjugate `σ₀ x` lies outside, then since `n ≥ 2` another conjugate has modulus
  `1`; an algebraic number with a conjugate on the unit circle has `x⁻¹` as a conjugate
  (`HermiteCompositum.minpoly_inv_eq_of_norm_eq_one`), so `(σ₀ x)⁻¹`, of modulus `< 1`, is a
  conjugate of `x`, a contradiction.

The deciding steps are Kronecker's theorem (1857) and the reciprocity of the minimal polynomial
of an algebraic number with a conjugate on the unit circle: the reciprocity step in the proof of
Salem's lemma (Salem, *Algebraic Numbers and Fourier Analysis*, 1963, p. 26, as restated with
proof in Smyth, Bull. LMS 47 (2015), Lemma 1).

Controls: the hypothesis `2 ≤ n` cannot be dropped (`control_finrank_two_needed`: in `ℚ`,
`x = 2` gives `4 = 4 + 0`); the equality is not automatic in degree at least two
(`control_strict_two`: at `x = 2` the inequality is strict).
-/

@[expose] public section

open NumberField

namespace HeightT2

noncomputable section

/-- For reals at least one, the inequality `∑ y + 1 ≤ ∏ y + card` is strict when two distinct
indices carry values greater than one. -/
theorem sum_add_one_lt_prod_add_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ)
    (hy : ∀ k ∈ s, 1 ≤ y k) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hyi : 1 < y i) (hyj : 1 < y j) :
    ∑ k ∈ s, y k + 1 < ∏ k ∈ s, y k + (s.card : ℝ) := by
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  set t := (s.erase i).erase j with ht
  have hsum : ∑ k ∈ s, y k = y i + (y j + ∑ k ∈ t, y k) := by
    rw [← Finset.add_sum_erase s y hi, ← Finset.add_sum_erase _ y hj']
  have hprod : ∏ k ∈ s, y k = y i * (y j * ∏ k ∈ t, y k) := by
    rw [← Finset.mul_prod_erase s y hi, ← Finset.mul_prod_erase _ y hj']
  have hcard : (s.card : ℝ) = (t.card : ℝ) + 2 := by
    have h1 : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
    have h2 : t.card + 1 = (s.erase i).card := Finset.card_erase_add_one hj'
    have : s.card = t.card + 2 := by omega
    rw [this]; push_cast; ring
  have hyt : ∀ k ∈ t, 1 ≤ y k := fun k hk =>
    hy k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
  have ih := RulerSelection.sum_add_one_le_prod_add_card t y hyt
  have hP : 1 ≤ ∏ k ∈ t, y k := Finset.one_le_prod₀ hyt
  rw [hsum, hprod, hcard]
  have e1 : 0 < (y i - 1) * (y j - 1) := mul_pos (by linarith) (by linarith)
  have e2 : 0 ≤ (y i * y j - 1) * (∏ k ∈ t, y k - 1) :=
    mul_nonneg (by nlinarith) (by linarith)
  nlinarith

/-- For `t ≥ 0`, `max 1 (t ^ 2) = (max 1 t) ^ 2`. -/
theorem max_one_sq_eq {t : ℝ} (ht : 0 ≤ t) : max 1 (t ^ 2) = (max 1 t) ^ 2 := by
  rcases le_total 1 t with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
  · rw [max_eq_left h, max_eq_left (by nlinarith)]
    norm_num

variable {K : Type*} [Field K] [NumberField K]

/-- If every finite place takes value at most `1` at `x`, then `x` is integral over `ℤ`. -/
theorem isIntegral_of_finitePlace_le_one (x : K) (h : ∀ w : FinitePlace K, w x ≤ 1) :
    IsIntegral ℤ x := by
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v.valuation K x ≤ 1 := by
    intro v
    have h1 := h (FinitePlace.mk v)
    rw [FinitePlace.mk_apply, FinitePlace.norm_embedding'] at h1
    have h2 := (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp (by exact_mod_cast h1)
    exact h2
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x hv
  exact (y.isIntegral_coe : IsIntegral ℤ (y : K))

/-- **Structure of the equality case.** If `T₂(x) = mulHeight₁(x)² + (n − 1)`, then every
conjugate of `x` has modulus at least `1`, among any two distinct embeddings at least one sends `x`
to the unit circle, and `x` is integral over `ℤ`. -/
theorem eq_case_structure (x : K)
    (heq : ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 =
      Height.mulHeight₁ x ^ 2 + ((Module.finrank ℚ K : ℝ) - 1)) :
    (∀ σ : K →+* ℂ, 1 ≤ ‖σ x‖) ∧
    (∀ σ τ : K →+* ℂ, σ ≠ τ → ‖σ x‖ = 1 ∨ ‖τ x‖ = 1) ∧
    IsIntegral ℤ x := by
  classical
  set P := ∏ σ : K →+* ℂ, max 1 ‖σ x‖ with hPdef
  set H := Height.mulHeight₁ x with hHdef
  set y : (K →+* ℂ) → ℝ := fun σ => max 1 (‖σ x‖ ^ 2) with hydef
  have hPH : P ≤ H := prod_embeddings_le_mulHeight₁ x
  have hP1 : 1 ≤ P := Finset.one_le_prod₀ fun _ _ => le_max_left _ _
  have hyP : ∏ σ, y σ = P ^ 2 := by
    rw [hPdef, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun σ _ => max_one_sq_eq (norm_nonneg _)
  have hy1 : ∀ σ ∈ (Finset.univ : Finset (K →+* ℂ)), 1 ≤ y σ := fun _ _ => le_max_left _ _
  have hcardR : ((Finset.univ : Finset (K →+* ℂ)).card : ℝ) = (Module.finrank ℚ K : ℝ) := by
    rw [Finset.card_univ, Embeddings.card K ℂ]
  have h1 : ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 ≤ ∑ σ, y σ :=
    Finset.sum_le_sum fun σ _ => le_max_right _ _
  have h2 := RulerSelection.sum_add_one_le_prod_add_card Finset.univ y hy1
  rw [hcardR, hyP] at h2
  have h3 : P ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (by linarith) hPH 2
  -- all three inequalities are equalities
  have e1 : ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 = ∑ σ, y σ := by linarith
  have e2 : ∑ σ, y σ + 1 = P ^ 2 + (Module.finrank ℚ K : ℝ) := by linarith
  have e3 : P ^ 2 = H ^ 2 := by linarith
  have hge : ∀ σ : K →+* ℂ, 1 ≤ ‖σ x‖ := by
    have := (Finset.sum_eq_sum_iff_of_le (fun σ _ => le_max_right (1 : ℝ) (‖σ x‖ ^ 2))).mp e1
    intro σ
    have hσ := this σ (Finset.mem_univ σ)
    have h1σ : (1 : ℝ) ≤ ‖σ x‖ ^ 2 := by rw [hσ]; exact le_max_left _ _
    nlinarith [norm_nonneg (σ x)]
  refine ⟨hge, ?_, ?_⟩
  · intro σ τ hστ
    by_contra hcon
    push Not at hcon
    have hσ : 1 < ‖σ x‖ := lt_of_le_of_ne (hge σ) (Ne.symm hcon.1)
    have hτ : 1 < ‖τ x‖ := lt_of_le_of_ne (hge τ) (Ne.symm hcon.2)
    have hyσ : 1 < y σ := lt_of_lt_of_le (by nlinarith) (le_max_right _ _)
    have hyτ : 1 < y τ := lt_of_lt_of_le (by nlinarith) (le_max_right _ _)
    have hlt := sum_add_one_lt_prod_add_card Finset.univ y hy1 (Finset.mem_univ σ)
      (Finset.mem_univ τ) hστ hyσ hyτ
    rw [hcardR, hyP] at hlt
    linarith
  · -- the finite part of the height is `1`
    have hPHeq : P = H := by nlinarith
    rcases eq_or_ne x 0 with rfl | hx0
    · exact isIntegral_zero
    have hHF : H = P * ∏ᶠ w : FinitePlace K, max (w x) 1 := by
      rw [hHdef, NumberField.mulHeight₁_eq, prod_infinitePlace_eq_prod_embeddings]
    have hF : ∏ᶠ w : FinitePlace K, max (w x) 1 = 1 := by
      have hP0 : P ≠ 0 := by linarith
      have : P * ∏ᶠ w : FinitePlace K, max (w x) 1 = P * 1 := by rw [mul_one, ← hHF, hPHeq]
      exact mul_left_cancel₀ hP0 this
    have hsupp : (fun w : FinitePlace K => max (w x) 1).HasFiniteMulSupport := by
      refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hx0) ?_
      intro w hw
      simp only [Function.mem_mulSupport] at hw ⊢
      intro hw1
      exact hw (by rw [hw1, max_self])
    apply isIntegral_of_finitePlace_le_one
    intro w
    have hfin := finprod_eq_prod_of_mulSupport_toFinset_subset
      (fun w : FinitePlace K => max (w x) 1) hsupp (Finset.subset_insert w hsupp.toFinset)
    rw [hfin, ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self w _)] at hF
    have hrest : 1 ≤ ∏ j ∈ (insert w hsupp.toFinset).erase w, max (j x) 1 :=
      Finset.one_le_prod₀ fun _ _ => le_max_right _ _
    have hw1 : max (w x) 1 ≤ 1 := by nlinarith [le_max_right (w x) 1]
    exact le_trans (le_max_left _ _) hw1

/-- **The equality case.** For a number field `K` of degree `n ≥ 2` and every `x : K`,
`T₂(x) = mulHeight₁(x)² + (n − 1)` if and only if `x` is a root of unity. -/
theorem sum_norm_sq_eq_mulHeight₁_sq_add_iff (hK : 2 ≤ Module.finrank ℚ K) (x : K) :
    ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 = Height.mulHeight₁ x ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) ↔
      ∃ m : ℕ, 0 < m ∧ x ^ m = 1 := by
  constructor
  · intro heq
    obtain ⟨hge, hone, hint⟩ := eq_case_structure x heq
    by_cases hbig : ∃ σ₀ : K →+* ℂ, 1 < ‖σ₀ x‖
    · exfalso
      obtain ⟨σ₀, hσ₀⟩ := hbig
      have hcard : 1 < Fintype.card (K →+* ℂ) := by
        rw [Embeddings.card K ℂ]; omega
      obtain ⟨σ₁, hσ₁⟩ := Fintype.exists_ne_of_one_lt_card hcard σ₀
      have h1 : ‖σ₁ x‖ = 1 := by
        rcases hone σ₀ σ₁ (Ne.symm hσ₁) with h | h
        · exact absurd h (ne_of_gt hσ₀)
        · exact h
      have hmin := HermiteCompositum.minpoly_inv_eq_of_norm_eq_one σ₁ x h1
      have hmem : σ₀ x⁻¹ ∈ Set.range (fun φ : K →+* ℂ => φ x) := by
        rw [Embeddings.range_eval_eq_rootSet_minpoly K ℂ x, ← hmin,
          ← Embeddings.range_eval_eq_rootSet_minpoly K ℂ x⁻¹]
        exact ⟨σ₀, rfl⟩
      obtain ⟨τ, hτ'⟩ := hmem
      have hτ : τ x = σ₀ x⁻¹ := hτ'
      have hτx : ‖τ x‖ < 1 := by
        rw [hτ, map_inv₀, norm_inv]
        exact inv_lt_one_of_one_lt₀ hσ₀
      exact absurd (hge τ) (not_le.mpr hτx)
    · push Not at hbig
      obtain ⟨m, hm, hxm⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ hint
        (fun φ => le_antisymm (hbig φ) (hge φ))
      exact ⟨m, hm, hxm⟩
  · rintro ⟨m, hm, hxm⟩
    have hσ : ∀ σ : K →+* ℂ, ‖σ x‖ = 1 := fun σ => by
      have : ‖σ x‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, hxm, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp this
    have hH : Height.mulHeight₁ x = 1 := by
      have : Height.mulHeight₁ x ^ m = 1 := by
        rw [← Height.mulHeight₁_pow, hxm, Height.mulHeight₁_one]
      exact (pow_eq_one_iff_of_nonneg
        (le_trans zero_le_one (Height.one_le_mulHeight₁ x)) hm.ne').mp this
    simp only [hσ, hH, one_pow, Finset.sum_const, Finset.card_univ, Embeddings.card K ℂ,
      nsmul_eq_mul, mul_one]
    ring

/-- **The equality case for algebraic integers.** For `x : 𝓞 K` with `[K : ℚ] ≥ 2`,
`T₂(x) = mulHeight₁(x)² + (n − 1)` if and only if `x` is a root of unity. -/
theorem sum_norm_sq_eq_mulHeight₁_sq_add_iff_of_integer (hK : 2 ≤ Module.finrank ℚ K)
    (x : 𝓞 K) :
    ∑ σ : K →+* ℂ, ‖σ (x : K)‖ ^ 2 =
        Height.mulHeight₁ (x : K) ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) ↔
      ∃ m : ℕ, 0 < m ∧ x ^ m = 1 := by
  rw [sum_norm_sq_eq_mulHeight₁_sq_add_iff hK]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  constructor
  · intro h
    apply RingOfIntegers.coe_injective
    simpa using h
  · intro h
    have := congrArg (fun z : 𝓞 K => (z : K)) h
    simpa using this

/-- **Control (`n ≥ 2` is needed).** In `ℚ`, at `x = 2` the equality holds (both sides are `4`)
and `2` is not a root of unity. -/
theorem control_finrank_two_needed :
    ∑ σ : ℚ →+* ℂ, ‖σ (2 : ℚ)‖ ^ 2 =
        Height.mulHeight₁ (2 : ℚ) ^ 2 + ((Module.finrank ℚ ℚ : ℝ) - 1) ∧
      ¬ ∃ m : ℕ, 0 < m ∧ (2 : ℚ) ^ m = 1 := by
  refine ⟨control_bound_attained_rat_two, ?_⟩
  rintro ⟨m, hm, h⟩
  have : (1 : ℚ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
  linarith

/-- **Control (the equality is not automatic).** In every number field of degree `n ≥ 2`, at
`x = 2` the inequality is strict (here `T₂(2) = 4n` and `mulHeight₁(2)² = 4ⁿ`, not proved in
this statement). -/
theorem control_strict_two (hK : 2 ≤ Module.finrank ℚ K) :
    ∑ σ : K →+* ℂ, ‖σ (2 : K)‖ ^ 2 <
      Height.mulHeight₁ (2 : K) ^ 2 + ((Module.finrank ℚ K : ℝ) - 1) := by
  have hne : ¬ (∑ σ : K →+* ℂ, ‖σ (2 : K)‖ ^ 2 =
      Height.mulHeight₁ (2 : K) ^ 2 + ((Module.finrank ℚ K : ℝ) - 1)) := by
    rw [sum_norm_sq_eq_mulHeight₁_sq_add_iff hK]
    rintro ⟨m, hm, h⟩
    have hσ : ∀ σ : K →+* ℂ, σ ((2 : K) ^ m) = (2 : ℂ) ^ m := fun σ => by
      rw [map_pow, map_ofNat]
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h2 := hσ σ
    rw [h, map_one] at h2
    have : ‖(2 : ℂ) ^ m‖ = 2 ^ m := by rw [norm_pow]; norm_num
    rw [← h2, norm_one] at this
    have : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) hm.ne'
    linarith
  exact lt_of_le_of_ne (sum_norm_sq_le_mulHeight₁_sq_add 2) hne

end

end HeightT2
