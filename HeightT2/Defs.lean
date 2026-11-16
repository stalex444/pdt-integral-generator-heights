module

public import Mathlib

/-!
# Definitions: Perron numbers and the `T₂` Gram matrix

`IsPerronNumber r` (Lind, 1984): `r` is a real algebraic integer, `r ≥ 1`, and every other
complex root of the minimal polynomial of `r` over `ℤ` has modulus strictly less than `r`.

Controls on the definition: every integer `n ≥ 1` is a Perron number (in particular `1` and
`2`); `1 + √2` is a Perron number; `√2` is not (its conjugate `−√2` has the same modulus); a
real number below `1` is not.

`t2Gram b` (for a finite family `b : ι → K` in a number field `K`) is the `T₂` Gram matrix,
`t2Gram b i k = ∑_σ σ (b i) · conj (σ (b k))` over all ring homomorphisms `K →+* ℂ`, and
`t2GramRe b` its real part. Their properties are in `HeightT2.Compositum`.
-/

@[expose] public section

open Polynomial

namespace HeightT2

/-- A real algebraic integer `r ≥ 1` exceeding the modulus of every other complex root of its
minimal polynomial over `ℤ` (Lind's convention). -/
def IsPerronNumber (r : ℝ) : Prop :=
  IsIntegral ℤ r ∧ 1 ≤ r ∧ ∀ z ∈ (minpoly ℤ r).aroots ℂ, z ≠ (r : ℂ) → ‖z‖ < r

/-- Every complex root of the minimal polynomial over `ℤ` of an algebraic integer `r : ℝ` is a
root of each integer polynomial vanishing at `r`. -/
theorem aeval_eq_zero_of_mem_aroots_minpoly {r : ℝ} (hr : IsIntegral ℤ r) {p : ℤ[X]}
    (hp : aeval r p = 0) {z : ℂ} (hz : z ∈ (minpoly ℤ r).aroots ℂ) : aeval z p = 0 := by
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hr hp
  rw [mem_aroots] at hz
  rw [hq, map_mul, hz.2, zero_mul]

/-- **Control.** Every integer `n ≥ 1` is a Perron number. -/
theorem isPerronNumber_intCast (n : ℤ) (hn : 1 ≤ n) : IsPerronNumber (n : ℝ) := by
  have hint : IsIntegral ℤ (n : ℝ) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := n)
  refine ⟨hint, by exact_mod_cast hn, fun z hz hne => ?_⟩
  have hp : aeval (n : ℝ) (X - C n) = 0 := by simp
  have h := aeval_eq_zero_of_mem_aroots_minpoly hint hp hz
  simp only [map_sub, aeval_X, map_intCast, eq_intCast, sub_eq_zero] at h
  exact (hne (by rw [h]; norm_cast)).elim

/-- **Control.** `1` is a Perron number. -/
theorem isPerronNumber_one : IsPerronNumber 1 := by
  simpa using isPerronNumber_intCast 1 le_rfl

/-- **Control.** `2` is a Perron number. -/
theorem isPerronNumber_two : IsPerronNumber 2 := by
  simpa using isPerronNumber_intCast 2 (by norm_num)

/-- **Control.** A real number below `1` is not a Perron number. -/
theorem not_isPerronNumber_of_lt_one {r : ℝ} (hr : r < 1) : ¬ IsPerronNumber r :=
  fun h => absurd h.2.1 (not_le.2 hr)

/-- **Control.** `1 + √2` is a Perron number (its conjugate `1 − √2` has modulus `√2 − 1`). -/
theorem isPerronNumber_one_add_sqrt_two : IsPerronNumber (1 + √2) := by
  have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsint : IsIntegral ℤ (√2 : ℝ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hs]; simpa using isIntegral_algebraMap (R := ℤ) (A := ℝ) (x := 2)
  have hint : IsIntegral ℤ (1 + √2 : ℝ) := isIntegral_one.add hsint
  refine ⟨hint, by linarith, fun z hz hne => ?_⟩
  have hp : aeval (1 + √2 : ℝ) (X ^ 2 - C 2 * X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
    linear_combination hs
  have h := aeval_eq_zero_of_mem_aroots_minpoly hint hp hz
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one] at h
  have hsC : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hs
  have hfac : (z - ((1 + √2 : ℝ) : ℂ)) * (z - ((1 - √2 : ℝ) : ℂ)) = 0 := by
    push_cast; linear_combination h - hsC
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hne
  · rw [sub_eq_zero.1 h1, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith

/-- **Control (strictness).** `√2` is not a Perron number: `−√2` is a root of its minimal
polynomial with the same modulus. -/
theorem not_isPerronNumber_sqrt_two : ¬ IsPerronNumber √2 := by
  have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  rintro ⟨hint, -, hroots⟩
  have hp : aeval (√2 : ℝ) (X ^ 2 - C 2 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_ofNat]
    linear_combination hs
  have hmon : (X ^ 2 - C 2 : ℤ[X]).Monic := by
    simpa using monic_X_pow_sub_C (2 : ℤ) (by norm_num : (2 : ℕ) ≠ 0)
  have hdvd := minpoly.isIntegrallyClosed_dvd hint hp
  have hdeg2 : (X ^ 2 - C 2 : ℤ[X]).natDegree = 2 := by
    simpa using natDegree_X_pow_sub_C (n := 2) (r := (2 : ℤ))
  -- the minimal polynomial has degree 2: degree 1 would make `√2` an integer
  have hdeg : (X ^ 2 - C 2 : ℤ[X]).natDegree ≤ (minpoly ℤ (√2 : ℝ)).natDegree := by
    rw [hdeg2]
    by_contra hlt
    push Not at hlt
    have hpos := minpoly.natDegree_pos hint
    have h1 : (minpoly ℤ (√2 : ℝ)).natDegree = 1 := by omega
    have hm := minpoly.monic hint
    obtain ⟨c, hc⟩ : ∃ c : ℤ, minpoly ℤ (√2 : ℝ) = X + C c := ⟨_, hm.eq_X_add_C h1⟩
    have h0 := minpoly.aeval ℤ (√2 : ℝ)
    rw [hc] at h0
    simp only [map_add, aeval_X, map_intCast, eq_intCast] at h0
    have hirr : Irrational √2 := irrational_sqrt_two
    exact hirr.ne_int (-c) (by push_cast; linarith)
  have heq := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd hdeg
  have hmem : (-((√2 : ℝ) : ℂ)) ∈ (minpoly ℤ (√2 : ℝ)).aroots ℂ := by
    rw [← heq, mem_aroots]
    refine ⟨hmon.ne_zero, ?_⟩
    have hsC : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hs
    simp only [map_sub, map_pow, aeval_X, map_ofNat]
    linear_combination hsC
  have hne : (-((√2 : ℝ) : ℂ)) ≠ ((√2 : ℝ) : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have := hroots _ hmem hne
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at this
  exact lt_irrefl _ this

/-! ### The `T₂` Gram matrix of a family -/

section Gram

variable {K : Type*} [Field K] [NumberField K]

/-- The `T₂` Gram matrix of a family in a number field: entry `(i, k)` is
`∑_σ σ (b i) * conj (σ (b k))`, over all ring homomorphisms `K →+* ℂ`. It is Hermitian
(`t2Gram_isHermitian`) and real-valued (`t2Gram_eq_ofReal`). -/
noncomputable def t2Gram {ι : Type*} (b : ι → K) : Matrix ι ι ℂ :=
  Matrix.of fun i k => ∑ σ : K →+* ℂ, σ (b i) * star (σ (b k))

/-- The real part of the `T₂` Gram matrix, a real symmetric matrix (`t2GramRe_isHermitian`). -/
noncomputable def t2GramRe {ι : Type*} (b : ι → K) : Matrix ι ι ℝ :=
  Matrix.of fun i k => (t2Gram b i k).re

end Gram

end HeightT2
