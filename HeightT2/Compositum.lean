module

public import Mathlib
public import HeightT2.Defs
public import HermiteCompositum.Places
public import RulerSelection.Kron

/-!
# The `T₂` Gram matrix of a linearly disjoint compositum is a Kronecker product

For a finite family `b : ι → K` in a number field `K`, the `T₂` Gram matrix (defined in
`HeightT2.Defs`) is `t2Gram b i k = ∑_σ σ (b i) · conj (σ (b k))`, the sum over all ring
homomorphisms `K →+* ℂ`.
For rational coefficients `a`, `∑_σ ‖σ (∑ a_i b_i)‖² = aᵀ (Re G) a` (`sum_norm_sq_eq_t2GramRe`);
only the real part of the Gram matrix enters, and no hypothesis is needed for this identity.
Because the set of embeddings is closed under complex conjugation, the Gram matrix is in fact
real (`t2Gram_eq_ofReal`); that is what makes the real part multiplicative below.

Let `L` be a number field and `K₁ K₂ : IntermediateField ℚ L` with `K₁.LinearDisjoint K₂` and
`K₁ ⊔ K₂ = ⊤`.

* `t2Gram_compositum` : the `T₂` Gram matrix over the embeddings of `L` of the product family
  `(i, j) ↦ b i · c j` is the Kronecker product of the `T₂` Gram matrices of `b` (over the
  embeddings of `K₁`) and of `c` (over the embeddings of `K₂`); `t2GramRe_compositum` is the
  real form, and `sum_norm_sq_compositum` the quadratic-form version.
* `coord_sq_le_sum_norm_sq` : with `s, t ≥ 0` and `Re G_b − s E_ii ⪰ 0`, `Re G_c − t E_jj ⪰ 0`,
  every rational coefficient vector satisfies
  `s t a(i,j)² ≤ ∑_σ ‖σ (∑_p a_p b_{p.1} c_{p.2})‖²`.

Controls: in any number field of degree `n ≥ 2`, `K₁ = K₂ = ⊥` (linearly disjoint, but
`⊥ ⊔ ⊥ ≠ ⊤`) breaks the Kronecker identity (`n` against `1`); `K₁ = K₂ = ⊤` (`⊤ ⊔ ⊤ = ⊤`, not
linearly disjoint) breaks the coordinate bound (`n` against `n²`); and with `K₁ = ⊥, K₂ = ⊤` the
coordinate bound fails once both signs `s, t ≥ 0` are dropped (`s = −2`, `t = −n`).
-/

@[expose] public section

open Matrix NumberField
open scoped Kronecker

namespace HeightT2

noncomputable section

/-! ### The Gram matrix of a family -/

section General

variable {K : Type*} [Field K] [NumberField K]

theorem t2Gram_apply {ι : Type*} (b : ι → K) (i k : ι) :
    t2Gram b i k = ∑ σ : K →+* ℂ, σ (b i) * star (σ (b k)) := rfl

theorem t2GramRe_apply {ι : Type*} (b : ι → K) (i k : ι) :
    t2GramRe b i k = (t2Gram b i k).re := rfl

omit [NumberField K] in
/-- Complex conjugation of embeddings is an involution. -/
theorem conjugate_involutive :
    Function.Involutive (ComplexEmbedding.conjugate : (K →+* ℂ) → (K →+* ℂ)) := by
  intro φ
  ext x
  simp

/-- The Gram matrix is Hermitian. -/
theorem t2Gram_isHermitian {ι : Type*} (b : ι → K) : (t2Gram b).IsHermitian := by
  ext i k
  simp only [conjTranspose_apply, t2Gram_apply, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun σ _ => mul_comm _ _

/-- Each entry of the Gram matrix is fixed by complex conjugation (reindex by `σ ↦ conj ∘ σ`). -/
theorem star_t2Gram {ι : Type*} (b : ι → K) (i k : ι) : star (t2Gram b i k) = t2Gram b i k := by
  rw [t2Gram_apply, star_sum]
  refine Fintype.sum_equiv (conjugate_involutive.toPerm _) _ _ fun σ => ?_
  show star (σ (b i) * star (σ (b k))) = (ComplexEmbedding.conjugate σ) (b i) *
    star ((ComplexEmbedding.conjugate σ) (b k))
  rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, star_mul', star_star]
  congr 1
  exact (Complex.conj_conj _).symm

/-- The Gram matrix is real: each entry is the complex number of its real part. -/
theorem t2Gram_eq_ofReal {ι : Type*} (b : ι → K) (i k : ι) :
    t2Gram b i k = ((t2GramRe b i k : ℝ) : ℂ) :=
  (Complex.conj_eq_iff_re.1 (star_t2Gram b i k)).symm

/-- The real Gram matrix is symmetric. -/
theorem t2GramRe_isHermitian {ι : Type*} (b : ι → K) : (t2GramRe b).IsHermitian := by
  ext i k
  rw [conjTranspose_apply, star_trivial, t2GramRe_apply, t2GramRe_apply,
    ← (t2Gram_isHermitian b).apply i k]
  exact Complex.conj_re _

/-- The quadratic form of a finite family of complex vectors: for real `w`,
`∑_t ‖∑_i w_i f_t(i)‖² = wᵀ M w` with `M i k = Re ∑_t f_t(i) conj f_t(k)`. -/
theorem sum_norm_sq_eq_form {τ ι : Type*} [Fintype τ] [Fintype ι] (f : τ → ι → ℂ)
    (w : ι → ℝ) :
    ∑ t, ‖∑ i, (w i : ℂ) * f t i‖ ^ 2 =
      w ⬝ᵥ ((Matrix.of fun i k => (∑ t, f t i * star (f t k)).re) *ᵥ w) := by
  have key : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hA : ∀ t, ‖∑ i, (w i : ℂ) * f t i‖ ^ 2 =
      ∑ i, ∑ k, w i * w k * (f t i * star (f t k)).re := by
    intro t
    rw [key, star_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (w i : ℂ) * f t i * star ((w k : ℂ) * f t k) =
        ((w i * w k : ℝ) : ℂ) * (f t i * star (f t k)) := by
      rw [star_mul', show star (w k : ℂ) = (w k : ℂ) from Complex.conj_ofReal _]
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  rw [Finset.sum_congr rfl fun t _ => hA t]
  simp only [dotProduct, mulVec, of_apply, Complex.re_sum, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- **The `T₂` form of a family.** For rational coefficients,
`∑_σ ‖σ (∑ a_i b_i)‖² = aᵀ (Re G_b) a`. -/
theorem sum_norm_sq_eq_t2GramRe {ι : Type*} [Fintype ι] (b : ι → K) (a : ι → ℚ) :
    ∑ σ : K →+* ℂ, ‖σ (∑ i, (a i : K) * b i)‖ ^ 2 =
      (fun i => (a i : ℝ)) ⬝ᵥ (t2GramRe b *ᵥ fun i => (a i : ℝ)) := by
  rw [show t2GramRe b = Matrix.of fun i k => (∑ σ : K →+* ℂ, σ (b i) * star (σ (b k))).re
    from rfl, ← sum_norm_sq_eq_form]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [map_sum, map_mul, map_ratCast, Complex.ofReal_ratCast]

/-- The Gram matrix of the one-element family `1` is the degree. -/
theorem t2GramRe_one : t2GramRe (fun _ : Fin 1 => (1 : K)) 0 0 = Module.finrank ℚ K := by
  simp [t2GramRe_apply, t2Gram_apply, Embeddings.card K ℂ]

end General

/-! ### The compositum -/

section Compositum

variable {L : Type*} [Field L] [NumberField L] {K₁ K₂ : IntermediateField ℚ L}

/-- Sums over the embeddings of a linearly disjoint compositum are double sums over the
embeddings of the two factors. -/
theorem sum_embeddings_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    {M : Type*} [AddCommMonoid M] (F : (K₁ →+* ℂ) → (K₂ →+* ℂ) → M) :
    ∑ φ : L →+* ℂ, F (φ.comp (algebraMap K₁ L)) (φ.comp (algebraMap K₂ L)) =
      ∑ φ₁ : K₁ →+* ℂ, ∑ φ₂ : K₂ →+* ℂ, F φ₁ φ₂ := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (HermiteCompositum.embeddingsEquiv h₁ h₂) _ _ fun φ => rfl

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
/-- **The Kronecker identity.** The `T₂` Gram matrix over `L` of the product family is the
Kronecker product of the `T₂` Gram matrices over `K₁` and `K₂`. -/
theorem t2Gram_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (b : ι → K₁) (c : κ → K₂) :
    t2Gram (fun p : ι × κ => (b p.1 : L) * (c p.2 : L)) = t2Gram b ⊗ₖ t2Gram c := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [kroneckerMap_apply, t2Gram_apply, t2Gram_apply, t2Gram_apply, Finset.sum_mul_sum]
  have e := sum_embeddings_compositum h₁ h₂
    (fun φ₁ φ₂ => φ₁ (b i) * star (φ₁ (b k)) * (φ₂ (c j) * star (φ₂ (c l))))
  rw [← e]
  refine Finset.sum_congr rfl fun φ _ => ?_
  simp only [RingHom.comp_apply, IntermediateField.algebraMap_apply, map_mul, star_mul']
  ring

omit [Fintype ι] [Fintype κ] in
/-- **The Kronecker identity, real form.** -/
theorem t2GramRe_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (b : ι → K₁) (c : κ → K₂) :
    t2GramRe (fun p : ι × κ => (b p.1 : L) * (c p.2 : L)) = t2GramRe b ⊗ₖ t2GramRe c := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [kroneckerMap_apply, t2GramRe_apply, t2Gram_compositum h₁ h₂, kroneckerMap_apply,
    t2Gram_eq_ofReal b, t2Gram_eq_ofReal c, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The Kronecker identity, quadratic form.** For rational coefficients,
`∑_σ ‖σ (∑_p a_p b_{p.1} c_{p.2})‖² = aᵀ (Re G_b ⊗ Re G_c) a`. -/
theorem sum_norm_sq_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (b : ι → K₁) (c : κ → K₂) (a : ι × κ → ℚ) :
    ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 =
      (fun p => (a p : ℝ)) ⬝ᵥ ((t2GramRe b ⊗ₖ t2GramRe c) *ᵥ fun p => (a p : ℝ)) := by
  rw [← t2GramRe_compositum h₁ h₂, ← sum_norm_sq_eq_t2GramRe]
  simp only [mul_assoc]

/-- **The coordinate bound in `T₂`.** With `s, t ≥ 0` and certificates `Re G_b − s E_ii ⪰ 0`,
`Re G_c − t E_jj ⪰ 0`, every rational coefficient vector satisfies
`s t a(i,j)² ≤ ∑_σ ‖σ (∑_p a_p b_{p.1} c_{p.2})‖²`. -/
theorem coord_sq_le_sum_norm_sq [DecidableEq ι] [DecidableEq κ]
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (b : ι → K₁) (c : κ → K₂)
    (i : ι) (j : κ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hb : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ ((t2GramRe b - diagonal (Pi.single i s)) *ᵥ v))
    (hc : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ ((t2GramRe c - diagonal (Pi.single j t)) *ᵥ w))
    (a : ι × κ → ℚ) :
    s * t * (a (i, j) : ℝ) ^ 2 ≤
      ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 := by
  rw [sum_norm_sq_compositum h₁ h₂]
  exact RulerSelection.Kron.kron_ge_diag (t2GramRe_isHermitian b) (t2GramRe_isHermitian c)
    i j s t hs ht hb hc (fun p => (a p : ℝ))

end Compositum

/-! ### Controls -/

section Controls

variable {L : Type*} [Field L] [NumberField L]

/-- A `1 × 1` certificate: `v (M − s E) v = (M₀₀ − s) v₀²`. -/
theorem form_one_sub_diag (M : Matrix (Fin 1) (Fin 1) ℝ) (s : ℝ) (v : Fin 1 → ℝ) :
    v ⬝ᵥ ((M - diagonal (Pi.single 0 s)) *ᵥ v) = (M 0 0 - s) * v 0 ^ 2 := by
  simp [dotProduct, mulVec, Matrix.sub_apply]
  ring

/-- **Control (the Kronecker identity needs `K₁ ⊔ K₂ = ⊤`).** In a number field of degree
`n ≥ 2`, `K₁ = K₂ = ⊥` are linearly disjoint, and the Gram entry of `1 · 1` over `L` is `n`,
while the Kronecker product of the Gram entries over `⊥` is `1`. -/
theorem control_t2Gram_compositum_needs_sup (h : 2 ≤ Module.finrank ℚ L) :
    (⊥ : IntermediateField ℚ L).LinearDisjoint (⊥ : IntermediateField ℚ L) ∧
      t2GramRe (fun p : Fin 1 × Fin 1 =>
          (((fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) p.1 : L) *
            ((fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) p.2 : L))) ≠
        t2GramRe (fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) ⊗ₖ
          t2GramRe (fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) := by
  refine ⟨IntermediateField.LinearDisjoint.bot_left ℚ L _, fun he => ?_⟩
  have e := congrFun (congrFun he (0, 0)) (0, 0)
  rw [kroneckerMap_apply, t2GramRe_one, IntermediateField.finrank_bot] at e
  have e2 : t2GramRe (fun p : Fin 1 × Fin 1 =>
      (((fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) p.1 : L) *
        ((fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) p.2 : L))) (0, 0) (0, 0) =
      Module.finrank ℚ L := by
    simp [t2GramRe_apply, t2Gram_apply, Embeddings.card L ℂ]
  rw [e2] at e
  have : (2 : ℝ) ≤ Module.finrank ℚ L := by exact_mod_cast h
  norm_num at e
  linarith

/-- **Control (the coordinate bound needs linear disjointness).** In a number field of degree
`n ≥ 2`, `K₁ = K₂ = ⊤` satisfy `⊤ ⊔ ⊤ = ⊤`; with `b = c = 1`, `s = t = n` (valid certificates,
the Gram entries are `n`) and `a = 1`, the bound would say `n² ≤ n`. -/
theorem control_coord_sq_le_needs_linearDisjoint (h : 2 ≤ Module.finrank ℚ L) :
    (⊤ : IntermediateField ℚ L) ⊔ ⊤ = ⊤ ∧
      ∃ (b c : Fin 1 → (⊤ : IntermediateField ℚ L)) (s t : ℝ) (a : Fin 1 × Fin 1 → ℚ),
        0 ≤ s ∧ 0 ≤ t ∧
        (∀ v : Fin 1 → ℝ, 0 ≤ v ⬝ᵥ ((t2GramRe b - diagonal (Pi.single 0 s)) *ᵥ v)) ∧
        (∀ w : Fin 1 → ℝ, 0 ≤ w ⬝ᵥ ((t2GramRe c - diagonal (Pi.single 0 t)) *ᵥ w)) ∧
        ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 <
          s * t * (a (0, 0) : ℝ) ^ 2 := by
  have hn : (2 : ℝ) ≤ Module.finrank ℚ L := by exact_mod_cast h
  have hg : t2GramRe (fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) 0 0 =
      Module.finrank ℚ L := by
    rw [t2GramRe_one, IntermediateField.finrank_top']
  refine ⟨sup_idem _, fun _ => 1, fun _ => 1, Module.finrank ℚ L, Module.finrank ℚ L,
    fun _ => 1, by positivity, by positivity, fun v => ?_, fun w => ?_, ?_⟩
  · rw [form_one_sub_diag, hg, sub_self, zero_mul]
  · rw [form_one_sub_diag, hg, sub_self, zero_mul]
  · simp [Embeddings.card L ℂ]
    nlinarith

/-- **Control (the signs of `s, t`).** With `K₁ = ⊥`, `K₂ = ⊤` in a number field of degree
`n ≥ 1` (hypotheses of the coordinate bound hold), `b = c = 1`, `s = −2`, `t = −n`: both
certificates hold, and the bound would say `2n ≤ n`. So `s, t ≥ 0` cannot both be dropped. -/
theorem control_coord_sq_le_needs_signs :
    (⊥ : IntermediateField ℚ L).LinearDisjoint (⊤ : IntermediateField ℚ L) ∧
      (⊥ : IntermediateField ℚ L) ⊔ ⊤ = ⊤ ∧
      ∃ (b : Fin 1 → (⊥ : IntermediateField ℚ L)) (c : Fin 1 → (⊤ : IntermediateField ℚ L))
        (s t : ℝ) (a : Fin 1 × Fin 1 → ℚ),
        (∀ v : Fin 1 → ℝ, 0 ≤ v ⬝ᵥ ((t2GramRe b - diagonal (Pi.single 0 s)) *ᵥ v)) ∧
        (∀ w : Fin 1 → ℝ, 0 ≤ w ⬝ᵥ ((t2GramRe c - diagonal (Pi.single 0 t)) *ᵥ w)) ∧
        ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 <
          s * t * (a (0, 0) : ℝ) ^ 2 := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hb : t2GramRe (fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) 0 0 = 1 := by
    rw [t2GramRe_one, IntermediateField.finrank_bot, Nat.cast_one]
  have hc : t2GramRe (fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) 0 0 =
      Module.finrank ℚ L := by
    rw [t2GramRe_one, IntermediateField.finrank_top']
  refine ⟨IntermediateField.LinearDisjoint.bot_left ℚ L _, bot_sup_eq _, fun _ => 1, fun _ => 1,
    -2, -(Module.finrank ℚ L : ℝ), fun _ => 1, fun v => ?_, fun w => ?_, ?_⟩
  · rw [form_one_sub_diag, hb]; nlinarith [sq_nonneg (v 0)]
  · rw [form_one_sub_diag, hc]; nlinarith [sq_nonneg (w 0)]
  · simp [Embeddings.card L ℂ]
    nlinarith

end Controls

end

end HeightT2
