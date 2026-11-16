module

public import Mathlib
public import HeightT2.Compositum

/-!
# Statement-review probes for the compositum Gram identity and the coordinate bound

* `kron_needs_linearDisjoint` : with `K₁ = K₂ = ⊤` (`⊤ ⊔ ⊤ = ⊤`, not linearly disjoint when
  `n ≥ 2`) the Kronecker identity fails (`n` against `n²`).
* `coord_needs_hb`, `coord_needs_hc` : deleting either certificate breaks the coordinate bound
  (all other hypotheses hold, with `K₁ = ⊥`, `K₂ = ⊤`).
* `coord_of_hs_only` : the coordinate bound holds with the hypothesis `0 ≤ t` deleted, so each
  sign hypothesis alone is redundant (only both together are needed).
* `coord_attained` : all hypotheses hold jointly on `K₁ = ⊥`, `K₂ = ⊤`, `b = c = 1`, `s = 1`,
  `t = n`, `a = 1`, and the bound is an equality there.
* `t2GramRe_diag` : the diagonal of the real Gram matrix is `∑_σ ‖σ x‖²`, the usual `T₂`.
* `t2Gram_eq_trace_of_isReal` : when every embedding is real, the Gram entry is the trace form
  `Tr (b i * b k)`; in general it is the Hermitian form, not the trace form.
-/

@[expose] public section

open Matrix NumberField
open scoped Kronecker

namespace HeightT2.Review

noncomputable section

variable {L : Type*} [Field L] [NumberField L]

/-- The Kronecker identity needs linear disjointness. -/
theorem kron_needs_linearDisjoint (h : 2 ≤ Module.finrank ℚ L) :
    (⊤ : IntermediateField ℚ L) ⊔ ⊤ = ⊤ ∧
      t2GramRe (fun p : Fin 1 × Fin 1 =>
          (((fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) p.1 : L) *
            ((fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) p.2 : L))) ≠
        t2GramRe (fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) ⊗ₖ
          t2GramRe (fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) := by
  refine ⟨sup_idem _, fun he => ?_⟩
  have e := congrFun (congrFun he (0, 0)) (0, 0)
  rw [kroneckerMap_apply, t2GramRe_one, IntermediateField.finrank_top'] at e
  have e2 : t2GramRe (fun p : Fin 1 × Fin 1 =>
      (((fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) p.1 : L) *
        ((fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) p.2 : L))) (0, 0) (0, 0) =
      Module.finrank ℚ L := by
    simp [t2GramRe_apply, t2Gram_apply, Embeddings.card L ℂ]
  rw [e2] at e
  have : (2 : ℝ) ≤ Module.finrank ℚ L := by exact_mod_cast h
  nlinarith

/-- Deleting the first certificate breaks the coordinate bound. -/
theorem coord_needs_hb :
    (⊥ : IntermediateField ℚ L).LinearDisjoint (⊤ : IntermediateField ℚ L) ∧
      (⊥ : IntermediateField ℚ L) ⊔ ⊤ = ⊤ ∧
      ∃ (b : Fin 1 → (⊥ : IntermediateField ℚ L)) (c : Fin 1 → (⊤ : IntermediateField ℚ L))
        (s t : ℝ) (a : Fin 1 × Fin 1 → ℚ),
        0 ≤ s ∧ 0 ≤ t ∧
        (∀ w : Fin 1 → ℝ, 0 ≤ w ⬝ᵥ ((t2GramRe c - diagonal (Pi.single 0 t)) *ᵥ w)) ∧
        ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 <
          s * t * (a (0, 0) : ℝ) ^ 2 := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : t2GramRe (fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) 0 0 =
      Module.finrank ℚ L := by
    rw [t2GramRe_one, IntermediateField.finrank_top']
  refine ⟨IntermediateField.LinearDisjoint.bot_left ℚ L _, bot_sup_eq _, fun _ => 1, fun _ => 1,
    2, Module.finrank ℚ L, fun _ => 1, by norm_num, by positivity, fun w => ?_, ?_⟩
  · rw [form_one_sub_diag, hc, sub_self, zero_mul]
  · simp [Embeddings.card L ℂ]
    nlinarith

/-- Deleting the second certificate breaks the coordinate bound. -/
theorem coord_needs_hc :
    (⊥ : IntermediateField ℚ L).LinearDisjoint (⊤ : IntermediateField ℚ L) ∧
      (⊥ : IntermediateField ℚ L) ⊔ ⊤ = ⊤ ∧
      ∃ (b : Fin 1 → (⊥ : IntermediateField ℚ L)) (c : Fin 1 → (⊤ : IntermediateField ℚ L))
        (s t : ℝ) (a : Fin 1 × Fin 1 → ℚ),
        0 ≤ s ∧ 0 ≤ t ∧
        (∀ v : Fin 1 → ℝ, 0 ≤ v ⬝ᵥ ((t2GramRe b - diagonal (Pi.single 0 s)) *ᵥ v)) ∧
        ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 <
          s * t * (a (0, 0) : ℝ) ^ 2 := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hb : t2GramRe (fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) 0 0 = 1 := by
    rw [t2GramRe_one, IntermediateField.finrank_bot, Nat.cast_one]
  refine ⟨IntermediateField.LinearDisjoint.bot_left ℚ L _, bot_sup_eq _, fun _ => 1, fun _ => 1,
    1, 2 * Module.finrank ℚ L, fun _ => 1, by norm_num, by positivity, fun v => ?_, ?_⟩
  · rw [form_one_sub_diag, hb, sub_self, zero_mul]
  · simp [Embeddings.card L ℂ]
    nlinarith

/-- The coordinate bound with `0 ≤ t` deleted: still true. -/
theorem coord_of_hs_only {K₁ K₂ : IntermediateField ℚ L} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (b : ι → K₁) (c : κ → K₂)
    (i : ι) (j : κ) (s t : ℝ) (hs : 0 ≤ s)
    (hb : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ ((t2GramRe b - diagonal (Pi.single i s)) *ᵥ v))
    (hc : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ ((t2GramRe c - diagonal (Pi.single j t)) *ᵥ w))
    (a : ι × κ → ℚ) :
    s * t * (a (i, j) : ℝ) ^ 2 ≤
      ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 := by
  rcases le_or_gt 0 t with ht | ht
  · exact coord_sq_le_sum_norm_sq h₁ h₂ b c i j s t hs ht hb hc a
  · have h0 : s * t * (a (i, j) : ℝ) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs ht.le) (sq_nonneg _)
    exact h0.trans (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- All hypotheses hold jointly, and the bound is attained. -/
theorem coord_attained :
    (⊥ : IntermediateField ℚ L).LinearDisjoint (⊤ : IntermediateField ℚ L) ∧
      (⊥ : IntermediateField ℚ L) ⊔ ⊤ = ⊤ ∧
      ∃ (b : Fin 1 → (⊥ : IntermediateField ℚ L)) (c : Fin 1 → (⊤ : IntermediateField ℚ L))
        (s t : ℝ) (a : Fin 1 × Fin 1 → ℚ),
        0 ≤ s ∧ 0 ≤ t ∧
        (∀ v : Fin 1 → ℝ, 0 ≤ v ⬝ᵥ ((t2GramRe b - diagonal (Pi.single 0 s)) *ᵥ v)) ∧
        (∀ w : Fin 1 → ℝ, 0 ≤ w ⬝ᵥ ((t2GramRe c - diagonal (Pi.single 0 t)) *ᵥ w)) ∧
        ∑ σ : L →+* ℂ, ‖σ (∑ p, (a p : L) * (b p.1 : L) * (c p.2 : L))‖ ^ 2 =
          s * t * (a (0, 0) : ℝ) ^ 2 := by
  have hb : t2GramRe (fun _ : Fin 1 => (1 : (⊥ : IntermediateField ℚ L))) 0 0 = 1 := by
    rw [t2GramRe_one, IntermediateField.finrank_bot, Nat.cast_one]
  have hc : t2GramRe (fun _ : Fin 1 => (1 : (⊤ : IntermediateField ℚ L))) 0 0 =
      Module.finrank ℚ L := by
    rw [t2GramRe_one, IntermediateField.finrank_top']
  refine ⟨IntermediateField.LinearDisjoint.bot_left ℚ L _, bot_sup_eq _, fun _ => 1, fun _ => 1,
    1, Module.finrank ℚ L, fun _ => 1, by norm_num, by positivity, fun v => ?_, fun w => ?_, ?_⟩
  · rw [form_one_sub_diag, hb, sub_self, zero_mul]
  · rw [form_one_sub_diag, hc, sub_self, zero_mul]
  · simp [Embeddings.card L ℂ]

variable {K : Type*} [Field K] [NumberField K]

/-- The diagonal of the real Gram matrix is the usual `T₂ (x) = ∑_σ ‖σ x‖²`. -/
theorem t2GramRe_diag {ι : Type*} (b : ι → K) (i : ι) :
    t2GramRe b i i = ∑ σ : K →+* ℂ, ‖σ (b i)‖ ^ 2 := by
  have := sum_norm_sq_eq_t2GramRe (fun _ : Fin 1 => b i) (fun _ => 1)
  simp only [Rat.cast_one, one_mul, Finset.univ_unique, Finset.sum_singleton] at this
  rw [this]
  simp [dotProduct, mulVec, t2GramRe_apply, t2Gram_apply]

/-- When every embedding is real, the Gram entry is the trace form. -/
theorem t2Gram_eq_trace_of_isReal (hr : ∀ σ : K →+* ℂ, ComplexEmbedding.IsReal σ)
    {ι : Type*} (b : ι → K) (i k : ι) :
    t2Gram b i k = ((Algebra.trace ℚ K (b i * b k) : ℚ) : ℂ) := by
  have e := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := b i * b k)
  rw [show ((Algebra.trace ℚ K (b i * b k) : ℚ) : ℂ) =
    algebraMap ℚ ℂ (Algebra.trace ℚ K (b i * b k)) from rfl, e, t2Gram_apply]
  refine Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ)
    (fun σ : K →+* ℂ => σ (b i) * star (σ (b k))) (fun σ : K →ₐ[ℚ] ℂ => σ (b i * b k))
    fun σ => ?_
  have hσ : star (σ (b k)) = σ (b k) := by
    rw [show star (σ (b k)) = (starRingEnd ℂ) (σ (b k)) from rfl,
      ← ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.isReal_iff.1 (hr σ)]
  rw [hσ, ← map_mul]
  rfl

end

end HeightT2.Review

#print axioms HeightT2.Review.kron_needs_linearDisjoint
#print axioms HeightT2.Review.coord_needs_hb
#print axioms HeightT2.Review.coord_needs_hc
#print axioms HeightT2.Review.coord_of_hs_only
#print axioms HeightT2.Review.coord_attained
#print axioms HeightT2.Review.t2GramRe_diag
#print axioms HeightT2.Review.t2Gram_eq_trace_of_isReal
