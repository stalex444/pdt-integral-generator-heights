module

public import Mathlib
public import HeightT2.Compositum
public import HeightT2.Bound
public import HeightT2.Instance.SmallHeight
public import RulerSelection.Link

/-!
# The coordinate box in `L = ℚ(ρ, Q)` through the compositum Gram identity

Here `ρ` and `Q` are the adjoined roots of `X³ − X − 1` and `X⁴ − X − 1`,
`S₃ = ℚ(ρ)` and `S₄ = ℚ(Q)` inside `L = ℚ(ρ, Q)` (linearly disjoint, `S₃ ⊔ S₄ = ⊤`).
The families are `famS = (1, ρ⁻¹, ρ)` in `S₃` and `famT = (1, Q⁻¹, Q, Q²)` in `S₄`; their
products `ρ^{(a)} Q^{(b)}` form a `ℤ`-basis of `𝓞 L` (the tensor basis `tU ⊗ tV`; the chain's
tensor basis: `tens_surjective`, `tens_coords_unique`).

* `famS_ge`, `famT_ge` : the rational lower forms `Sp`, `Tp` sit below the real `T₂` Gram
  matrices of `famS` over the embeddings of `S₃` and of `famT` over those of `S₄`;
  `famS_cert`, `famT_cert` : the diagonal certificates `Re G − s E ⪰ 0` with the rational
  diagonal data `sv`, `tv`.
* `box_of_mulHeight₁_le` : an integer `x ∈ 𝓞 L` with `mulHeight₁ x ≤ mulHeight₁ (ρQ)` has every
  tensor coordinate in `{−1, 0, 1}`; derived from the general coordinate bound
  `coord_sq_le_sum_norm_sq`, the inequality `T₂ ≤ H² + 11`, and `H(ρQ)² + 11 < 24.03`.
* `box_of_embHeight_le` : the same in the product height `embHeight`, and
  `box_of_embHeight_le_chain` : the same statement derived along the earlier route
  (`height_le_imp`, `kron_lower_bound`, `nmat_identity`, `box_of_qf`);
  `box_routes_agree` : the two declarations have the same statement (checked by `rfl`, which
  is proof irrelevance). The derivation from the general coordinate bound is
  `box_of_embHeight_le`.
* `small_height_in_L12_via_compositum` : the enumeration step's input (box and the
  quadratic-form cut), with the cut obtained from the Kronecker identity
  `sum_norm_sq_compositum`.
-/

@[expose] public section

open Matrix NumberField
open scoped Kronecker

namespace HeightT2

noncomputable section

open HermiteCompositum.Instance RulerSelection.Emb RulerSelection.LaneB RulerSelection.GramCert
  RulerSelection.EnumProbe

/-- The cubic family `(1, ρ⁻¹, ρ)` in `S₃ = ℚ(ρ)`. -/
def famS : Fin 3 → S₃ := ![1, gen₃⁻¹, gen₃]

/-- The quartic family `(1, Q⁻¹, Q, Q²)` in `S₄ = ℚ(Q)`. -/
def famT : Fin 4 → S₄ := ![1, gen₄⁻¹, gen₄, gen₄ ^ 2]

theorem coe_gen₃ : ((gen₃ : S₃) : L) = ρ := algebraMap_gen₃

theorem coe_gen₄ : ((gen₄ : S₄) : L) = Q := algebraMap_gen₄

theorem famS_coe (a : Fin 3) : (famS a : L) = tU a := by
  fin_cases a <;> simp [famS, tU, coe_gen₃]

theorem famT_coe (b : Fin 4) : (famT b : L) = tV b := by
  fin_cases b <;> simp [famT, tV, coe_gen₄]

/-- The real `T₂` form of a family, for real coefficients. -/
theorem form_t2GramRe {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (b : ι → K) (v : ι → ℝ) :
    v ⬝ᵥ (t2GramRe b *ᵥ v) = ∑ σ : K →+* ℂ, ‖∑ i, (v i : ℂ) * σ (b i)‖ ^ 2 := by
  rw [sum_norm_sq_eq_form]
  rfl

theorem sum_comp_S₃ (f : (S₃ →+* ℂ) → ℝ) :
    ∑ φ : L →+* ℂ, f (φ.comp (algebraMap S₃ L)) = 4 * ∑ φ₁ : S₃ →+* ℂ, f φ₁ := by
  have e := sum_embeddings_compositum S₃_linearDisjoint_S₄ S₃_sup_S₄
    (fun φ₁ (_ : S₄ →+* ℂ) => f φ₁)
  rw [e]
  simp [Finset.sum_const, Embeddings.card _ ℂ, finrank_S₄, Finset.mul_sum]

theorem sum_comp_S₄ (f : (S₄ →+* ℂ) → ℝ) :
    ∑ φ : L →+* ℂ, f (φ.comp (algebraMap S₄ L)) = 3 * ∑ φ₂ : S₄ →+* ℂ, f φ₂ := by
  have e := sum_embeddings_compositum S₃_linearDisjoint_S₄ S₃_sup_S₄
    (fun (_ : S₃ →+* ℂ) φ₂ => f φ₂)
  rw [e]
  simp [Finset.sum_const, Embeddings.card _ ℂ, finrank_S₃, Finset.mul_sum]

/-- Power-basis coordinates of a tensor-basis coefficient vector (cubic side). -/
def wS (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => ∑ a, v a * (pu3 a i : ℝ)

/-- Power-basis coordinates of a tensor-basis coefficient vector (quartic side). -/
def wT (v : Fin 4 → ℝ) : Fin 4 → ℝ := fun j => ∑ b, v b * (pu4 b j : ℝ)

theorem form_famS (v : Fin 3 → ℝ) :
    v ⬝ᵥ (t2GramRe famS *ᵥ v) = wS v ⬝ᵥ (Smat rhoR *ᵥ wS v) := by
  have hL : ∑ φ : L →+* ℂ, ‖∑ a, (v a : ℂ) * φ (tU a)‖ ^ 2 =
      4 * (v ⬝ᵥ (t2GramRe famS *ᵥ v)) := by
    rw [form_t2GramRe, ← sum_comp_S₃]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [RingHom.comp_apply, IntermediateField.algebraMap_apply, famS_coe]
  have hM : (Matrix.of fun i k : Fin 3 => (∑ t, zs t ^ (i : ℕ) * star (zs t ^ (k : ℕ))).re) =
      Smat rhoR := by
    ext i k
    rw [of_apply]
    simp only [star_pow]
    rw [gram3, Complex.ofReal_re]
  have inner : ∀ (t : Fin 3) (q : Fin 4),
      ∑ a, (v a : ℂ) * φL (t, q) (tU a) = ∑ i, (wS v i : ℂ) * zs t ^ (i : ℕ) := by
    intro t q
    simp only [RulerSelection.Emb.tU_eq, map_sum, map_mul, map_intCast, map_pow, φL_ρ, wS]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hR : ∑ φ : L →+* ℂ, ‖∑ a, (v a : ℂ) * φ (tU a)‖ ^ 2 =
      4 * (wS v ⬝ᵥ (Smat rhoR *ᵥ wS v)) := by
    rw [sum_emb, Fintype.sum_prod_type]
    simp only [inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_norm_sq_eq_form (fun t (i : Fin 3) => zs t ^ (i : ℕ)), hM]
    norm_num
  linarith

theorem form_famT (v : Fin 4 → ℝ) :
    v ⬝ᵥ (t2GramRe famT *ᵥ v) = wT v ⬝ᵥ (Tmat QR qN *ᵥ wT v) := by
  have hL : ∑ φ : L →+* ℂ, ‖∑ b, (v b : ℂ) * φ (tV b)‖ ^ 2 =
      3 * (v ⬝ᵥ (t2GramRe famT *ᵥ v)) := by
    rw [form_t2GramRe, ← sum_comp_S₄]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [RingHom.comp_apply, IntermediateField.algebraMap_apply, famT_coe]
  have hM : (Matrix.of fun j l : Fin 4 => (∑ t, ws t ^ (j : ℕ) * star (ws t ^ (l : ℕ))).re) =
      Tmat QR qN := by
    ext j l
    rw [of_apply]
    simp only [star_pow]
    rw [gram4, Complex.ofReal_re]
  have inner : ∀ (q : Fin 3) (t : Fin 4),
      ∑ b, (v b : ℂ) * φL (q, t) (tV b) = ∑ j, (wT v j : ℂ) * ws t ^ (j : ℕ) := by
    intro q t
    simp only [RulerSelection.Emb.tV_eq, map_sum, map_mul, map_intCast, map_pow, φL_Q, wT]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hR : ∑ φ : L →+* ℂ, ‖∑ b, (v b : ℂ) * φ (tV b)‖ ^ 2 =
      3 * (wT v ⬝ᵥ (Tmat QR qN *ᵥ wT v)) := by
    rw [sum_emb, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_norm_sq_eq_form (fun t (j : Fin 4) => ws t ^ (j : ℕ)), hM]
    norm_num
  linarith

/-- The rational lower form `Sp` is below the real `T₂` Gram matrix of `famS`. -/
theorem famS_ge (v : Fin 3 → ℝ) : v ⬝ᵥ (Sp *ᵥ v) ≤ v ⬝ᵥ (t2GramRe famS *ᵥ v) := by
  rw [form_famS]
  have h1 := cubic_side_inst (wS v)
  rw [sub_mulVec, dotProduct_sub] at h1
  have h2 : wS v ⬝ᵥ (S0 *ᵥ wS v) = v ⬝ᵥ (Sp *ᵥ v) := by
    simp [wS, dotProduct, mulVec, Fin.sum_univ_three, S0, Sp, pu3]
    ring
  linarith

/-- The rational lower form `Tp` is below the real `T₂` Gram matrix of `famT`. -/
theorem famT_ge (v : Fin 4 → ℝ) : v ⬝ᵥ (Tp *ᵥ v) ≤ v ⬝ᵥ (t2GramRe famT *ᵥ v) := by
  rw [form_famT]
  have h1 := quartic_side_inst (wT v)
  rw [sub_mulVec, dotProduct_sub] at h1
  have h2 : wT v ⬝ᵥ (T0 *ᵥ wT v) = v ⬝ᵥ (Tp *ᵥ v) := by
    simp [wT, dotProduct, mulVec, Fin.sum_univ_four, T0, Tp, pu4]
    ring
  linarith

/-- The diagonal certificate on the cubic side: `Re G_famS − sv a · E_aa ⪰ 0`. -/
theorem famS_cert (a : Fin 3) (v : Fin 3 → ℝ) :
    0 ≤ v ⬝ᵥ ((t2GramRe famS - diagonal (Pi.single a (sv a))) *ᵥ v) := by
  have h := Sp_diag a v
  unfold RulerSelection.Kron.diagE at h
  rw [sub_mulVec, dotProduct_sub] at h ⊢
  linarith [famS_ge v]

/-- The diagonal certificate on the quartic side: `Re G_famT − tv b · E_bb ⪰ 0`. -/
theorem famT_cert (b : Fin 4) (v : Fin 4 → ℝ) :
    0 ≤ v ⬝ᵥ ((t2GramRe famT - diagonal (Pi.single b (tv b))) *ᵥ v) := by
  have h := Tp_diag b v
  unfold RulerSelection.Kron.diagE at h
  rw [sub_mulVec, dotProduct_sub] at h ⊢
  linarith [famT_ge v]

/-- An integer tensor-coordinate combination is the product-family sum. -/
theorem famST_sum (y : Fin 3 × Fin 4 → ℤ) :
    ∑ p, (((y p : ℚ)) : L) * (famS p.1 : L) * (famT p.2 : L) =
      ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2 := by
  simp [famS_coe, famT_coe]

/-- From a `T₂` bound below `24.03` to the box, through the general coordinate bound. -/
theorem box_of_sum_norm_sq_lt (y : Fin 3 × Fin 4 → ℤ)
    (hT : ∑ σ : L →+* ℂ, ‖σ (∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2)‖ ^ 2 < 2403 / 100)
    (d : Fin 3 × Fin 4) : -1 ≤ y d ∧ y d ≤ 1 := by
  have hc := coord_sq_le_sum_norm_sq S₃_linearDisjoint_S₄ S₃_sup_S₄ famS famT d.1 d.2
    (sv d.1) (tv d.2) (sv_pos _) (tv_pos _) (famS_cert d.1) (famT_cert d.2)
    (fun p => (y p : ℚ))
  rw [famST_sum] at hc
  have hst := svtv_ge d.1 d.2
  have hcast : (((y (d.1, d.2) : ℚ)) : ℝ) = (y d : ℝ) := by simp
  rw [hcast] at hc
  have hsq : ((y d : ℝ)) ^ 2 < 4 := by nlinarith [sq_nonneg ((y d : ℝ))]
  have hsqZ : (y d) ^ 2 < 4 := by exact_mod_cast hsq
  constructor <;> nlinarith

/-- **The box, in Mathlib's height.** An integer `x ∈ 𝓞 L` with
`mulHeight₁ x ≤ mulHeight₁ (ρQ)` has every coordinate in the basis `tU ⊗ tV` in `{−1, 0, 1}`. -/
theorem box_of_mulHeight₁_le (x : 𝓞 L)
    (h : Height.mulHeight₁ (x : L) ≤ Height.mulHeight₁ (ρ * Q))
    (y : Fin 3 × Fin 4 → ℤ) (hy : (x : L) = ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2)
    (d : Fin 3 × Fin 4) : -1 ≤ y d ∧ y d ≤ 1 := by
  refine box_of_sum_norm_sq_lt y ?_ d
  rw [← hy]
  have h1 := sum_norm_sq_le_mulHeight₁_sq_add (x : L)
  rw [finrank_L] at h1
  have h0 := Height.one_le_mulHeight₁ (x : L)
  have h2 : Height.mulHeight₁ (x : L) ^ 2 ≤ Height.mulHeight₁ (ρ * Q) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h 2
  have h3 := embHeight_ρQ_sq_add_lt
  rw [← mulHeight₁_ρQ] at h3
  push_cast at h1
  linarith

/-- **The box, in the product height.** -/
theorem box_of_embHeight_le (x : 𝓞 L)
    (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q))
    (y : Fin 3 × Fin 4 → ℤ)
    (hy : algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2)
    (d : Fin 3 × Fin 4) : -1 ≤ y d ∧ y d ≤ 1 := by
  refine box_of_mulHeight₁_le x ?_ y hy d
  rw [mulHeight₁_eq_embHeight, mulHeight₁_ρQ]
  exact h

/-- The same statement along the earlier route: `height_le_imp`, `kron_lower_bound`,
`nmat_identity`, `box_of_qf`. -/
theorem box_of_embHeight_le_chain (x : 𝓞 L)
    (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q))
    (y : Fin 3 × Fin 4 → ℤ)
    (hy : algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2)
    (d : Fin 3 × Fin 4) : -1 ≤ y d ∧ y d ≤ 1 := by
  obtain ⟨c, hc, hlt⟩ := height_le_imp x h
  obtain rfl : c = y := tens_coords_unique c y (hc.symm.trans hy)
  have h1 := RulerSelection.Kron.kron_lower_bound (fun p => (powC c p : ℝ))
  have h2 := nmat_identity c
  have hR : (qf Nmat (vecOf c) : ℝ) < 240300 := by linarith
  have hZ : qf Nmat (vecOf c) < 240300 := by exact_mod_cast hR
  exact box_of_qf c hZ.le d

/-- **Agreement.** The two declarations have the same statement (checked by `rfl`, which is
proof irrelevance). The derivation from the general coordinate bound is
`box_of_embHeight_le`. -/
theorem box_routes_agree : @box_of_embHeight_le = @box_of_embHeight_le_chain := rfl

theorem Sp_form_nonneg (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ (Sp *ᵥ v) := by
  have h := Sp_diag 0 v
  rw [sub_mulVec, dotProduct_sub, RulerSelection.Kron.diagE_form] at h
  nlinarith [sv_pos 0, sq_nonneg (v 0)]

theorem Tp_form_nonneg (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ (Tp *ᵥ v) := by
  have h := Tp_diag 0 v
  rw [sub_mulVec, dotProduct_sub, RulerSelection.Kron.diagE_form] at h
  nlinarith [tv_pos 0, sq_nonneg (v 0)]

/-- **The enumeration input through the compositum.** An integer `x ∈ 𝓞 L` of product height at
most `H(ρQ)` has tensor coordinates `y` in the enumerated list `L12`: the box from
`box_of_embHeight_le`, and the cut `qf Nmat (vecOf y) ≤ 240300` from the Kronecker identity
`sum_norm_sq_compositum` and `Sp ⊗ Tp ⪯ Re G_famS ⊗ Re G_famT`. -/
theorem small_height_in_L12_via_compositum (x : 𝓞 L)
    (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q)) :
    ∃ y : Fin 3 × Fin 4 → ℤ,
      algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2 ∧
        vecOf y ∈ L12 := by
  obtain ⟨y, hy⟩ := tens_surjective x
  refine ⟨y, hy, enum12 _ (vecOf_mem_box y (box_of_embHeight_le x h y hy)) ?_⟩
  have hT := T2_lt_of_embHeight_le _ h
  rw [RulerSelection.Emb.T2, hy] at hT
  have hform := sum_norm_sq_compositum S₃_linearDisjoint_S₄ S₃_sup_S₄ famS famT
    (fun p => (y p : ℚ))
  rw [famST_sum] at hform
  have hmono := RulerSelection.Kron.kron_form_mono (t2GramRe_isHermitian famS) Sp_herm
    (t2GramRe_isHermitian famT) Tp_herm
    (fun v => by rw [sub_mulVec, dotProduct_sub]; linarith [famS_ge v])
    (fun w => by rw [sub_mulVec, dotProduct_sub]; linarith [famT_ge w])
    Sp_form_nonneg Tp_form_nonneg (fun p => (y p : ℝ))
  have hq := qf_Nmat_eq y
  have hcast : (fun p => (((y p : ℚ)) : ℝ)) = fun p => (y p : ℝ) := by
    funext p; simp
  rw [hcast] at hform
  have hR : (qf Nmat (vecOf y) : ℝ) < 240300 := by linarith
  exact_mod_cast hR.le

end

end HeightT2
