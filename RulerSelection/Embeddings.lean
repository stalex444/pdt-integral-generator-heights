module

public import Mathlib
public import HermiteCompositum.Instance
public import RulerSelection.GramCert
public import RulerSelection.Threshold

/-!
# The twelve complex embeddings of `L = ℚ(ρ, Q)` (stage 2, lane A, targets A1–A2)

The field is `HermiteCompositum.Instance.L` (copied unmodified from PALOMAR-2026-10-21-000012,
`stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031`).

PORTED (namespace changed, field changed to `HermiteCompositum.Instance.L`) from the registered
entry PALOMAR-2026-10-22-000030, `cut-project-dimension@c41d9d29f9c86fb0f849df79b03e713d3405a5eb`,
`InflationDimension/Instances.lean` lines 50–235 (roots in rational boxes by the intermediate value
theorem, the non-real roots `zC`, `wC` from the real quadratic factors, the root vectors `zs`, `ws`
and their injectivity) and lines 1246–1274 (`φ₃`, `φL`, `φL_ρ`, `φL_Q`). Proofs are verbatim
except for the names of the tower and the two polynomials.

NEW here: injectivity of `p ↦ φL p`, `Fintype.card (L →+* ℂ) = 12`, the equivalence
`embEquiv : Fin 3 × Fin 4 ≃ (L →+* ℂ)`, and the instantiation of the stage-1 theorems.
-/

@[expose] public section

open Polynomial

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance

/-! ### Real roots in rational boxes (ported) -/

theorem exists_rho_box : ∃ r : ℝ, 13247 / 10000 < r ∧ r < 13248 / 10000 ∧ r ^ 3 = r + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 3 - t - 1)
      (Set.Icc (13247 / 10000) (13248 / 10000)) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (13247 / 10000 : ℝ) ≤ 13248 / 10000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 3 - t - 1) (13247 / 10000))
      ((fun t : ℝ => t ^ 3 - t - 1) (13248 / 10000)) := by
    constructor <;> norm_num
  obtain ⟨r, hr, hr0⟩ := h h0
  exact ⟨r, hr.1, hr.2, by simp only at hr0; linarith⟩

theorem exists_Q_box : ∃ q : ℝ, 12207 / 10000 < q ∧ q < 12208 / 10000 ∧ q ^ 4 = q + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 4 - t - 1)
      (Set.Icc (12207 / 10000) (12208 / 10000)) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (12207 / 10000 : ℝ) ≤ 12208 / 10000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 4 - t - 1) (12207 / 10000))
      ((fun t : ℝ => t ^ 4 - t - 1) (12208 / 10000)) := by
    constructor <;> norm_num
  obtain ⟨q, hq, hq0⟩ := h h0
  exact ⟨q, hq.1, hq.2, by simp only at hq0; linarith⟩

theorem exists_q_box : ∃ q : ℝ, -72450 / 100000 < q ∧ q < -72449 / 100000 ∧ q ^ 4 = q + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 4 - t - 1)
      (Set.Icc (-72450 / 100000) (-72449 / 100000)) := by fun_prop
  have h := intermediate_value_Ioo' (by norm_num : (-72450 / 100000 : ℝ) ≤ -72449 / 100000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 4 - t - 1) (-72449 / 100000))
      ((fun t : ℝ => t ^ 4 - t - 1) (-72450 / 100000)) := by
    constructor <;> norm_num
  obtain ⟨q, hq, hq0⟩ := h h0
  exact ⟨q, hq.1, hq.2, by simp only at hq0; linarith⟩

/-- The real root `ρ ≈ 1.32472` of `x³ − x − 1`. -/
def rhoR : ℝ := Classical.choose exists_rho_box
/-- The real root `Q ≈ 1.22074` of `x⁴ − x − 1` greater than `1`. -/
def QR : ℝ := Classical.choose exists_Q_box
/-- The negative real root `q′ ≈ −0.72449` of `x⁴ − x − 1`. -/
def qN : ℝ := Classical.choose exists_q_box

theorem rhoR_lo : 13247 / 10000 < rhoR := (Classical.choose_spec exists_rho_box).1
theorem rhoR_hi : rhoR < 13248 / 10000 := (Classical.choose_spec exists_rho_box).2.1
theorem rhoR_eq : rhoR ^ 3 = rhoR + 1 := (Classical.choose_spec exists_rho_box).2.2
theorem QR_lo : 12207 / 10000 < QR := (Classical.choose_spec exists_Q_box).1
theorem QR_hi : QR < 12208 / 10000 := (Classical.choose_spec exists_Q_box).2.1
theorem QR_eq : QR ^ 4 = QR + 1 := (Classical.choose_spec exists_Q_box).2.2
theorem qN_lo : -72450 / 100000 < qN := (Classical.choose_spec exists_q_box).1
theorem qN_hi : qN < -72449 / 100000 := (Classical.choose_spec exists_q_box).2.1
theorem qN_eq : qN ^ 4 = qN + 1 := (Classical.choose_spec exists_q_box).2.2

/-! ### The non-real roots (ported) -/

/-- The root in the upper half plane of `x² + b x + c` (when `b² < 4c`). -/
def upperRoot (b c : ℝ) : ℂ := ⟨-b / 2, Real.sqrt (4 * c - b ^ 2) / 2⟩

theorem upperRoot_im_pos {b c : ℝ} (h : b ^ 2 < 4 * c) : 0 < (upperRoot b c).im := by
  have := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 4 * c - b ^ 2)
  simp only [upperRoot]
  linarith

theorem upperRoot_add_star (b c : ℝ) : upperRoot b c + star (upperRoot b c) = -b := by
  apply Complex.ext <;> simp [upperRoot]

theorem upperRoot_mul_star {b c : ℝ} (h : b ^ 2 < 4 * c) :
    upperRoot b c * star (upperRoot b c) = c := by
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 * c - b ^ 2)
  apply Complex.ext <;> simp [upperRoot, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · ring

theorem upperRoot_normSq {b c : ℝ} (h : b ^ 2 < 4 * c) : ‖upperRoot b c‖ ^ 2 = c := by
  have h1 := upperRoot_mul_star h
  rw [show star (upperRoot b c) = (starRingEnd ℂ) (upperRoot b c) from rfl,
    Complex.mul_conj'] at h1
  exact_mod_cast h1

theorem upperRoot_quad {b c : ℝ} (h : b ^ 2 < 4 * c) :
    upperRoot b c ^ 2 + b * upperRoot b c + c = 0 := by
  linear_combination upperRoot b c * upperRoot_add_star b c - upperRoot_mul_star h

/-- The complex root `z` of `x³ − x − 1` in the upper half plane (`|z|² = ρ² − 1 = 1/ρ`). -/
def zC : ℂ := upperRoot rhoR (rhoR ^ 2 - 1)
/-- The complex root `w` of `x⁴ − x − 1` in the upper half plane (`|w|² = −1/(Q q′)`). -/
def wC : ℂ := upperRoot (QR + qN) ((QR + qN) ^ 2 - QR * qN)

theorem zC_disc : rhoR ^ 2 < 4 * (rhoR ^ 2 - 1) := by nlinarith [rhoR_lo, rhoR_hi]

theorem QqN_neg : QR * qN < 0 := by nlinarith [QR_lo, qN_hi]

theorem wC_disc : (QR + qN) ^ 2 < 4 * ((QR + qN) ^ 2 - QR * qN) := by
  nlinarith [QqN_neg, sq_nonneg (QR + qN)]

theorem zC_eq : zC ^ 3 = zC + 1 := by
  have hq := upperRoot_quad zC_disc
  have hr : ((rhoR : ℂ)) ^ 3 = rhoR + 1 := by exact_mod_cast rhoR_eq
  rw [zC]
  push_cast at hq
  linear_combination (upperRoot rhoR (rhoR ^ 2 - 1) - rhoR) * hq + hr

theorem quartic_e1 : (QR + qN) * ((QR + qN) ^ 2 - 2 * (QR * qN)) = 1 := by
  have hsub : QR - qN ≠ 0 := by nlinarith [QR_lo, qN_hi]
  have : (QR - qN) * ((QR + qN) * ((QR + qN) ^ 2 - 2 * (QR * qN)) - 1) = 0 := by
    linear_combination QR_eq - qN_eq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hsub
  · linarith

theorem quartic_e2 : (QR * qN) * ((QR + qN) ^ 2 - QR * qN) = -1 := by
  have hsub : QR - qN ≠ 0 := by nlinarith [QR_lo, qN_hi]
  have : (QR - qN) * ((QR * qN) * ((QR + qN) ^ 2 - QR * qN) + 1) = 0 := by
    linear_combination qN * QR_eq - QR * qN_eq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hsub
  · linarith

theorem wC_eq : wC ^ 4 = wC + 1 := by
  have hq := upperRoot_quad wC_disc
  have e1 : (((QR + qN) * ((QR + qN) ^ 2 - 2 * (QR * qN)) : ℝ) : ℂ) = 1 := by
    exact_mod_cast quartic_e1
  have e2 : (((QR * qN) * ((QR + qN) ^ 2 - QR * qN) : ℝ) : ℂ) = -1 := by
    exact_mod_cast quartic_e2
  rw [wC]
  push_cast at hq e1 e2
  set w := upperRoot (QR + qN) ((QR + qN) ^ 2 - QR * qN)
  linear_combination (w ^ 2 - (QR + qN) * w + QR * qN) * hq + w * e1 - e2

theorem zC_im : 0 < zC.im := upperRoot_im_pos zC_disc
theorem wC_im : 0 < wC.im := upperRoot_im_pos wC_disc

theorem zC_normSq : ‖zC‖ ^ 2 = rhoR ^ 2 - 1 := upperRoot_normSq zC_disc
theorem wC_normSq : ‖wC‖ ^ 2 = (QR + qN) ^ 2 - QR * qN := upperRoot_normSq wC_disc

theorem wC_normSq_gt : 1 < (QR + qN) ^ 2 - QR * qN := by
  nlinarith [QR_lo, QR_hi, qN_lo, qN_hi]

/-- The three roots of `x³ − x − 1`. -/
def zs : Fin 3 → ℂ := ![(rhoR : ℂ), zC, star zC]
/-- The four roots of `x⁴ − x − 1`. -/
def ws : Fin 4 → ℂ := ![(QR : ℂ), (qN : ℂ), wC, star wC]

theorem zs_eq (k : Fin 3) : zs k ^ 3 = zs k + 1 := by
  fin_cases k
  · simp only [zs]; norm_num; exact_mod_cast rhoR_eq
  · simpa [zs] using zC_eq
  · have := congrArg star zC_eq
    simpa [zs] using this

theorem ws_eq (l : Fin 4) : ws l ^ 4 = ws l + 1 := by
  fin_cases l
  · simp only [ws]; norm_num; exact_mod_cast QR_eq
  · simp only [ws]; norm_num; exact_mod_cast qN_eq
  · simpa [ws] using wC_eq
  · have := congrArg star wC_eq
    simpa [ws] using this

theorem zs_injective : Function.Injective zs := by
  have h1 : (rhoR : ℂ) ≠ zC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [zC_im]
  have h2 : (rhoR : ℂ) ≠ star zC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [zC_im]
  have h3 : zC ≠ star zC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [zC_im]
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd h h1 | exact absurd h h1.symm | exact absurd h h2 | exact absurd h h2.symm
    | exact absurd h h3 | exact absurd h h3.symm

theorem ws_injective : Function.Injective ws := by
  have h0 : (QR : ℂ) ≠ (qN : ℂ) := fun h => by
    have := Complex.ofReal_injective h; linarith [QR_lo, qN_hi]
  have h1 : (QR : ℂ) ≠ wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h2 : (QR : ℂ) ≠ star wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h3 : (qN : ℂ) ≠ wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h4 : (qN : ℂ) ≠ star wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h5 : wC ≠ star wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd h h0 | exact absurd h h0.symm | exact absurd h h1 | exact absurd h h1.symm
    | exact absurd h h2 | exact absurd h h2.symm | exact absurd h h3 | exact absurd h h3.symm
    | exact absurd h h4 | exact absurd h h4.symm | exact absurd h h5 | exact absurd h h5.symm

/-! ### The embeddings of `L` (ported, over `HermiteCompositum.Instance.L`) -/

/-- The complex embedding of `K₃ = ℚ[X]/(X³ − X − 1)` sending the root to `zs k`. -/
def φ₃ (k : Fin 3) : K₃ →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℚ ℂ) (zs k) (by
    simp [HermiteCompositum.Port014.fρ]
    linear_combination zs_eq k)

/-- The complex embedding of `L` sending `ρ ↦ zs p.1` and `Q ↦ ws p.2`. -/
def φL (p : Fin 3 × Fin 4) : L →+* ℂ :=
  AdjoinRoot.lift (φ₃ p.1) (ws p.2) (by
    rw [g, Polynomial.eval₂_map]
    simp [HermiteCompositum.Port014.fQ]
    linear_combination ws_eq p.2)

theorem φL_ρ (p : Fin 3 × Fin 4) : φL p ρ = zs p.1 := by
  simp only [φL, φ₃, HermiteCompositum.Instance.ρ, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.lift_of, AdjoinRoot.lift_root]

theorem φL_Q (p : Fin 3 × Fin 4) : φL p Q = ws p.2 := by
  simp only [φL, HermiteCompositum.Instance.Q, AdjoinRoot.lift_root]

/-! ### New: the embedding table is all of `L →+* ℂ` -/

theorem φL_injective : Function.Injective φL := by
  intro p q h
  have h1 : zs p.1 = zs q.1 := by rw [← φL_ρ, ← φL_ρ, h]
  have h2 : ws p.2 = ws q.2 := by rw [← φL_Q, ← φL_Q, h]
  exact Prod.ext (zs_injective h1) (ws_injective h2)

/-- `L` has exactly twelve complex embeddings. -/
theorem card_emb : Fintype.card (L →+* ℂ) = 12 := by
  rw [NumberField.Embeddings.card L ℂ, finrank_L]

theorem φL_bijective : Function.Bijective φL := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨φL_injective, by rw [card_emb]; rfl⟩

/-- The twelve embeddings indexed by the pairs (cubic root, quartic root). -/
def embEquiv : Fin 3 × Fin 4 ≃ (L →+* ℂ) := Equiv.ofBijective φL φL_bijective

theorem embEquiv_apply (p : Fin 3 × Fin 4) : embEquiv p = φL p := rfl

theorem embEquiv_ρ (p : Fin 3 × Fin 4) : embEquiv p ρ = zs p.1 := φL_ρ p

theorem embEquiv_Q (p : Fin 3 × Fin 4) : embEquiv p Q = ws p.2 := φL_Q p

/-- Reindexing a sum over the embeddings of `L` by the pairs of roots. -/
theorem sum_emb {M : Type*} [AddCommMonoid M] (f : (L →+* ℂ) → M) :
    ∑ σ : L →+* ℂ, f σ = ∑ p : Fin 3 × Fin 4, f (φL p) :=
  (embEquiv.sum_comp f).symm

/-- Reindexing a product over the embeddings of `L` by the pairs of roots. -/
theorem prod_emb {M : Type*} [CommMonoid M] (f : (L →+* ℂ) → M) :
    ∏ σ : L →+* ℂ, f σ = ∏ p : Fin 3 × Fin 4, f (φL p) :=
  (embEquiv.prod_comp f).symm

/-! ### New: the three reals satisfy the stage-1 hypotheses, and are the only reals that do -/

theorem rhoR_gt_one : 1 < rhoR := by linarith [rhoR_lo]
theorem QR_gt_one : 1 < QR := by linarith [QR_lo]
theorem qN_neg : qN < 0 := by linarith [qN_hi]

theorem rhoR_spec : rhoR ^ 3 = rhoR + 1 ∧ 1 < rhoR := ⟨rhoR_eq, rhoR_gt_one⟩
theorem QR_spec : QR ^ 4 = QR + 1 ∧ 1 < QR := ⟨QR_eq, QR_gt_one⟩
theorem qN_spec : qN ^ 4 = qN + 1 ∧ qN < 0 := ⟨qN_eq, qN_neg⟩

/-- Uniqueness: `rhoR` is the only real `r > 1` with `r³ = r + 1`. -/
theorem rhoR_unique (r : ℝ) (h : r ^ 3 = r + 1) (h1 : 1 < r) : r = rhoR := by
  have h2 := rhoR_eq
  have hpos : 0 < r ^ 2 + r * rhoR + rhoR ^ 2 - 1 := by nlinarith [rhoR_lo]
  have : (r - rhoR) * (r ^ 2 + r * rhoR + rhoR ^ 2 - 1) = 0 := by linear_combination h - h2
  rcases mul_eq_zero.mp this with h3 | h3
  · linarith
  · linarith

/-- Uniqueness: `QR` is the only real `q > 1` with `q⁴ = q + 1`. -/
theorem QR_unique (q : ℝ) (h : q ^ 4 = q + 1) (h1 : 1 < q) : q = QR := by
  have h2 := QR_eq
  have hpos : 0 < q ^ 3 + q ^ 2 * QR + q * QR ^ 2 + QR ^ 3 - 1 := by
    nlinarith [QR_lo, mul_pos (by linarith : (0:ℝ) < q) (by linarith [QR_lo] : (0:ℝ) < QR)]
  have : (q - QR) * (q ^ 3 + q ^ 2 * QR + q * QR ^ 2 + QR ^ 3 - 1) = 0 := by
    linear_combination h - h2
  rcases mul_eq_zero.mp this with h3 | h3
  · linarith
  · linarith

/-- Uniqueness: `qN` is the only real `q < 0` with `q⁴ = q + 1`. -/
theorem qN_unique (q : ℝ) (h : q ^ 4 = q + 1) (h0 : q < 0) : q = qN := by
  have h2 := qN_eq
  -- for two negatives every term of the cubic cofactor `q³ + q²q' + q q'² + q'³ - 1` is negative
  have a1 : q ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ h0
  have a2 : q ^ 2 * qN < 0 := mul_neg_of_pos_of_neg (by nlinarith) qN_neg
  have a3 : q * qN ^ 2 < 0 := mul_neg_of_neg_of_pos h0 (by nlinarith [qN_neg])
  have a4 : qN ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ qN_neg
  have hneg : q ^ 3 + q ^ 2 * qN + q * qN ^ 2 + qN ^ 3 - 1 < 0 := by linarith
  have : (q - qN) * (q ^ 3 + q ^ 2 * qN + q * qN ^ 2 + qN ^ 3 - 1) = 0 := by
    linear_combination h - h2
  rcases mul_eq_zero.mp this with h3 | h3
  · linarith
  · linarith

/-! ### New: the stage-1 theorems instantiated at the actual roots -/

open Matrix in
theorem cubic_side_inst (v : Fin 3 → ℝ) :
    0 ≤ v ⬝ᵥ ((RulerSelection.GramCert.Smat rhoR - RulerSelection.GramCert.S0) *ᵥ v) :=
  RulerSelection.GramCert.cubic_side rhoR rhoR_eq rhoR_gt_one v

open Matrix in
theorem quartic_side_inst (v : Fin 4 → ℝ) :
    0 ≤ v ⬝ᵥ ((RulerSelection.GramCert.Tmat QR qN - RulerSelection.GramCert.T0) *ᵥ v) :=
  RulerSelection.GramCert.quartic_side QR qN QR_eq QR_gt_one qN_eq qN_neg v

theorem threshold_inst : (rhoR ^ 2 * QR ^ 2 / (-qN)) ^ 2 + 11 < 2403 / 100 :=
  RulerSelection.GramCert.threshold rhoR QR qN rhoR_eq rhoR_gt_one QR_eq QR_gt_one qN_eq qN_neg

end

end RulerSelection.Emb
