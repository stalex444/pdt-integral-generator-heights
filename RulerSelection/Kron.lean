module

public import Mathlib
public import RulerSelection.Embeddings

/-!
# B1. The Kronecker lower bound (stage 2, lane B)

* `psd_of_form` : a real symmetric matrix whose quadratic form is nonnegative is `PosSemidef`.
* `kron_form_mono` (general) : if `A ⪰ A₀ ⪰ 0` and `B ⪰ B₀ ⪰ 0` (quadratic-form sense, all four
  symmetric), then `xᵀ (A₀ ⊗ₖ B₀) x ≤ xᵀ (A ⊗ₖ B) x`, via
  `A ⊗ B = (A − A₀) ⊗ B + A₀ ⊗ (B − B₀) + A₀ ⊗ B₀` and Mathlib's `PosSemidef.kronecker`.
* `kron_ge_diag` (general, the corrected stage-1 helper with BOTH `0 ≤ s` and `0 ≤ t`) :
  `A ⪰ s E_aa`, `B ⪰ t E_bb` ⇒ `s t x(a,b)² ≤ xᵀ (A ⊗ₖ B) x`.
* `kron_ge_diag_needs_t`, `kron_ge_diag_needs_s` (controls) : the 1×1 counterexample of
  GATE_STAGE1 F2 (`A = 1, s = 0, B = −1, t = −2`) and its mirror.
* `kron_lower_bound` (instance) : `vᵀ (S0 ⊗ₖ T0) v ≤ vᵀ (Smat rhoR ⊗ₖ Tmat QR qN) v` for all real
  `v` on `Fin 3 × Fin 4` (power basis), from `cubic_side_inst`, `quartic_side_inst`, `S0_psd`,
  `T0_psd`.
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace RulerSelection.Kron

noncomputable section

theorem psd_of_form {k : Type*} [Fintype k] {M : Matrix k k ℝ} (hM : M.IsHermitian)
    (h : ∀ v : k → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM (fun x => by simpa using h x)

theorem form_nonneg_of_psd {k : Type*} [Fintype k] {M : Matrix k k ℝ} (hM : M.PosSemidef)
    (v : k → ℝ) : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  simpa using hM.dotProduct_mulVec_nonneg v

/-- **General Kronecker monotonicity.** -/
theorem kron_form_mono {m n : Type*} [Fintype m] [Fintype n]
    {A A0 : Matrix m m ℝ} {B B0 : Matrix n n ℝ}
    (hA : A.IsHermitian) (hA0 : A0.IsHermitian) (hB : B.IsHermitian) (hB0 : B0.IsHermitian)
    (h1 : ∀ v, 0 ≤ v ⬝ᵥ ((A - A0) *ᵥ v)) (h2 : ∀ w, 0 ≤ w ⬝ᵥ ((B - B0) *ᵥ w))
    (h3 : ∀ v, 0 ≤ v ⬝ᵥ (A0 *ᵥ v)) (h4 : ∀ w, 0 ≤ w ⬝ᵥ (B0 *ᵥ w)) (x : m × n → ℝ) :
    x ⬝ᵥ ((A0 ⊗ₖ B0) *ᵥ x) ≤ x ⬝ᵥ ((A ⊗ₖ B) *ᵥ x) := by
  have hBf : ∀ w, 0 ≤ w ⬝ᵥ (B *ᵥ w) := fun w => by
    have e : w ⬝ᵥ (B *ᵥ w) = w ⬝ᵥ ((B - B0) *ᵥ w) + w ⬝ᵥ (B0 *ᵥ w) := by
      rw [sub_mulVec, dotProduct_sub]; ring
    rw [e]; exact add_nonneg (h2 w) (h4 w)
  have k1 := (psd_of_form (hA.sub hA0) h1).kronecker (psd_of_form hB hBf)
  have k2 := (psd_of_form hA0 h3).kronecker (psd_of_form (hB.sub hB0) h2)
  have e : A ⊗ₖ B = (A - A0) ⊗ₖ B + A0 ⊗ₖ (B - B0) + A0 ⊗ₖ B0 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [kroneckerMap_apply, Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [e, add_mulVec, add_mulVec, dotProduct_add, dotProduct_add]
  have := form_nonneg_of_psd k1 x
  have := form_nonneg_of_psd k2 x
  linarith

/-- The diagonal unit form `s · E_aa`. -/
def diagE {k : Type*} [DecidableEq k] (a : k) (s : ℝ) : Matrix k k ℝ := diagonal (Pi.single a s)

theorem diagE_herm {k : Type*} [DecidableEq k] (a : k) (s : ℝ) : (diagE a s).IsHermitian := by
  unfold diagE
  exact isHermitian_diagonal_of_self_adjoint _ (by simp [IsSelfAdjoint])

theorem diagE_form {k : Type*} [Fintype k] [DecidableEq k] (a : k) (s : ℝ) (v : k → ℝ) :
    v ⬝ᵥ (diagE a s *ᵥ v) = s * v a ^ 2 := by
  unfold diagE
  have hd : diagonal (Pi.single a s) *ᵥ v = fun i => (Pi.single a s : k → ℝ) i * v i := by
    funext i; exact mulVec_diagonal _ _ _
  rw [hd]
  simp only [dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · simp; ring
  · intro b _ hb; simp [hb]
  · simp

theorem diagE_kron_form {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a : m) (b : n) (s t : ℝ) (x : m × n → ℝ) :
    x ⬝ᵥ ((diagE a s ⊗ₖ diagE b t) *ᵥ x) = s * t * x (a, b) ^ 2 := by
  have : diagE a s ⊗ₖ diagE b t = diagE (a, b) (s * t) := by
    unfold diagE
    rw [diagonal_kronecker_diagonal]
    congr 1
    funext ⟨i, j⟩
    by_cases hi : i = a <;> by_cases hj : j = b <;> simp [Pi.single_apply, hi, hj]
  rw [this, diagE_form]

/-- **`kron_ge_diag`, corrected (both signs).** -/
theorem kron_ge_diag {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (a : m) (b : n) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h1 : ∀ v, 0 ≤ v ⬝ᵥ ((A - diagE a s) *ᵥ v)) (h2 : ∀ w, 0 ≤ w ⬝ᵥ ((B - diagE b t) *ᵥ w))
    (x : m × n → ℝ) : s * t * x (a, b) ^ 2 ≤ x ⬝ᵥ ((A ⊗ₖ B) *ᵥ x) := by
  rw [← diagE_kron_form]
  refine kron_form_mono hA (diagE_herm a s) hB (diagE_herm b t) h1 h2 (fun v => ?_) (fun w => ?_) x
  · rw [diagE_form]; positivity
  · rw [diagE_form]; positivity

/-- **Control (GATE_STAGE1 F2).** Without `0 ≤ t` the conclusion fails: `A = 1, s = 0,
`B = −1, t = −2` on `1 × 1`, `x = 1`. -/
theorem kron_ge_diag_needs_t :
    ¬ ∀ (A B : Matrix (Fin 1) (Fin 1) ℝ) (s t : ℝ), A.IsHermitian → B.IsHermitian → 0 ≤ s →
      (∀ v, 0 ≤ v ⬝ᵥ ((A - diagE 0 s) *ᵥ v)) → (∀ w, 0 ≤ w ⬝ᵥ ((B - diagE 0 t) *ᵥ w)) →
      ∀ x : Fin 1 × Fin 1 → ℝ, s * t * x (0, 0) ^ 2 ≤ x ⬝ᵥ ((A ⊗ₖ B) *ᵥ x) := by
  intro h
  have := h !![(1:ℝ)] !![(-1:ℝ)] 0 (-2) (by ext i j; fin_cases i; fin_cases j; simp)
    (by ext i j; fin_cases i; fin_cases j; simp) le_rfl
    (fun v => by
      simp [diagE, dotProduct, mulVec, Fin.sum_univ_one, Matrix.sub_apply] <;>
        nlinarith [sq_nonneg (v 0)])
    (fun w => by
      simp [diagE, dotProduct, mulVec, Fin.sum_univ_one, Matrix.sub_apply] <;>
        nlinarith [sq_nonneg (w 0)])
    1
  simp [dotProduct, mulVec, kroneckerMap_apply, Fin.sum_univ_one] at this
  <;> linarith

/-- **Control (mirror).** Without `0 ≤ s` the conclusion fails: `A = −1, s = −2, B = 1, t = 0`. -/
theorem kron_ge_diag_needs_s :
    ¬ ∀ (A B : Matrix (Fin 1) (Fin 1) ℝ) (s t : ℝ), A.IsHermitian → B.IsHermitian → 0 ≤ t →
      (∀ v, 0 ≤ v ⬝ᵥ ((A - diagE 0 s) *ᵥ v)) → (∀ w, 0 ≤ w ⬝ᵥ ((B - diagE 0 t) *ᵥ w)) →
      ∀ x : Fin 1 × Fin 1 → ℝ, s * t * x (0, 0) ^ 2 ≤ x ⬝ᵥ ((A ⊗ₖ B) *ᵥ x) := by
  intro h
  have := h !![(-1:ℝ)] !![(1:ℝ)] (-2) 0 (by ext i j; fin_cases i; fin_cases j; simp)
    (by ext i j; fin_cases i; fin_cases j; simp) le_rfl
    (fun v => by
      simp [diagE, dotProduct, mulVec, Fin.sum_univ_one, Matrix.sub_apply] <;>
        nlinarith [sq_nonneg (v 0)])
    (fun w => by
      simp [diagE, dotProduct, mulVec, Fin.sum_univ_one, Matrix.sub_apply] <;>
        nlinarith [sq_nonneg (w 0)])
    1
  simp [dotProduct, mulVec, kroneckerMap_apply, Fin.sum_univ_one] at this
  <;> linarith

/-! ### The instance at the actual roots -/

open RulerSelection.GramCert RulerSelection.Emb

theorem S0_herm : S0.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S0, conjTranspose_apply]

theorem T0_herm : T0.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T0, conjTranspose_apply]

theorem Smat_herm (r : ℝ) : (Smat r).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Smat, conjTranspose_apply]

theorem Tmat_herm (q q' : ℝ) : (Tmat q q').IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Tmat, conjTranspose_apply]

/-- **B1. The Kronecker lower bound at the actual roots (power basis).** -/
theorem kron_lower_bound (v : Fin 3 × Fin 4 → ℝ) :
    v ⬝ᵥ ((S0 ⊗ₖ T0) *ᵥ v) ≤ v ⬝ᵥ ((Smat rhoR ⊗ₖ Tmat QR qN) *ᵥ v) :=
  kron_form_mono (Smat_herm _) S0_herm (Tmat_herm _ _) T0_herm cubic_side_inst quartic_side_inst
    S0_psd T0_psd v

end

end RulerSelection.Kron
