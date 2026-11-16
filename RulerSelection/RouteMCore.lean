module

public import Mathlib
public import RulerSelection.Link
public import RulerSelection.HeightExtra

/-!
# C1 core: route M machinery (stage 2, lane C)

For a power-coordinate vector `A : Fin 3 × Fin 4 → ℤ`, `powElemF A = ∑ A(i,j) ρ^i Q^j ∈ L` and
`Vz z w A = ∑ A(i,j) z^i w^j ∈ ℂ`; `φL p (powElemF A) = Vz (zs p.1) (ws p.2) A`, so
`embHeight (powElemF A) = ∏_p max 1 ‖Vz (zs p.1) (ws p.2) A‖`.

The real and imaginary parts of `Vz` are linear in the twelve numbers `REf z w i j = (z^i w^j).re`
and `IMf z w i j = (z^i w^j).im`; these are polynomials in six positive reals
`rhoR, QR, nN = −qN, Cw = (QR + qN)/2, zi = Im zC, wi = Im wC`, bounded on rational boxes.

Conjugate embeddings have equal moduli (`norm_02_03` etc.), so seven classes cover all twelve.
-/

@[expose] public section

open NumberField

namespace RulerSelection.LaneC

noncomputable section

open RulerSelection.Emb RulerSelection.LaneB HermiteCompositum.Instance

/-- `∑ A(i,j) z^i w^j`. -/
def Vz (z w : ℂ) (A : Fin 3 × Fin 4 → ℤ) : ℂ :=
  ∑ p : Fin 3 × Fin 4, (A p : ℂ) * (z ^ (p.1 : ℕ) * w ^ (p.2 : ℕ))

/-- The element `∑ A(i,j) ρ^i Q^j` of `L`. -/
def powElemF (A : Fin 3 × Fin 4 → ℤ) : L :=
  ∑ p : Fin 3 × Fin 4, (A p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ)

theorem φL_powElemF (A : Fin 3 × Fin 4 → ℤ) (p : Fin 3 × Fin 4) :
    φL p (powElemF A) = Vz (zs p.1) (ws p.2) A := by
  simp only [powElemF, Vz, map_sum, map_mul, map_pow, map_intCast, φL_ρ, φL_Q, mul_assoc]

theorem embHeight_powElemF (A : Fin 3 × Fin 4 → ℤ) :
    embHeight (powElemF A) = ∏ p : Fin 3 × Fin 4, max 1 ‖Vz (zs p.1) (ws p.2) A‖ := by
  rw [embHeight, prod_emb]
  exact Finset.prod_congr rfl fun p _ => by rw [φL_powElemF]

theorem Vz_star (z w : ℂ) (A : Fin 3 × Fin 4 → ℤ) :
    Vz (star z) (star w) A = star (Vz z w A) := by
  simp only [Vz, star_sum, star_mul', star_pow, star_intCast]

/-- `(z^i w^j).re`. -/
def REf (z w : ℂ) (i j : ℕ) : ℝ := (z ^ i * w ^ j).re
/-- `(z^i w^j).im`. -/
def IMf (z w : ℂ) (i j : ℕ) : ℝ := (z ^ i * w ^ j).im

theorem intmul_re (n : ℤ) (x : ℂ) : ((n : ℂ) * x).re = n * x.re := by simp [Complex.mul_re]
theorem intmul_im (n : ℤ) (x : ℂ) : ((n : ℂ) * x).im = n * x.im := by simp [Complex.mul_im]

theorem Vz_eq (z w : ℂ) (A : Fin 3 × Fin 4 → ℤ) : Vz z w A =
    (A (0, 0) : ℂ) * (z ^ 0 * w ^ 0) + (A (0, 1) : ℂ) * (z ^ 0 * w ^ 1) +
    (A (0, 2) : ℂ) * (z ^ 0 * w ^ 2) + (A (0, 3) : ℂ) * (z ^ 0 * w ^ 3) +
    ((A (1, 0) : ℂ) * (z ^ 1 * w ^ 0) + (A (1, 1) : ℂ) * (z ^ 1 * w ^ 1) +
    (A (1, 2) : ℂ) * (z ^ 1 * w ^ 2) + (A (1, 3) : ℂ) * (z ^ 1 * w ^ 3)) +
    ((A (2, 0) : ℂ) * (z ^ 2 * w ^ 0) + (A (2, 1) : ℂ) * (z ^ 2 * w ^ 1) +
    (A (2, 2) : ℂ) * (z ^ 2 * w ^ 2) + (A (2, 3) : ℂ) * (z ^ 2 * w ^ 3)) := by
  simp only [Vz, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four]
  rfl

theorem Vz_re_eq (z w : ℂ) (A : Fin 3 × Fin 4 → ℤ) : (Vz z w A).re =
    (A (0, 0) : ℝ) * REf z w 0 0 + (A (0, 1) : ℝ) * REf z w 0 1 +
    (A (0, 2) : ℝ) * REf z w 0 2 + (A (0, 3) : ℝ) * REf z w 0 3 +
    ((A (1, 0) : ℝ) * REf z w 1 0 + (A (1, 1) : ℝ) * REf z w 1 1 +
    (A (1, 2) : ℝ) * REf z w 1 2 + (A (1, 3) : ℝ) * REf z w 1 3) +
    ((A (2, 0) : ℝ) * REf z w 2 0 + (A (2, 1) : ℝ) * REf z w 2 1 +
    (A (2, 2) : ℝ) * REf z w 2 2 + (A (2, 3) : ℝ) * REf z w 2 3) := by
  rw [Vz_eq]; simp only [Complex.add_re, intmul_re, REf]

theorem Vz_im_eq (z w : ℂ) (A : Fin 3 × Fin 4 → ℤ) : (Vz z w A).im =
    (A (0, 0) : ℝ) * IMf z w 0 0 + (A (0, 1) : ℝ) * IMf z w 0 1 +
    (A (0, 2) : ℝ) * IMf z w 0 2 + (A (0, 3) : ℝ) * IMf z w 0 3 +
    ((A (1, 0) : ℝ) * IMf z w 1 0 + (A (1, 1) : ℝ) * IMf z w 1 1 +
    (A (1, 2) : ℝ) * IMf z w 1 2 + (A (1, 3) : ℝ) * IMf z w 1 3) +
    ((A (2, 0) : ℝ) * IMf z w 2 0 + (A (2, 1) : ℝ) * IMf z w 2 1 +
    (A (2, 2) : ℝ) * IMf z w 2 2 + (A (2, 3) : ℝ) * IMf z w 2 3) := by
  rw [Vz_eq]; simp only [Complex.add_im, intmul_im, IMf]

/-! ### Conjugate classes -/

theorem zs0_star : star (zs 0) = zs 0 := by
  show star ((rhoR : ℝ) : ℂ) = _; rw [Complex.star_def, Complex.conj_ofReal]; rfl
theorem ws0_star : star (ws 0) = ws 0 := by
  show star ((QR : ℝ) : ℂ) = _; rw [Complex.star_def, Complex.conj_ofReal]; rfl
theorem ws1_star : star (ws 1) = ws 1 := by
  show star ((qN : ℝ) : ℂ) = _; rw [Complex.star_def, Complex.conj_ofReal]; rfl

theorem norm_03 (A : Fin 3 × Fin 4 → ℤ) : ‖Vz (zs 0) (ws 3) A‖ = ‖Vz (zs 0) (ws 2) A‖ := by
  have : Vz (zs 0) (ws 3) A = star (Vz (zs 0) (ws 2) A) := by
    rw [← Vz_star, zs0_star]; rfl
  rw [this, norm_star]
theorem norm_20 (A : Fin 3 × Fin 4 → ℤ) : ‖Vz (zs 2) (ws 0) A‖ = ‖Vz (zs 1) (ws 0) A‖ := by
  have : Vz (zs 2) (ws 0) A = star (Vz (zs 1) (ws 0) A) := by
    rw [← Vz_star, ws0_star]; rfl
  rw [this, norm_star]
theorem norm_21 (A : Fin 3 × Fin 4 → ℤ) : ‖Vz (zs 2) (ws 1) A‖ = ‖Vz (zs 1) (ws 1) A‖ := by
  have : Vz (zs 2) (ws 1) A = star (Vz (zs 1) (ws 1) A) := by
    rw [← Vz_star, ws1_star]; rfl
  rw [this, norm_star]
theorem norm_22 (A : Fin 3 × Fin 4 → ℤ) : ‖Vz (zs 2) (ws 2) A‖ = ‖Vz (zs 1) (ws 3) A‖ := by
  rw [show zs 2 = star (zs 1) from rfl, show ws 2 = star (ws 3) from (star_star wC).symm,
    Vz_star, norm_star]
theorem norm_23 (A : Fin 3 × Fin 4 → ℤ) : ‖Vz (zs 2) (ws 3) A‖ = ‖Vz (zs 1) (ws 2) A‖ := by
  rw [show zs 2 = star (zs 1) from rfl, show ws 3 = star (ws 2) from rfl, Vz_star, norm_star]

/-! ### The six positive reals and the root vectors as `⟨re, im⟩` -/

/-- `n = −q′ > 0`. -/
def nN : ℝ := -qN
/-- `C = −Re w = (Q + q′)/2 > 0`. -/
def Cw : ℝ := (QR + qN) / 2
/-- `Im z > 0`. -/
def zi : ℝ := zC.im
/-- `Im w > 0`. -/
def wi : ℝ := wC.im

theorem zs0_mk : zs 0 = ⟨rhoR, 0⟩ := rfl
theorem zs1_mk : zs 1 = ⟨-rhoR / 2, zi⟩ := rfl
theorem ws0_mk : ws 0 = ⟨QR, 0⟩ := rfl
theorem ws1_mk : ws 1 = ⟨-nN, 0⟩ := Complex.ext (by simp [ws, nN]) (by simp [ws])
theorem ws2_mk : ws 2 = ⟨-Cw, wi⟩ := Complex.ext (by simp [ws, wC, upperRoot, Cw]; ring) rfl
theorem ws3_mk : ws 3 = ⟨-Cw, -wi⟩ :=
  Complex.ext (by simp [ws, wC, upperRoot, Cw]; ring) (by simp [ws, wi])

theorem nN_eq : nN ^ 4 + nN - 1 = 0 := by
  have := qN_eq; simp only [nN]; linear_combination this

theorem zi_def : zi = Real.sqrt (4 * (rhoR ^ 2 - 1) - rhoR ^ 2) / 2 := rfl
theorem wi_def : wi = Real.sqrt (4 * ((QR + qN) ^ 2 - QR * qN) - (QR + qN) ^ 2) / 2 := rfl

/-! ### Generic interval lemmas -/

theorem mono_bounds {x lo hi : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ x) (h2 : x ≤ hi) (n : ℕ) :
    lo ^ n ≤ x ^ n ∧ x ^ n ≤ hi ^ n :=
  ⟨pow_le_pow_left₀ h0 h1 n, pow_le_pow_left₀ (h0.trans h1) h2 n⟩

theorem mul_bounds {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) : a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

theorem rho_gt (a : ℝ) (ha : 1 ≤ a) (h : a ^ 3 - a - 1 < 0) : a < rhoR := by
  by_contra hc; push Not at hc
  have := rhoR_eq; have h1 := rhoR_gt_one
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (by nlinarith : (0:ℝ) ≤ a ^ 2 + a * rhoR + rhoR ^ 2 - 1)]

theorem rho_lt (b : ℝ) (hb : 1 ≤ b) (h : 0 < b ^ 3 - b - 1) : rhoR < b := by
  by_contra hc; push Not at hc
  have := rhoR_eq; have h1 := rhoR_gt_one
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (by nlinarith : (0:ℝ) ≤ b ^ 2 + b * rhoR + rhoR ^ 2 - 1)]

theorem Q_gt (a : ℝ) (ha : 1 ≤ a) (h : a ^ 4 - a - 1 < 0) : a < QR := by
  by_contra hc; push Not at hc
  have := QR_eq; have h1 := QR_gt_one
  nlinarith [mul_nonneg (sub_nonneg.2 hc)
    (by nlinarith : (0:ℝ) ≤ a ^ 3 + a ^ 2 * QR + a * QR ^ 2 + QR ^ 3 - 1)]

theorem Q_lt (b : ℝ) (hb : 1 ≤ b) (h : 0 < b ^ 4 - b - 1) : QR < b := by
  by_contra hc; push Not at hc
  have := QR_eq; have h1 := QR_gt_one
  nlinarith [mul_nonneg (sub_nonneg.2 hc)
    (by nlinarith : (0:ℝ) ≤ b ^ 3 + b ^ 2 * QR + b * QR ^ 2 + QR ^ 3 - 1)]

theorem nN_pos : 0 < nN := by simp only [nN]; linarith [qN_neg]

theorem n_gt (a : ℝ) (ha : 0 ≤ a) (h : a ^ 4 + a - 1 < 0) : a < nN := by
  by_contra hc; push Not at hc
  have := nN_eq; have h1 := nN_pos
  nlinarith [mul_nonneg (sub_nonneg.2 hc)
    (by positivity : (0:ℝ) ≤ a ^ 3 + a ^ 2 * nN + a * nN ^ 2 + nN ^ 3 + 1)]

theorem n_lt (b : ℝ) (hb : 0 ≤ b) (h : 0 < b ^ 4 + b - 1) : nN < b := by
  by_contra hc; push Not at hc
  have := nN_eq; have h1 := nN_pos
  nlinarith [mul_nonneg (sub_nonneg.2 hc)
    (by positivity : (0:ℝ) ≤ b ^ 3 + b ^ 2 * nN + b * nN ^ 2 + nN ^ 3 + 1)]

theorem half_sqrt_ge (D a : ℝ) (ha : 0 ≤ a) (h : (2 * a) ^ 2 ≤ D) : a ≤ Real.sqrt D / 2 := by
  have := (Real.le_sqrt (by linarith) (le_trans (by positivity) h)).2 h
  linarith

theorem half_sqrt_le (D b : ℝ) (hb : 0 ≤ b) (h : D ≤ (2 * b) ^ 2) : Real.sqrt D / 2 ≤ b := by
  have := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by linarith)] at this
  linarith

theorem sq_ge_pos {x lo : ℝ} (h0 : 0 ≤ lo) (h : lo ≤ x) : lo ^ 2 ≤ x ^ 2 :=
  pow_le_pow_left₀ h0 h 2

theorem sq_ge_neg {x hi : ℝ} (h0 : hi ≤ 0) (h : x ≤ hi) : hi ^ 2 ≤ x ^ 2 := by nlinarith

theorem norm_ge_of (v : ℂ) (c a b : ℝ) (hc : 0 ≤ c) (ha : a ≤ v.re ^ 2) (hb : b ≤ v.im ^ 2)
    (h : c ^ 2 ≤ a + b) : c ≤ ‖v‖ := by
  have h1 : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  by_contra hlt; push Not at hlt
  nlinarith [norm_nonneg v]

end

end RulerSelection.LaneC
