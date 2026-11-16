module

public import Mathlib
public import RulerSelection.Embeddings

/-!
# `T₂` on `L = ℚ(ρ, Q)` in coordinates (stage 2, lane A, target A3: bridge B1)

`T2 x = ∑ σ : L →+* ℂ, ‖σ x‖²` is a sum over Mathlib's embeddings of the actual field
`HermiteCompositum.Instance.L`. For `x = ∑ a(i,j) ρ^i Q^j` (power basis, index
`p = (i, j) : Fin 3 × Fin 4`, coefficient of `ρ^i Q^j`), `T2 x = aᵀ (Smat ρ ⊗ₖ Tmat Q q′) a`
with `Smat`, `Tmat` exactly the stage-1 constants of `RulerSelection.GramCert`, evaluated at the
real roots `rhoR`, `QR`, `qN`. `Matrix.kronecker` indexes by pairs:
`(Smat ⊗ₖ Tmat) (i, j) (k, l) = Smat i k * Tmat j l`. (The stage-1 `Nmat` uses the TENSOR basis
`{1, ρ⁻¹, ρ} ⊗ {1, Q⁻¹, Q, Q²}` with flat index `4a + b`; that change of basis is not made here.)

Route: a general identity (`sum_norm_sq_tensor`): for any finite families `z`, `w` of complex
numbers whose Gram sums `∑ₜ z_t^{e i} (z_t^*)^{e k}` are (casts of) the entries of real matrices `S`,
`T`, the sum over pairs `(t₁, t₂)` of `|∑ a_p z_{t₁}^{e p.1} w_{t₂}^{f p.2}|²` is `aᵀ (S ⊗ₖ T) a`. The
two sector Gram matrices are identified with `Smat rhoR` and `Tmat QR qN` entry by entry
(25 polynomial identities, each a `linear_combination` against the root relations, cofactors
from a lex Gröbner reduction).
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance

/-- **The Kronecker Gram identity** (general). -/
theorem sum_norm_sq_tensor {m n ι κ : Type*} [Fintype m] [Fintype n] [Fintype ι] [Fintype κ]
    (z : m → ℂ) (w : n → ℂ) (e : ι → ℕ) (f : κ → ℕ) (S : Matrix ι ι ℝ) (T : Matrix κ κ ℝ)
    (hS : ∀ i k, ∑ t, z t ^ e i * star (z t) ^ e k = (S i k : ℂ))
    (hT : ∀ j l, ∑ t, w t ^ f j * star (w t) ^ f l = (T j l : ℂ))
    (a : ι × κ → ℝ) :
    ∑ t : m × n, ‖∑ p : ι × κ, (a p : ℂ) * z t.1 ^ e p.1 * w t.2 ^ f p.2‖ ^ 2
      = a ⬝ᵥ ((S ⊗ₖ T) *ᵥ a) := by
  apply Complex.ofReal_injective
  have hn : ∀ c : ℂ, ((‖c‖ ^ 2 : ℝ) : ℂ) = c * star c := fun c => by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
  have hstar : ∀ x : ℝ, star (x : ℂ) = x := fun x => Complex.conj_ofReal x
  rw [Complex.ofReal_sum]
  simp only [hn, star_sum, star_mul', star_pow, hstar]
  simp only [Finset.sum_mul_sum]
  simp only [dotProduct, mulVec, kroneckerMap_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum]
  -- LHS: ∑ t ∑ p ∑ q X t p q ;  RHS: ∑ p ∑ q a_p (S T) a_q
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← hS p.1 q.1, ← hT p.2 q.2, Fintype.sum_prod_type]
  simp only [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  ring

/-! ### The sector Gram matrices: 25 entry identities -/

theorem g3_0_0 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 0 * (r:ℂ) ^ 0 + z ^ 0 * zb ^ 0 + zb ^ 0 * z ^ 0 = (((3:ℝ) : ℝ) : ℂ) := by
  push_cast
  linear_combination 0

theorem g3_0_1 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 0 * (r:ℂ) ^ 1 + z ^ 0 * zb ^ 1 + zb ^ 0 * z ^ 1 = ((0 : ℝ) : ℂ) := by
  push_cast
  linear_combination (1) * h1

theorem g3_0_2 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 0 * (r:ℂ) ^ 2 + z ^ 0 * zb ^ 2 + zb ^ 0 * z ^ 2 = ((2 : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(r:ℂ) - z + zb) * h1 + (2) * h2

theorem g3_1_0 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 1 * (r:ℂ) ^ 0 + z ^ 1 * zb ^ 0 + zb ^ 1 * z ^ 0 = ((0 : ℝ) : ℂ) := by
  push_cast
  linear_combination (1) * h1

theorem g3_1_1 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 1 * (r:ℂ) ^ 1 + z ^ 1 * zb ^ 1 + zb ^ 1 * z ^ 1 = ((3*r^2-2 : ℝ) : ℂ) := by
  push_cast
  linear_combination (2*z) * h1 + (-2) * h2

theorem g3_1_2 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 1 * (r:ℂ) ^ 2 + z ^ 1 * zb ^ 2 + zb ^ 1 * z ^ 2 = ((r : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(r:ℂ)*z + z*zb) * h1 + ((r:ℂ)) * h2

theorem g3_2_0 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 2 * (r:ℂ) ^ 0 + z ^ 2 * zb ^ 0 + zb ^ 2 * z ^ 0 = ((2 : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(r:ℂ) - z + zb) * h1 + (2) * h2

theorem g3_2_1 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 2 * (r:ℂ) ^ 1 + z ^ 2 * zb ^ 1 + zb ^ 2 * z ^ 1 = ((r : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(r:ℂ)*z + z*zb) * h1 + ((r:ℂ)) * h2

theorem g3_2_2 (r : ℝ) (z zb : ℂ) (h1 : zb + z + (r:ℂ) = 0)
    (h2 : z ^ 2 + (r:ℂ) * z + (r:ℂ) ^ 2 - 1 = 0) (h3 : (r:ℂ) ^ 3 - (r:ℂ) - 1 = 0) :
    (r:ℂ) ^ 2 * (r:ℂ) ^ 2 + z ^ 2 * zb ^ 2 + zb ^ 2 * z ^ 2 = ((-r^2+3*r+2 : ℝ) : ℂ) := by
  push_cast
  linear_combination (-2*(r:ℂ)*z^2 - 2*z^3 + 2*z^2*zb) * h1 + (-2*(r:ℂ)^2 + 2*(r:ℂ)*z + 2*z^2 + 2) * h2 + (3*(r:ℂ)) * h3

theorem g4_0_0 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 0 * (Q:ℂ) ^ 0 + (q:ℂ) ^ 0 * (q:ℂ) ^ 0 + w ^ 0 * wb ^ 0 + wb ^ 0 * w ^ 0 =
      (((4) : ℝ) : ℂ) := by
  push_cast
  linear_combination 0

theorem g4_0_1 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 0 * (Q:ℂ) ^ 1 + (q:ℂ) ^ 0 * (q:ℂ) ^ 1 + w ^ 0 * wb ^ 1 + wb ^ 0 * w ^ 1 =
      (((0) : ℝ) : ℂ) := by
  push_cast
  linear_combination (1) * h1

theorem g4_0_2 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 0 * (Q:ℂ) ^ 2 + (q:ℂ) ^ 0 * (q:ℂ) ^ 2 + w ^ 0 * wb ^ 2 + wb ^ 0 * w ^ 2 =
      (((2*Q^3*q^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*q^1 - 2*q^3 + 2*q^2 + 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(Q:ℂ) - (q:ℂ) - w + wb) * h1 + (2) * h2 + (2 - 2*(q:ℂ)^3) * h3 + (2*(Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) + 2*(q:ℂ)^2) * h4

theorem g4_0_3 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 0 * (Q:ℂ) ^ 3 + (q:ℂ) ^ 0 * (q:ℂ) ^ 3 + w ^ 0 * wb ^ 3 + wb ^ 0 * w ^ 3 =
      (((-3*Q^3 - 3*Q^2*q^1 - 3*Q^1*q^2 - 3*q^3 + 6) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) + 2*(Q:ℂ)*w - (Q:ℂ)*wb + (q:ℂ)^2 + 2*(q:ℂ)*w - (q:ℂ)*wb + w^2 - w*wb + wb^2) * h1 + (-3*(Q:ℂ) - 3*(q:ℂ)) * h2 + (6) * h3

theorem g4_1_0 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 1 * (Q:ℂ) ^ 0 + (q:ℂ) ^ 1 * (q:ℂ) ^ 0 + w ^ 1 * wb ^ 0 + wb ^ 1 * w ^ 0 =
      (((0) : ℝ) : ℂ) := by
  push_cast
  linear_combination (1) * h1

theorem g4_1_1 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 1 * (Q:ℂ) ^ 1 + (q:ℂ) ^ 1 * (q:ℂ) ^ 1 + w ^ 1 * wb ^ 1 + wb ^ 1 * w ^ 1 =
      (((-2*Q^3*q^3 + 2*Q^3 + 1*Q^2 + 2*q^3 + 1*q^2 - 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination (2*w) * h1 + (-2) * h2 + (2*(q:ℂ)^3 - 2) * h3 + (-2*(Q:ℂ)^2 - 2*(Q:ℂ)*(q:ℂ) - 2*(q:ℂ)^2) * h4

theorem g4_1_2 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 1 * (Q:ℂ) ^ 2 + (q:ℂ) ^ 1 * (q:ℂ) ^ 2 + w ^ 1 * wb ^ 2 + wb ^ 1 * w ^ 2 =
      (((2*Q^3 + 2*q^3 - 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(Q:ℂ)*w - (q:ℂ)*w + w*wb) * h1 + ((Q:ℂ) + (q:ℂ)) * h2 + (-2) * h3

theorem g4_1_3 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 1 * (Q:ℂ) ^ 3 + (q:ℂ) ^ 1 * (q:ℂ) ^ 3 + w ^ 1 * wb ^ 3 + wb ^ 1 * w ^ 3 =
      (((-2*Q^3*q^3 + 2*Q^3*q^2 - 1*Q^3*q^1 + 2*Q^3 + 2*Q^2*q^3 - 2*Q^2*q^2 - 2*Q^2 - 1*Q^1*q^3 + 2*Q^1 + 2*q^3 - 2*q^2 + 2*q^1 - 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((Q:ℂ)^2*w + 2*(Q:ℂ)*(q:ℂ)*w + 2*(Q:ℂ)*w^2 - (Q:ℂ)*w*wb + (q:ℂ)^2*w + 2*(q:ℂ)*w^2 - (q:ℂ)*w*wb + 2*w^3 - w^2*wb + w*wb^2) * h1 + ((Q:ℂ)^2 - 2*(Q:ℂ)*w + (q:ℂ)^2 - 2*(q:ℂ)*w - 2*w^2) * h2 + (2*(q:ℂ)^3 - 2*(q:ℂ)^2 - 2) * h3 + (-2*(Q:ℂ)^2 - 2*(Q:ℂ)*(q:ℂ) + 2*(Q:ℂ) - 2*(q:ℂ)^2 + 2*(q:ℂ)) * h4

theorem g4_2_0 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 2 * (Q:ℂ) ^ 0 + (q:ℂ) ^ 2 * (q:ℂ) ^ 0 + w ^ 2 * wb ^ 0 + wb ^ 2 * w ^ 0 =
      (((2*Q^3*q^3 - 2*Q^3 + 2*Q^2 + 2*Q^1*q^1 - 2*q^3 + 2*q^2 + 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(Q:ℂ) - (q:ℂ) - w + wb) * h1 + (2) * h2 + (2 - 2*(q:ℂ)^3) * h3 + (2*(Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) + 2*(q:ℂ)^2) * h4

theorem g4_2_1 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 2 * (Q:ℂ) ^ 1 + (q:ℂ) ^ 2 * (q:ℂ) ^ 1 + w ^ 2 * wb ^ 1 + wb ^ 2 * w ^ 1 =
      (((2*Q^3 + 2*q^3 - 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(Q:ℂ)*w - (q:ℂ)*w + w*wb) * h1 + ((Q:ℂ) + (q:ℂ)) * h2 + (-2) * h3

theorem g4_2_2 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 2 * (Q:ℂ) ^ 2 + (q:ℂ) ^ 2 * (q:ℂ) ^ 2 + w ^ 2 * wb ^ 2 + wb ^ 2 * w ^ 2 =
      (((2*Q^3*q^3 - 2*Q^3*q^2 - 2*Q^3 - 2*Q^2*q^3 + 2*Q^2*q^2 + 2*Q^2 + 1*Q^1 - 2*q^3 + 2*q^2 + 1*q^1 + 4) : ℝ) : ℂ) := by
  push_cast
  linear_combination (-2*(Q:ℂ)*w^2 - 2*(q:ℂ)*w^2 - 2*w^3 + 2*w^2*wb) * h1 + (-2*(Q:ℂ)^2 - 2*(Q:ℂ)*(q:ℂ) + 2*(Q:ℂ)*w - 2*(q:ℂ)^2 + 2*(q:ℂ)*w + 2*w^2) * h2 + (3*(Q:ℂ) - 2*(q:ℂ)^3 + 2*(q:ℂ)^2 + (q:ℂ) + 2) * h3 + (2*(Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) - 2*(Q:ℂ) + 2*(q:ℂ)^2 - 2*(q:ℂ) + 2) * h4

theorem g4_2_3 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 2 * (Q:ℂ) ^ 3 + (q:ℂ) ^ 2 * (q:ℂ) ^ 3 + w ^ 2 * wb ^ 3 + wb ^ 2 * w ^ 3 =
      (((2*Q^3*q^3 - 1*Q^3*q^2 - 2*Q^3 - 1*Q^2*q^3 + 2*Q^2 + 1*Q^1 - 2*q^3 + 2*q^2 + 1*q^1 + 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((Q:ℂ)^2*w^2 + 2*(Q:ℂ)*(q:ℂ)*w^2 + (Q:ℂ)*w^3 - (Q:ℂ)*w^2*wb + (q:ℂ)^2*w^2 + (q:ℂ)*w^3 - (q:ℂ)*w^2*wb + w^2*wb^2) * h1 + ((Q:ℂ)^3 + 2*(Q:ℂ)^2*(q:ℂ) - (Q:ℂ)^2*w + 2*(Q:ℂ)*(q:ℂ)^2 - 2*(Q:ℂ)*(q:ℂ)*w - (Q:ℂ)*w^2 + (q:ℂ)^3 - (q:ℂ)^2*w - (q:ℂ)*w^2) * h2 + (-3*(Q:ℂ)*(q:ℂ) - 2*(q:ℂ)^3 - (q:ℂ)^2 + 2) * h3 + (2*(Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) + (Q:ℂ) + 2*(q:ℂ)^2 + (q:ℂ)) * h4

theorem g4_3_0 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 3 * (Q:ℂ) ^ 0 + (q:ℂ) ^ 3 * (q:ℂ) ^ 0 + w ^ 3 * wb ^ 0 + wb ^ 3 * w ^ 0 =
      (((-3*Q^3 - 3*Q^2*q^1 - 3*Q^1*q^2 - 3*q^3 + 6) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) + 2*(Q:ℂ)*w - (Q:ℂ)*wb + (q:ℂ)^2 + 2*(q:ℂ)*w - (q:ℂ)*wb + w^2 - w*wb + wb^2) * h1 + (-3*(Q:ℂ) - 3*(q:ℂ)) * h2 + (6) * h3

theorem g4_3_1 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 3 * (Q:ℂ) ^ 1 + (q:ℂ) ^ 3 * (q:ℂ) ^ 1 + w ^ 3 * wb ^ 1 + wb ^ 3 * w ^ 1 =
      (((-2*Q^3*q^3 + 2*Q^3*q^2 - 1*Q^3*q^1 + 2*Q^3 + 2*Q^2*q^3 - 2*Q^2*q^2 - 2*Q^2 - 1*Q^1*q^3 + 2*Q^1 + 2*q^3 - 2*q^2 + 2*q^1 - 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((Q:ℂ)^2*w + 2*(Q:ℂ)*(q:ℂ)*w + 2*(Q:ℂ)*w^2 - (Q:ℂ)*w*wb + (q:ℂ)^2*w + 2*(q:ℂ)*w^2 - (q:ℂ)*w*wb + 2*w^3 - w^2*wb + w*wb^2) * h1 + ((Q:ℂ)^2 - 2*(Q:ℂ)*w + (q:ℂ)^2 - 2*(q:ℂ)*w - 2*w^2) * h2 + (2*(q:ℂ)^3 - 2*(q:ℂ)^2 - 2) * h3 + (-2*(Q:ℂ)^2 - 2*(Q:ℂ)*(q:ℂ) + 2*(Q:ℂ) - 2*(q:ℂ)^2 + 2*(q:ℂ)) * h4

theorem g4_3_2 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 3 * (Q:ℂ) ^ 2 + (q:ℂ) ^ 3 * (q:ℂ) ^ 2 + w ^ 3 * wb ^ 2 + wb ^ 3 * w ^ 2 =
      (((2*Q^3*q^3 - 1*Q^3*q^2 - 2*Q^3 - 1*Q^2*q^3 + 2*Q^2 + 1*Q^1 - 2*q^3 + 2*q^2 + 1*q^1 + 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((Q:ℂ)^2*w^2 + 2*(Q:ℂ)*(q:ℂ)*w^2 + (Q:ℂ)*w^3 - (Q:ℂ)*w^2*wb + (q:ℂ)^2*w^2 + (q:ℂ)*w^3 - (q:ℂ)*w^2*wb + w^2*wb^2) * h1 + ((Q:ℂ)^3 + 2*(Q:ℂ)^2*(q:ℂ) - (Q:ℂ)^2*w + 2*(Q:ℂ)*(q:ℂ)^2 - 2*(Q:ℂ)*(q:ℂ)*w - (Q:ℂ)*w^2 + (q:ℂ)^3 - (q:ℂ)^2*w - (q:ℂ)*w^2) * h2 + (-3*(Q:ℂ)*(q:ℂ) - 2*(q:ℂ)^3 - (q:ℂ)^2 + 2) * h3 + (2*(Q:ℂ)^2 + 2*(Q:ℂ)*(q:ℂ) + (Q:ℂ) + 2*(q:ℂ)^2 + (q:ℂ)) * h4

theorem g4_3_3 (Q q : ℝ) (w wb : ℂ) (h1 : wb + w + (Q:ℂ) + (q:ℂ) = 0)
    (h2 : w ^ 2 + ((Q:ℂ) + (q:ℂ)) * w + ((Q:ℂ) + (q:ℂ)) ^ 2 - (Q:ℂ) * (q:ℂ) = 0)
    (h3 : (q:ℂ) ^ 3 + (Q:ℂ) * (q:ℂ) ^ 2 + (Q:ℂ) ^ 2 * (q:ℂ) + (Q:ℂ) ^ 3 - 1 = 0)
    (h4 : (q:ℂ) ^ 4 - (q:ℂ) - 1 = 0) :
    (Q:ℂ) ^ 3 * (Q:ℂ) ^ 3 + (q:ℂ) ^ 3 * (q:ℂ) ^ 3 + w ^ 3 * wb ^ 3 + wb ^ 3 * w ^ 3 =
      (((-2*Q^3*q^3 + 2*Q^3*q^2 - 2*Q^3*q^1 + 3*Q^3 + 2*Q^2*q^3 - 2*Q^2*q^2 + 2*Q^2*q^1 - 1*Q^2 - 2*Q^1*q^3 + 2*Q^1*q^2 - 2*Q^1*q^1 + 2*Q^1 + 3*q^3 - 1*q^2 + 2*q^1 - 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination (2*(Q:ℂ)^2*w^3 + 4*(Q:ℂ)*(q:ℂ)*w^3 + 4*(Q:ℂ)*w^4 - 2*(Q:ℂ)*w^3*wb + 2*(q:ℂ)^2*w^3 + 4*(q:ℂ)*w^4 - 2*(q:ℂ)*w^3*wb + 2*w^5 - 2*w^4*wb + 2*w^3*wb^2) * h1 + (-2*(Q:ℂ)^4 - 4*(Q:ℂ)^3*(q:ℂ) + 2*(Q:ℂ)^3*w - 6*(Q:ℂ)^2*(q:ℂ)^2 + 4*(Q:ℂ)^2*(q:ℂ)*w - 4*(Q:ℂ)*(q:ℂ)^3 + 4*(Q:ℂ)*(q:ℂ)^2*w - 2*(Q:ℂ)*(q:ℂ)*w^2 - 4*(Q:ℂ)*w^3 - 2*(q:ℂ)^4 + 2*(q:ℂ)^3*w - 4*(q:ℂ)*w^3 - 2*w^4) * h2 + (3*(Q:ℂ)^3 + 3*(Q:ℂ)^2*(q:ℂ) + 6*(Q:ℂ)*(q:ℂ)^2 + 4*(q:ℂ)^3 - 2*(q:ℂ)^2 + 2*(q:ℂ)) * h3 + (-(Q:ℂ)^2 - 4*(Q:ℂ)*(q:ℂ) + 2*(Q:ℂ) - (q:ℂ)^2 + 2*(q:ℂ) - 2) * h4


theorem gram3 (i k : Fin 3) :
    ∑ t, zs t ^ (i : ℕ) * star (zs t) ^ (k : ℕ) = ((GramCert.Smat rhoR i k : ℝ) : ℂ) := by
  have h1 : star zC + zC + (rhoR : ℂ) = 0 := by
    have := upperRoot_add_star rhoR (rhoR ^ 2 - 1)
    rw [← zC] at this; linear_combination this
  have h2 : zC ^ 2 + (rhoR : ℂ) * zC + (rhoR : ℂ) ^ 2 - 1 = 0 := by
    have := upperRoot_quad zC_disc
    rw [← zC] at this; push_cast at this; linear_combination this
  have h3 : (rhoR : ℂ) ^ 3 - (rhoR : ℂ) - 1 = 0 := by
    have : ((rhoR ^ 3 : ℝ) : ℂ) = ((rhoR + 1 : ℝ) : ℂ) := by rw [rhoR_eq]
    push_cast at this; linear_combination this
  rw [Fin.sum_univ_three, show zs 0 = (rhoR : ℂ) from rfl, show zs 1 = zC from rfl,
    show zs 2 = star zC from rfl, star_star, show star (rhoR : ℂ) = rhoR from Complex.conj_ofReal _]
  fin_cases i <;> fin_cases k
  · exact g3_0_0 rhoR zC (star zC) h1 h2 h3
  · exact g3_0_1 rhoR zC (star zC) h1 h2 h3
  · exact g3_0_2 rhoR zC (star zC) h1 h2 h3
  · exact g3_1_0 rhoR zC (star zC) h1 h2 h3
  · exact g3_1_1 rhoR zC (star zC) h1 h2 h3
  · exact g3_1_2 rhoR zC (star zC) h1 h2 h3
  · exact g3_2_0 rhoR zC (star zC) h1 h2 h3
  · exact g3_2_1 rhoR zC (star zC) h1 h2 h3
  · exact g3_2_2 rhoR zC (star zC) h1 h2 h3

theorem gram4 (j l : Fin 4) :
    ∑ t, ws t ^ (j : ℕ) * star (ws t) ^ (l : ℕ) = ((GramCert.Tmat QR qN j l : ℝ) : ℂ) := by
  have h1 : star wC + wC + (QR : ℂ) + (qN : ℂ) = 0 := by
    have := upperRoot_add_star (QR + qN) ((QR + qN) ^ 2 - QR * qN)
    rw [← wC] at this; push_cast at this; linear_combination this
  have h2 : wC ^ 2 + ((QR : ℂ) + (qN : ℂ)) * wC + ((QR : ℂ) + (qN : ℂ)) ^ 2 - (QR : ℂ) * (qN : ℂ)
      = 0 := by
    have := upperRoot_quad wC_disc
    rw [← wC] at this; push_cast at this; linear_combination this
  have h3 : (qN : ℂ) ^ 3 + (QR : ℂ) * (qN : ℂ) ^ 2 + (QR : ℂ) ^ 2 * (qN : ℂ) + (QR : ℂ) ^ 3 - 1
      = 0 := by
    have := GramCert.Qprime_cubic QR qN QR_eq qN_eq (by linarith [QR_lo, qN_hi])
    have h : (((qN ^ 3 + QR * qN ^ 2 + QR ^ 2 * qN + QR ^ 3 - 1 : ℝ)) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [this]
    push_cast at h; linear_combination h
  have h4 : (qN : ℂ) ^ 4 - (qN : ℂ) - 1 = 0 := by
    have : ((qN ^ 4 : ℝ) : ℂ) = ((qN + 1 : ℝ) : ℂ) := by rw [qN_eq]
    push_cast at this; linear_combination this
  rw [Fin.sum_univ_four, show ws 0 = (QR : ℂ) from rfl, show ws 1 = (qN : ℂ) from rfl,
    show ws 2 = wC from rfl, show ws 3 = star wC from rfl, star_star,
    show star (QR : ℂ) = QR from Complex.conj_ofReal _,
    show star (qN : ℂ) = qN from Complex.conj_ofReal _]
  fin_cases j <;> fin_cases l
  · exact g4_0_0 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_0_1 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_0_2 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_0_3 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_1_0 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_1_1 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_1_2 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_1_3 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_2_0 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_2_1 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_2_2 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_2_3 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_3_0 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_3_1 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_3_2 QR qN wC (star wC) h1 h2 h3 h4
  · exact g4_3_3 QR qN wC (star wC) h1 h2 h3 h4

/-! ### `T₂` -/

/-- `T₂(x) = ∑_σ ‖σ x‖²` over all ring homomorphisms `L →+* ℂ` (Mathlib's `Fintype` instance). -/
def T2 (x : L) : ℝ := ∑ σ : L →+* ℂ, ‖σ x‖ ^ 2

/-- **Bridge B1.** `T₂` of `∑ a(i,j) ρ^i Q^j` is the Kronecker quadratic form of the stage-1
matrices `Smat rhoR` and `Tmat QR qN`. -/
theorem T2_coords (a : Fin 3 × Fin 4 → ℤ) :
    T2 (∑ p : Fin 3 × Fin 4, (a p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ)) =
      (fun p => (a p : ℝ)) ⬝ᵥ ((GramCert.Smat rhoR ⊗ₖ GramCert.Tmat QR qN) *ᵥ
        (fun p => (a p : ℝ))) := by
  rw [T2, sum_emb, ← sum_norm_sq_tensor zs ws (fun i : Fin 3 => (i : ℕ)) (fun j : Fin 4 => (j : ℕ))
    _ _ gram3 gram4 (fun p => (a p : ℝ))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [map_sum, map_mul, map_pow, map_intCast, φL_ρ, φL_Q, Complex.ofReal_intCast]

/-- **Control.** `T₂(1) = 12` (directly from the definition and `card_emb`). -/
theorem T2_one : T2 1 = 12 := by
  simp [T2, card_emb]

/-- **Control.** `T₂(ρ) = 4 (3ρ² − 2)` computed directly from the embeddings (`|z|² = ρ² − 1`),
independently of the Gram identities. -/
theorem T2_ρ : T2 ρ = 4 * (3 * rhoR ^ 2 - 2) := by
  rw [T2, sum_emb, Fintype.sum_prod_type]
  simp only [φL_ρ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fin.sum_univ_three]
  have h1 : ‖zs 0‖ ^ 2 = rhoR ^ 2 := by
    show ‖(rhoR : ℂ)‖ ^ 2 = rhoR ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : ‖zs 1‖ ^ 2 = rhoR ^ 2 - 1 := zC_normSq
  have h3 : ‖zs 2‖ ^ 2 = rhoR ^ 2 - 1 := by
    show ‖star zC‖ ^ 2 = rhoR ^ 2 - 1
    rw [norm_star]; exact zC_normSq
  rw [h1, h2, h3]; push_cast; ring

/-- **Control.** The coordinate form at `ρ` (`a = e₍₁,₀₎`) agrees with the direct `T2_ρ`. -/
theorem T2_coords_ρ_check :
    (fun p => ((Pi.single ((1 : Fin 3), (0 : Fin 4)) (1 : ℤ) : Fin 3 × Fin 4 → ℤ) p : ℝ)) ⬝ᵥ
      ((GramCert.Smat rhoR ⊗ₖ GramCert.Tmat QR qN) *ᵥ
        (fun p => ((Pi.single ((1 : Fin 3), (0 : Fin 4)) (1 : ℤ) : Fin 3 × Fin 4 → ℤ) p : ℝ)))
      = 4 * (3 * rhoR ^ 2 - 2) := by
  have h := T2_coords (Pi.single ((1 : Fin 3), (0 : Fin 4)) 1)
  rw [← h, ← T2_ρ]
  congr 1
  rw [Finset.sum_eq_single ((1 : Fin 3), (0 : Fin 4))]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

end

end RulerSelection.Emb
