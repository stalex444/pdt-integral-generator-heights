module

public import Mathlib
public import HermiteCompositum.Instance

/-!
# Integer coordinates on `𝓞 L` (stage 2, lane A, target A5)

From the registered entry's `ℤ`-basis `bL` of `𝓞 L` (`bL_apply : bL p = ρ'^p.1 * Q'^p.2`):

* `bL_coe_sum`, `coords_exist`, `coords_unique` : every `x : 𝓞 L` is `∑ a(i,j) ρ^i Q^j` with
  integer `a : Fin 3 × Fin 4 → ℤ`, uniquely; and every such sum is the image of an element of `𝓞 L`.
* `ρ_inv`, `Q_inv` : `ρ⁻¹ = ρ² − 1`, `Q⁻¹ = Q³ − 1` in `L`.
* `tens_coords`, `tens_surjective` : the change to the tensor basis
  `tU ⊗ tV = {1, ρ⁻¹, ρ} ⊗ {1, Q⁻¹, Q, Q²}` (pair index `(a, b) : Fin 3 × Fin 4`, which is the
  stage-1 `Nmat` flat index `4a + b`), with the explicit integer change of coordinates `tensC`;
  and `pow_coords_of_tens` for the inverse direction (`powC`).
-/

@[expose] public section

open NumberField

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance

theorem bL_coe_sum (a : Fin 3 × Fin 4 → ℤ) :
    algebraMap (𝓞 L) L (∑ p, a p • bL p) =
      ∑ p : Fin 3 × Fin 4, (a p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_zsmul, bL_apply, map_mul, map_pow, map_pow, coe_ρ', coe_Q', zsmul_eq_mul, mul_assoc]

/-- **Power-basis coordinates exist.** -/
theorem coords_exist (x : 𝓞 L) : ∃ a : Fin 3 × Fin 4 → ℤ,
    algebraMap (𝓞 L) L x = ∑ p : Fin 3 × Fin 4, (a p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ) :=
  ⟨fun p => bL.repr x p, by rw [← bL_coe_sum, bL.sum_repr x]⟩

/-- **Power-basis coordinates are unique.** -/
theorem coords_unique (a b : Fin 3 × Fin 4 → ℤ)
    (h : ∑ p : Fin 3 × Fin 4, (a p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ) =
      ∑ p : Fin 3 × Fin 4, (b p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ)) : a = b := by
  rw [← bL_coe_sum, ← bL_coe_sum] at h
  have h' := FaithfulSMul.algebraMap_injective (𝓞 L) L h
  have h0 : ∑ p, (a - b) p • bL p = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h', sub_self]
  have := Fintype.linearIndependent_iff.mp bL.linearIndependent (a - b) h0
  funext p
  have hp := this p
  simp only [Pi.sub_apply] at hp
  linarith

theorem ρ_inv : ρ⁻¹ = ρ ^ 2 - 1 := by linear_combination -neg_inv_ρ

theorem Q_inv : Q⁻¹ = Q ^ 3 - 1 := by linear_combination -neg_inv_Q

/-- The cubic tensor factor `{1, ρ⁻¹, ρ}`. -/
def tU : Fin 3 → L := ![1, ρ⁻¹, ρ]
/-- The quartic tensor factor `{1, Q⁻¹, Q, Q²}`. -/
def tV : Fin 4 → L := ![1, Q⁻¹, Q, Q ^ 2]

/-- `ρ^i = ∑_a pw3 i a · tU a`. -/
def pw3 : Fin 3 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 0, 1], ![1, 1, 0]]
/-- `Q^j = ∑_b pw4 j b · tV b`. -/
def pw4 : Fin 4 → Fin 4 → ℤ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 1, 0, 0]]
/-- `tU a = ∑_i pu3 a i · ρ^i`. -/
def pu3 : Fin 3 → Fin 3 → ℤ := ![![1, 0, 0], ![-1, 0, 1], ![0, 1, 0]]
/-- `tV b = ∑_j pu4 b j · Q^j`. -/
def pu4 : Fin 4 → Fin 4 → ℤ :=
  ![![1, 0, 0, 0], ![-1, 0, 0, 1], ![0, 1, 0, 0], ![0, 0, 1, 0]]

theorem ρ_pow_eq (i : Fin 3) : ρ ^ (i : ℕ) = ∑ a, (pw3 i a : L) * tU a := by
  fin_cases i <;> simp [Fin.sum_univ_three, pw3, tU, ρ_inv]

theorem Q_pow_eq (j : Fin 4) : Q ^ (j : ℕ) = ∑ b, (pw4 j b : L) * tV b := by
  fin_cases j <;> simp [Fin.sum_univ_four, pw4, tV, Q_inv]

theorem tU_eq (a : Fin 3) : tU a = ∑ i : Fin 3, (pu3 a i : L) * ρ ^ (i : ℕ) := by
  fin_cases a <;> simp [Fin.sum_univ_three, pu3, tU, ρ_inv] <;> ring

theorem tV_eq (b : Fin 4) : tV b = ∑ j : Fin 4, (pu4 b j : L) * Q ^ (j : ℕ) := by
  fin_cases b <;> simp [Fin.sum_univ_four, pu4, tV, Q_inv] <;> ring

/-- Power coordinates `a` ↦ tensor coordinates. -/
def tensC (a : Fin 3 × Fin 4 → ℤ) (c : Fin 3 × Fin 4) : ℤ :=
  ∑ p : Fin 3 × Fin 4, a p * pw3 p.1 c.1 * pw4 p.2 c.2

/-- Tensor coordinates `c` ↦ power coordinates. -/
def powC (c : Fin 3 × Fin 4 → ℤ) (p : Fin 3 × Fin 4) : ℤ :=
  ∑ d : Fin 3 × Fin 4, c d * pu3 d.1 p.1 * pu4 d.2 p.2

/-- A general re-expansion: if `x i = ∑_a A i a · u a` and `y j = ∑_b B j b · v b` then
`∑ a(i,j) x_i y_j = ∑_{(a,b)} (∑ a(i,j) A i a B j b) u_a v_b`. -/
theorem reexpand {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (x : ι → L) (y : κ → L) (u : α → L) (v : β → L) (A : ι → α → ℤ) (B : κ → β → ℤ)
    (hx : ∀ i, x i = ∑ a, (A i a : L) * u a) (hy : ∀ j, y j = ∑ b, (B j b : L) * v b)
    (c : ι × κ → ℤ) :
    ∑ p : ι × κ, (c p : L) * x p.1 * y p.2 =
      ∑ d : α × β, ((∑ p : ι × κ, c p * A p.1 d.1 * B p.2 d.2 : ℤ) : L) * u d.1 * v d.2 := by
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hx p.1, hy p.2, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **Power coordinates → tensor coordinates.** -/
theorem tens_coords (a : Fin 3 × Fin 4 → ℤ) :
    ∑ p : Fin 3 × Fin 4, (a p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ) =
      ∑ c : Fin 3 × Fin 4, (tensC a c : L) * tU c.1 * tV c.2 :=
  reexpand (fun i : Fin 3 => ρ ^ (i : ℕ)) (fun j : Fin 4 => Q ^ (j : ℕ)) tU tV pw3 pw4
    ρ_pow_eq Q_pow_eq a

/-- **Tensor coordinates → power coordinates.** -/
theorem pow_coords_of_tens (c : Fin 3 × Fin 4 → ℤ) :
    ∑ d : Fin 3 × Fin 4, (c d : L) * tU d.1 * tV d.2 =
      ∑ p : Fin 3 × Fin 4, (powC c p : L) * ρ ^ (p.1 : ℕ) * Q ^ (p.2 : ℕ) :=
  reexpand tU tV (fun i : Fin 3 => ρ ^ (i : ℕ)) (fun j : Fin 4 => Q ^ (j : ℕ)) pu3 pu4
    tU_eq tV_eq c

/-- **`tens_surjective`.** Every `x ∈ 𝓞 L` has integer coordinates in `{1, ρ⁻¹, ρ} ⊗ {1, Q⁻¹, Q, Q²}`. -/
theorem tens_surjective (x : 𝓞 L) : ∃ c : Fin 3 × Fin 4 → ℤ,
    algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (c d : L) * tU d.1 * tV d.2 := by
  obtain ⟨a, ha⟩ := coords_exist x
  exact ⟨tensC a, by rw [ha, tens_coords]⟩

/-- Every tensor-coordinate combination is integral (it is the image of an element of `𝓞 L`). -/
theorem tens_integral (c : Fin 3 × Fin 4 → ℤ) : ∃ x : 𝓞 L,
    algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (c d : L) * tU d.1 * tV d.2 :=
  ⟨∑ p, powC c p • bL p, by rw [bL_coe_sum, pow_coords_of_tens]⟩

end

end RulerSelection.Emb
