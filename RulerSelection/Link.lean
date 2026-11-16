module

public import Mathlib
public import RulerSelection.Box

/-!
# B4. The link (stage 2, lane B)

* `small_height_in_L12` : for ANY `x : 𝓞 L` with `embHeight x ≤ embHeight (ρ * Q)`, the (unique,
  `tens_coords_unique`) tensor coordinates `y` of `x` satisfy `vecOf y ∈ L12` (the stage-1 list).
  Chain: lane A's `height_le_imp` (`T₂ x ≤ H(x)² + 11 ≤ H(ρQ)² + 11 < 24.03`, `T₂ = form`),
  B1 `kron_lower_bound`, B2 `nmat_identity`, B3 `vecOf_mem_L12` (box + `enum12`).
* `L12_split` : `L12` is the 15 listed vectors (`listed15`: `0` and `±e_k`,
  `k ∈ {0,1,2,4,5,8,10}`) plus the 56 others (`rest56`, 28 `±` pairs), and conversely.
* `listed_values` : the 15 listed vectors are exactly the elements
  `0, ±1, ±Q⁻¹, ±Q, ±ρ⁻¹, ±(ρQ)⁻¹, ±ρ, ±ρQ` of `L`.
* `small_height_cases` : such an `x` is one of those 15 elements, or `elemOf l` for some
  `l ∈ rest56` (the 28 pairs lane C must exclude).
-/

@[expose] public section

open Matrix NumberField
open scoped Kronecker

namespace RulerSelection.LaneB

noncomputable section

open RulerSelection.GramCert RulerSelection.Emb RulerSelection.EnumProbe
open HermiteCompositum.Instance

/-- **B4. The link.** -/
theorem small_height_in_L12 (x : 𝓞 L)
    (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q)) :
    ∃ y : Fin 3 × Fin 4 → ℤ,
      algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2 ∧ vecOf y ∈ L12 := by
  obtain ⟨c, hc, hlt⟩ := height_le_imp x h
  refine ⟨c, hc, vecOf_mem_L12 c ?_⟩
  have h1 := Kron.kron_lower_bound (fun p => (powC c p : ℝ))
  have h2 := nmat_identity c
  have hR : (qf Nmat (vecOf c) : ℝ) < 240300 := by linarith
  have hZ : qf Nmat (vecOf c) < 240300 := by exact_mod_cast hR
  exact hZ.le

/-- The element of `L` with tensor coordinates given by a flat list (index `4a + b`). -/
def elemOf (l : List ℤ) : L := ∑ d : Fin 3 × Fin 4, (funOf l d : L) * tU d.1 * tV d.2

theorem elemOf_vecOf (y : Fin 3 × Fin 4 → ℤ) :
    elemOf (vecOf y) = ∑ d : Fin 3 × Fin 4, (y d : L) * tU d.1 * tV d.2 := by
  rw [elemOf, funOf_vecOf]

/-- Every `x : 𝓞 L` of height at most `H(ρQ)` is `elemOf l` for some `l ∈ L12`. -/
theorem small_height_elemOf (x : 𝓞 L)
    (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q)) :
    ∃ l ∈ L12, algebraMap (𝓞 L) L x = elemOf l := by
  obtain ⟨y, hy, hm⟩ := small_height_in_L12 x h
  exact ⟨vecOf y, hm, by rw [elemOf_vecOf, hy]⟩

def listed15 : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def rest56 : List (List ℤ) :=
  [[-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [-1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [-1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  [-1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0],
  [-1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  [0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0],
  [0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0],
  [0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0],
  [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0],
  [0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0],
  [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1],
  [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1],
  [0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0],
  [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0],
  [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0],
  [0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0],
  [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0],
  [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
theorem L12_split : ∀ l ∈ L12, l ∈ listed15 ∨ l ∈ rest56 := by decide +kernel

set_option maxRecDepth 100000 in
theorem listed15_sub : ∀ l ∈ listed15, l ∈ L12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem rest56_sub : ∀ l ∈ rest56, l ∈ L12 := by decide +kernel

theorem listed15_length : listed15.length = 15 := rfl
theorem rest56_length : rest56.length = 56 := rfl

set_option maxRecDepth 100000 in
/-- `rest56` is closed under negation (28 `±` pairs). -/
theorem rest56_neg : ∀ l ∈ rest56, l.map (fun t => -t) ∈ rest56 := by decide +kernel

/-- The fifteen listed elements of `L`. -/
def IsListed (z : L) : Prop :=
  z = 0 ∨ z = 1 ∨ z = -1 ∨ z = ρ ∨ z = -ρ ∨ z = ρ⁻¹ ∨ z = -ρ⁻¹ ∨ z = Q ∨ z = -Q ∨
    z = Q⁻¹ ∨ z = -Q⁻¹ ∨ z = ρ * Q ∨ z = -(ρ * Q) ∨ z = (ρ * Q)⁻¹ ∨ z = -(ρ * Q)⁻¹

set_option maxHeartbeats 4000000 in
theorem listed_values : ∀ l ∈ listed15, IsListed (elemOf l) := by
  intro l hl
  simp only [listed15, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [IsListed, elemOf, funOf, Fintype.sum_prod_type, Fin.sum_univ_succ, tU, tV, mul_comm]

/-- **B4, cases.** -/
theorem small_height_cases (x : 𝓞 L)
    (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q)) :
    IsListed (algebraMap (𝓞 L) L x) ∨ ∃ l ∈ rest56, algebraMap (𝓞 L) L x = elemOf l := by
  obtain ⟨l, hl, hx⟩ := small_height_elemOf x h
  rcases L12_split l hl with h1 | h1
  · left; rw [hx]; exact listed_values l h1
  · right; exact ⟨l, h1, hx⟩

end

end RulerSelection.LaneB
