module

public import Mathlib
public import RulerSelection.Height
public import RulerSelection.Coords

/-!
# Lane A hand-off: the composed statements in tensor coordinates

* `tensC_powC` : the two integer changes of coordinates are inverse (`tensC ∘ powC = id`), so tensor
  coordinates are unique (`tens_coords_unique`).
* `T2_tens` : `T₂` of a tensor-coordinate combination, as the stage-1 power-basis Kronecker form
  evaluated at `powC c`.
* `height_le_imp` : for `x ∈ 𝓞 L` with `H(x) ≤ H(ρQ)`, there are tensor coordinates `c` with
  `x = ∑ c(a,b) tU a tV b` and `(powC c)ᵀ (Smat ⊗ₖ Tmat) (powC c) < 24.03`.
-/

@[expose] public section

open Matrix NumberField
open scoped Kronecker

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance

theorem pu3_pw3 (e d : Fin 3) : ∑ i : Fin 3, pu3 e i * pw3 i d = if e = d then 1 else 0 := by
  revert e d; decide

theorem pu4_pw4 (e d : Fin 4) : ∑ i : Fin 4, pu4 e i * pw4 i d = if e = d then 1 else 0 := by
  revert e d; decide

theorem tensC_powC (c : Fin 3 × Fin 4 → ℤ) : tensC (powC c) = c := by
  funext d
  simp only [tensC, powC, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ e : Fin 3 × Fin 4, ∑ p : Fin 3 × Fin 4,
      c e * pu3 e.1 p.1 * pu4 e.2 p.2 * pw3 p.1 d.1 * pw4 p.2 d.2 =
      c e * ((∑ i : Fin 3, pu3 e.1 i * pw3 i d.1) * (∑ j : Fin 4, pu4 e.2 j * pw4 j d.2)) := by
    intro e
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl fun e _ => key e]
  simp only [pu3_pw3, pu4_pw4]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ he
    rcases e with ⟨e1, e2⟩
    rcases d with ⟨d1, d2⟩
    by_cases h1 : e1 = d1
    · have h2 : e2 ≠ d2 := fun h2 => he (by rw [h1, h2])
      simp [h2]
    · simp [h1]
  · simp

/-- **Tensor coordinates are unique.** -/
theorem tens_coords_unique (c c' : Fin 3 × Fin 4 → ℤ)
    (h : ∑ d : Fin 3 × Fin 4, (c d : L) * tU d.1 * tV d.2 =
      ∑ d : Fin 3 × Fin 4, (c' d : L) * tU d.1 * tV d.2) : c = c' := by
  rw [pow_coords_of_tens, pow_coords_of_tens] at h
  have := coords_unique _ _ h
  rw [← tensC_powC c, ← tensC_powC c', this]

/-- `T₂` in tensor coordinates, via the power-basis form. -/
theorem T2_tens (c : Fin 3 × Fin 4 → ℤ) :
    T2 (∑ d : Fin 3 × Fin 4, (c d : L) * tU d.1 * tV d.2) =
      (fun p => (powC c p : ℝ)) ⬝ᵥ ((GramCert.Smat rhoR ⊗ₖ GramCert.Tmat QR qN) *ᵥ
        (fun p => (powC c p : ℝ))) := by
  rw [pow_coords_of_tens, T2_coords]

/-- **Hand-off to lane B.** An integral element of height at most `H(ρQ)` has tensor coordinates
whose power-basis Kronecker form is below `24.03`. -/
theorem height_le_imp (x : 𝓞 L) (h : embHeight (algebraMap (𝓞 L) L x) ≤ embHeight (ρ * Q)) :
    ∃ c : Fin 3 × Fin 4 → ℤ,
      algebraMap (𝓞 L) L x = ∑ d : Fin 3 × Fin 4, (c d : L) * tU d.1 * tV d.2 ∧
      (fun p => (powC c p : ℝ)) ⬝ᵥ ((GramCert.Smat rhoR ⊗ₖ GramCert.Tmat QR qN) *ᵥ
        (fun p => (powC c p : ℝ))) < 2403 / 100 := by
  obtain ⟨c, hc⟩ := tens_surjective x
  refine ⟨c, hc, ?_⟩
  rw [← T2_tens, ← hc]
  exact T2_lt_of_embHeight_le _ h

end

end RulerSelection.Emb
