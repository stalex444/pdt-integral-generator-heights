module

public import Mathlib
public import RulerSelection.Link
public import RulerSelection.ControlsA

/-!
# Lane B vacuity controls

* `kron_ge_diag_needs_t`, `kron_ge_diag_needs_s` (in `Kron.lean`): the sign hypotheses are needed.
* `box_hyp_sat` : the hypothesis of `box_of_qf` holds for the vector of `ρQ` (`e₁₀`, `N = 138775`).
* `cut_excludes_two` : the cut is not automatic: `y = 2 e₀` has `N = 477204 > 240300`.
* `small_height_hyp_sat` : the hypothesis of `small_height_in_L12` holds for `x = 1`.
* `elemOf_e10` : the `L12` vector `e₁₀` is `ρQ` (an independent single-case evaluation).
-/

@[expose] public section

namespace RulerSelection.LaneB

noncomputable section

open RulerSelection.EnumProbe RulerSelection.Emb HermiteCompositum.Instance NumberField

theorem box_hyp_sat : qf Nmat (vecOf (fun d => if d = (2, 2) then 1 else 0)) ≤ 240300 := by
  decide +kernel

theorem cut_excludes_two : ¬ qf Nmat (vecOf (fun d => if d = (0, 0) then 2 else 0)) ≤ 240300 := by
  decide +kernel

theorem small_height_hyp_sat :
    embHeight (algebraMap (𝓞 L) L 1) ≤ embHeight (ρ * Q) := height_le_imp_hyp_one

theorem elemOf_e10 : elemOf [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] = ρ * Q := by
  simp [elemOf, funOf, Fintype.sum_prod_type, Fin.sum_univ_succ, tU, tV]

end

end RulerSelection.LaneB
