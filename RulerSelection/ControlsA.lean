module

public import Mathlib
public import RulerSelection.Bridge

/-!
# Lane A vacuity controls

* The hypotheses of the hand-off are satisfiable (`height_le_imp_hyp_one`: `x = 1`).
* The conclusion of `T2_lt_of_embHeight_le` is not automatic (`T2_two`, `T2_two_not_lt`: `T₂(2) = 48`).
* `embHeight_ρQ` is not a trivial value (`one_lt_embHeight_ρQ`).
-/

@[expose] public section

namespace RulerSelection.Emb

noncomputable section

open HermiteCompositum.Instance NumberField

theorem height_le_imp_hyp_one : embHeight (algebraMap (𝓞 L) L 1) ≤ embHeight (ρ * Q) := by
  rw [map_one, embHeight_one]; exact one_le_embHeight _

theorem T2_two : T2 2 = 48 := by
  have h : ∀ σ : L →+* ℂ, ‖σ 2‖ ^ 2 = 4 := fun σ => by
    rw [map_ofNat, Complex.norm_ofNat]; norm_num
  rw [T2, Finset.sum_congr rfl fun σ _ => h σ, Finset.sum_const, Finset.card_univ, card_emb]
  norm_num

theorem T2_two_not_lt : ¬ T2 2 < 2403 / 100 := by
  rw [T2_two]; norm_num

theorem one_lt_embHeight_ρQ : 1 < embHeight (ρ * Q) := by
  rw [embHeight_ρQ, lt_div_iff₀ (by linarith [qN_hi])]
  have h1 : 1 < rhoR ^ 2 := by nlinarith [rhoR_lo]
  have h2 : 1 < QR ^ 2 := by nlinarith [QR_lo]
  nlinarith [qN_lo, mul_lt_mul'' h1 h2 (by norm_num) (by norm_num)]

end

end RulerSelection.Emb
