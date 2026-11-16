module

public import Mathlib
public import RulerSelection.Main

/-!
# C2 controls (stage 2, lane C)

(i) **The list is not too long**: every one of the fourteen listed elements has
`embHeight ≤ embHeight (ρ * Q)` (`listed_le`); `ρ, ρ⁻¹` have height `rhoR⁴ ≈ 3.0796`, `Q, Q⁻¹` have
height `(QR·|w|²)³ ≈ 2.6297`, `±(ρQ)^{±1}` have height exactly `H(ρQ)`; `±1` height `1`.

(ii) **An integral nonzero element outside the list whose height exceeds `H(ρQ)`**: `ρ⁻¹Q ∈ 𝓞 L`
(one of the 56), nonzero, not in the list, with `H(ρQ) < H(ρ⁻¹Q)` (`control_ii`). Nothing here says
that no integral element has height strictly between the two.
-/

@[expose] public section

open NumberField

namespace RulerSelection.LaneC

noncomputable section

open RulerSelection.Emb RulerSelection.LaneB HermiteCompositum.Instance

/-- The fourteen elements. -/
def S14 : Set L := {1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹, ρ * Q, -(ρ * Q), (ρ * Q)⁻¹,
  -(ρ * Q)⁻¹}

theorem ρ_ne_zero' : ρ ≠ 0 := left_ne_zero_of_mul ρQ_ne_zero
theorem Q_ne_zero' : Q ≠ 0 := right_ne_zero_of_mul ρQ_ne_zero

theorem norm_zC_lt_one : ‖zC‖ < 1 := by
  have h := zC_normSq; have := rhoR_hi; have := rhoR_lo
  nlinarith [norm_nonneg zC]

theorem one_lt_norm_wC : 1 < ‖wC‖ := by
  have h := wC_normSq; have h2 := wC_normSq_gt
  nlinarith [norm_nonneg wC]

theorem embHeight_ρ : embHeight ρ = rhoR ^ 4 := by
  rw [embHeight, prod_emb, Fintype.prod_prod_type]
  simp only [φL_ρ, Fin.prod_univ_three, Fin.prod_univ_four]
  rw [norm_zs0, norm_zs1, norm_zs2, max_eq_right rhoR_gt_one.le, max_eq_left norm_zC_lt_one.le]
  ring

theorem embHeight_Q : embHeight Q = (QR * ‖wC‖ ^ 2) ^ 3 := by
  rw [embHeight, prod_emb, Fintype.prod_prod_type]
  simp only [φL_Q, Fin.prod_univ_three, Fin.prod_univ_four]
  rw [norm_ws0, norm_ws1, norm_ws2, norm_ws3, max_eq_right QR_gt_one.le,
    max_eq_left (by linarith [qN_lo] : -qN ≤ 1), max_eq_right one_lt_norm_wC.le]
  ring

theorem prod_norm_ρ : ∏ σ : L →+* ℂ, ‖σ ρ‖ = 1 := by
  rw [prod_emb, Fintype.prod_prod_type]
  simp only [φL_ρ, Fin.prod_univ_three, Fin.prod_univ_four]
  rw [norm_zs0, norm_zs1, norm_zs2]
  have h1 : rhoR * ‖zC‖ ^ 2 = 1 := by
    rw [zC_normSq]; linear_combination rhoR_eq
  calc _ = (rhoR * ‖zC‖ ^ 2) ^ 4 := by ring
    _ = 1 := by rw [h1]; norm_num

theorem prod_norm_Q : ∏ σ : L →+* ℂ, ‖σ Q‖ = 1 := by
  rw [prod_emb, Fintype.prod_prod_type]
  simp only [φL_Q, Fin.prod_univ_three, Fin.prod_univ_four]
  rw [norm_ws0, norm_ws1, norm_ws2, norm_ws3]
  have h2 : QR * (-qN) * ‖wC‖ ^ 2 = 1 := by
    rw [wC_normSq]; linear_combination -quartic_e2
  calc _ = (QR * (-qN) * ‖wC‖ ^ 2) ^ 3 := by ring
    _ = 1 := by rw [h2]; norm_num

theorem embHeight_ρ_inv : embHeight ρ⁻¹ = embHeight ρ := by
  have := embHeight_inv_mul ρ ρ_ne_zero'
  rwa [prod_norm_ρ, mul_one] at this

theorem embHeight_Q_inv : embHeight Q⁻¹ = embHeight Q := by
  have := embHeight_inv_mul Q Q_ne_zero'
  rwa [prod_norm_Q, mul_one] at this

/-- `H(ρQ) ≥ 3.6`. -/
theorem H_ge : (36 / 10 : ℝ) ≤ embHeight (ρ * Q) := by
  have h := mon_r2_q2
  have hn := v_n
  rw [embHeight_ρQ, le_div_iff₀ (by linarith [qN_neg] : (0:ℝ) < -qN), show -qN = nN from rfl]
  nlinarith [h.1, hn.2]

theorem embHeight_ρ_le : embHeight ρ ≤ embHeight (ρ * Q) := by
  rw [embHeight_ρ]
  have h := mono_bounds (by norm_num) v_r.1 v_r.2 4
  have : rhoR ^ 4 ≤ 36 / 10 := le_trans h.2 (by norm_num)
  linarith [H_ge]

theorem embHeight_Q_le : embHeight Q ≤ embHeight (ρ * Q) := by
  rw [embHeight_Q]
  have hm : ‖wC‖ ^ 2 = 4 * Cw ^ 2 + QR ^ 1 * nN ^ 1 := by
    rw [wC_normSq]; simp only [Cw, nN]; ring
  have hm2 : ‖wC‖ ^ 2 ≤ 1131 / 1000 := by rw [hm]; linarith [mon_C2.2, mon_q1_n1.2]
  have hq : QR ≤ 12208 / 10000 := by linarith [v_q.2]
  have h1 : QR * ‖wC‖ ^ 2 ≤ 12208 / 10000 * (1131 / 1000) :=
    mul_le_mul hq hm2 (by positivity) (by norm_num)
  have h2 : (QR * ‖wC‖ ^ 2) ^ 3 ≤ (12208 / 10000 * (1131 / 1000)) ^ 3 :=
    pow_le_pow_left₀ (by have := QR_gt_one; positivity) h1 3
  have : (12208 / 10000 * (1131 / 1000) : ℝ) ^ 3 ≤ 36 / 10 := by norm_num
  linarith [H_ge]

/-- **Control (i).** Every listed element has height at most `H(ρQ)`. -/
theorem listed_le : ∀ y ∈ S14, embHeight y ≤ embHeight (ρ * Q) := by
  intro y hy
  simp only [S14, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  have h1 : embHeight 1 ≤ embHeight (ρ * Q) := by rw [embHeight_one]; exact one_le_embHeight _
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · rw [embHeight_neg]; exact h1
  · exact embHeight_ρ_le
  · rw [embHeight_neg]; exact embHeight_ρ_le
  · rw [embHeight_ρ_inv]; exact embHeight_ρ_le
  · rw [embHeight_neg, embHeight_ρ_inv]; exact embHeight_ρ_le
  · exact embHeight_Q_le
  · rw [embHeight_neg]; exact embHeight_Q_le
  · rw [embHeight_Q_inv]; exact embHeight_Q_le
  · rw [embHeight_neg, embHeight_Q_inv]; exact embHeight_Q_le
  · exact le_rfl
  · rw [embHeight_neg_ρQ]
  · rw [embHeight_ρQ_inv]
  · rw [embHeight_neg_ρQ_inv]

/-- The main theorem restated with `S14`, together with its converse (control (i)): for nonzero
`x ∈ 𝓞 L`, `H(x) ≤ H(ρQ) ↔ x ∈ S14`. -/
theorem small_height_iff (x : 𝓞 L) (hx : x ≠ 0) :
    embHeight (x : L) ≤ embHeight (ρ * Q) ↔ (x : L) ∈ S14 :=
  ⟨small_height x hx, listed_le _⟩

theorem elemOf_e6 : elemOf [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] = ρ⁻¹ * Q := by
  simp [elemOf, funOf, Fintype.sum_prod_type, Fin.sum_univ_succ, tU, tV]

theorem e6_mem : [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] ∈ rest56 := by
  simp [rest56]

/-- `H(ρQ) < H(ρ⁻¹Q)` (C1 at the pair `±ρ⁻¹Q`). -/
theorem control_excluded : embHeight (ρ * Q) < embHeight (ρ⁻¹ * Q) := by
  rw [← elemOf_e6]; exact rest56_excl _ e6_mem

/-- **Control (ii).** An integral, nonzero element outside the list, of height exceeding
`H(ρQ)`: the conclusion of `small_height` fails for any bound `≥ H(ρ⁻¹Q)`. -/
theorem control_ii : ∃ x : 𝓞 L, x ≠ 0 ∧ (x : L) = ρ⁻¹ * Q ∧ (x : L) ∉ S14 ∧
    embHeight (ρ * Q) < embHeight (x : L) := by
  obtain ⟨x, hx⟩ := tens_integral (funOf [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0])
  have hxv : (x : L) = ρ⁻¹ * Q := by
    rw [RingOfIntegers.coe_eq_algebraMap, hx]; exact elemOf_e6
  refine ⟨x, ?_, hxv, ?_, ?_⟩
  · rintro rfl
    have h0 : embHeight ((0 : 𝓞 L) : L) = 1 := by simp [embHeight]
    have := control_excluded
    rw [← hxv, h0] at this
    linarith [one_le_embHeight (ρ * Q)]
  · intro h
    exact absurd (listed_le _ h) (not_le.2 (hxv ▸ control_excluded))
  · rw [hxv]; exact control_excluded

end

end RulerSelection.LaneC
