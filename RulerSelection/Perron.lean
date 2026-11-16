module

public import Mathlib
public import RulerSelection.Mahler

/-!
# C3(c). The Perron selection (stage 2, lane C)

`IsPerronAt u` says that some real image of `u` above `1` strictly exceeds every other image of
`u` in modulus; it is stated on the embeddings of `L` and compares distinct values. It carries no
integrality clause (the unit hypotheses of the theorems below supply it) and requires the real image
to exceed `1`; for an algebraic integer it is the property of being a Perron number above `1`.

* `ρQ_perron` : `ρQ` is Perron at the real embedding `(ρ, Q)`.
* `not_perron_neg_ρQ`, `not_perron_inv_ρQ`, `not_perron_neg_inv_ρQ` : the other three minimisers
  are not (the largest modulus of `−ρQ` is at a negative real value; the largest modulus of
  `±(ρQ)⁻¹` is attained at two distinct complex-conjugate values).
* `ruler_selection` : a degree-12 unit of least Mahler measure that is Perron is `ρQ`.
* `ρQ_selected` : the hypotheses of `ruler_selection` hold at `ρQ` (non-vacuity).
-/

@[expose] public section

open NumberField IntermediateField Polynomial

namespace RulerSelection.LaneC

noncomputable section

open RulerSelection.Emb HermiteCompositum.Instance

/-- Some real image of `u` above `1` strictly exceeds every other image of `u` in modulus (no
integrality clause here). -/
def IsPerronAt (u : L) : Prop :=
  ∃ σ : L →+* ℂ, (σ u).im = 0 ∧ 1 < (σ u).re ∧ ∀ τ : L →+* ℂ, τ u ≠ σ u → ‖τ u‖ < (σ u).re

/-- A Perron value is the only value of maximal modulus. -/
theorem perron_eq (u : L) (hP : IsPerronAt u) : ∃ s : ℂ, s.im = 0 ∧ 1 < s.re ∧
    ∀ τ : L →+* ℂ, (∀ σ : L →+* ℂ, ‖σ u‖ ≤ ‖τ u‖) → τ u = s := by
  obtain ⟨σ, him, hre, hmax⟩ := hP
  refine ⟨σ u, him, hre, fun τ hτ => ?_⟩
  by_contra h
  have h1 := hmax τ h
  have h2 := hτ σ
  have h3 := Complex.re_le_norm (σ u)
  linarith

theorem norm_wC_lt_QR : ‖wC‖ < QR := by
  have hm : ‖wC‖ ^ 2 = 4 * Cw ^ 2 + QR ^ 1 * nN ^ 1 := by
    rw [wC_normSq]; simp only [Cw, nN]; ring
  have hm2 : ‖wC‖ ^ 2 ≤ 1131 / 1000 := by rw [hm]; linarith [mon_C2.2, mon_q1_n1.2]
  have hq := v_q.1
  nlinarith [norm_nonneg wC]

theorem nN_lt_one : nN < 1 := by linarith [v_n.2]

theorem norm_zs_le (i : Fin 3) : ‖zs i‖ ≤ rhoR := by
  have := norm_zC_lt_one; have := rhoR_gt_one
  fin_cases i
  · exact norm_zs0.le
  · show ‖zs 1‖ ≤ rhoR; rw [norm_zs1]; linarith
  · show ‖zs 2‖ ≤ rhoR; rw [norm_zs2]; linarith

theorem norm_ws_le (j : Fin 4) : ‖ws j‖ ≤ QR := by
  have := norm_wC_lt_QR; have := QR_gt_one; have := nN_lt_one
  fin_cases j
  · exact norm_ws0.le
  · show ‖ws 1‖ ≤ QR; rw [norm_ws1, show -qN = nN from rfl]; linarith
  · show ‖ws 2‖ ≤ QR; rw [norm_ws2]; linarith
  · show ‖ws 3‖ ≤ QR; rw [norm_ws3]; linarith

theorem norm_zs_ge (i : Fin 3) : ‖zC‖ ≤ ‖zs i‖ := by
  have := norm_zC_lt_one; have := rhoR_gt_one
  fin_cases i
  · show ‖zC‖ ≤ ‖zs 0‖; rw [norm_zs0]; linarith
  · exact le_rfl
  · show ‖zC‖ ≤ ‖zs 2‖; rw [norm_zs2]

theorem norm_ws_ge (j : Fin 4) : nN ≤ ‖ws j‖ := by
  have := one_lt_norm_wC; have := QR_gt_one; have := nN_lt_one
  fin_cases j
  · show nN ≤ ‖ws 0‖; rw [norm_ws0]; linarith
  · show nN ≤ ‖ws 1‖; rw [norm_ws1]; rfl
  · show nN ≤ ‖ws 2‖; rw [norm_ws2]; linarith
  · show nN ≤ ‖ws 3‖; rw [norm_ws3]; linarith

theorem norm_φL_ρQ (p : Fin 3 × Fin 4) : ‖φL p (ρ * Q)‖ = ‖zs p.1‖ * ‖ws p.2‖ := by
  rw [map_mul, φL_ρ, φL_Q, norm_mul]

theorem max_mod_ρQ (σ : L →+* ℂ) : ‖σ (ρ * Q)‖ ≤ rhoR * QR := by
  obtain ⟨p, rfl⟩ := embEquiv.surjective σ
  rw [embEquiv_apply, norm_φL_ρQ]
  exact mul_le_mul (norm_zs_le _) (norm_ws_le _) (norm_nonneg _) (by linarith [rhoR_gt_one])

theorem min_mod_ρQ (σ : L →+* ℂ) : ‖zC‖ * nN ≤ ‖σ (ρ * Q)‖ := by
  obtain ⟨p, rfl⟩ := embEquiv.surjective σ
  rw [embEquiv_apply, norm_φL_ρQ]
  exact mul_le_mul (norm_zs_ge _) (norm_ws_ge _) nN_pos.le (norm_nonneg _)

theorem φL00_ρQ : φL (0, 0) (ρ * Q) = ((rhoR * QR : ℝ) : ℂ) := by
  rw [map_mul, φL_ρ, φL_Q]; push_cast; rfl

theorem zC_ne_zero : zC ≠ 0 := fun h => by have := zC_im; rw [h] at this; simp at this

theorem ws1_ne_zero : ws 1 ≠ 0 := fun h => by
  have := congrArg norm h; rw [norm_ws1, norm_zero] at this; linarith [qN_neg]

theorem zs1_ws1_ne : zs 1 * ws 1 ≠ zs 2 * ws 1 := fun h => by
  have := zs_injective (mul_right_cancel₀ ws1_ne_zero h)
  exact absurd this (by decide)

/-- **Non-vacuity.** `ρQ` is Perron (at the embedding `(ρ, Q)`, value `ρ Q ≈ 1.617`). -/
theorem ρQ_perron : IsPerronAt (ρ * Q) := by
  refine ⟨φL (0, 0), ?_, ?_, fun τ hτ => ?_⟩
  · rw [φL00_ρQ, Complex.ofReal_im]
  · rw [φL00_ρQ, Complex.ofReal_re]; nlinarith [rhoR_gt_one, QR_gt_one]
  · rw [φL00_ρQ, Complex.ofReal_re]
    obtain ⟨p, rfl⟩ := embEquiv.surjective τ
    rw [embEquiv_apply] at hτ ⊢
    rw [norm_φL_ρQ]
    have hz := norm_zC_lt_one; have hw := norm_wC_lt_QR; have hn := nN_lt_one
    have hr := rhoR_gt_one; have hQ := QR_gt_one
    have hw0 := norm_nonneg wC; have hz0 := norm_nonneg zC
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hτ
    all_goals simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    all_goals first
      | (rw [norm_zs0, norm_ws1, show -qN = nN from rfl]; nlinarith)
      | (rw [norm_zs0, norm_ws2]; nlinarith)
      | (rw [norm_zs0, norm_ws3]; nlinarith)
      | (rw [norm_zs1, norm_ws0]; nlinarith)
      | (rw [norm_zs1, norm_ws1, show -qN = nN from rfl]; nlinarith)
      | (rw [norm_zs1, norm_ws2]; nlinarith)
      | (rw [norm_zs1, norm_ws3]; nlinarith)
      | (rw [norm_zs2, norm_ws0]; nlinarith)
      | (rw [norm_zs2, norm_ws1, show -qN = nN from rfl]; nlinarith)
      | (rw [norm_zs2, norm_ws2]; nlinarith)
      | (rw [norm_zs2, norm_ws3]; nlinarith)

theorem not_perron_neg_ρQ : ¬ IsPerronAt (-(ρ * Q)) := by
  intro hP
  obtain ⟨s, -, hs, hmax⟩ := perron_eq _ hP
  have h := hmax (φL (0, 0)) (fun σ => by
    rw [map_neg, map_neg, norm_neg, norm_neg, φL00_ρQ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by nlinarith [rhoR_gt_one, QR_gt_one])]
    exact max_mod_ρQ σ)
  rw [map_neg, φL00_ρQ] at h
  have : (-((rhoR * QR : ℝ) : ℂ)).re = -(rhoR * QR) := by simp
  rw [h] at this
  nlinarith [rhoR_gt_one, QR_gt_one]

theorem inv_max (σ : L →+* ℂ) :
    ‖σ (ρ * Q)⁻¹‖ ≤ ‖φL (1, 1) (ρ * Q)⁻¹‖ ∧ ‖σ (ρ * Q)⁻¹‖ ≤ ‖φL (2, 1) (ρ * Q)⁻¹‖ := by
  have h11 : ‖φL (1, 1) (ρ * Q)‖ = ‖zC‖ * nN := by
    rw [norm_φL_ρQ]; show ‖zs 1‖ * ‖ws 1‖ = _; rw [norm_zs1, norm_ws1]; rfl
  have h21 : ‖φL (2, 1) (ρ * Q)‖ = ‖zC‖ * nN := by
    rw [norm_φL_ρQ]; show ‖zs 2‖ * ‖ws 1‖ = _; rw [norm_zs2, norm_ws1]; rfl
  have hpos : 0 < ‖zC‖ * nN := mul_pos (norm_pos_iff.2 zC_ne_zero) nN_pos
  simp only [map_inv₀, norm_inv]
  rw [h11, h21]
  exact ⟨inv_anti₀ hpos (min_mod_ρQ σ), inv_anti₀ hpos (min_mod_ρQ σ)⟩

theorem not_perron_inv_ρQ : ¬ IsPerronAt (ρ * Q)⁻¹ := by
  intro hP
  obtain ⟨s, -, -, hmax⟩ := perron_eq _ hP
  have h1 := hmax (φL (1, 1)) (fun σ => (inv_max σ).1)
  have h2 := hmax (φL (2, 1)) (fun σ => (inv_max σ).2)
  rw [← h2, map_inv₀, map_inv₀, inv_inj, map_mul, map_mul, φL_ρ, φL_ρ, φL_Q, φL_Q] at h1
  exact zs1_ws1_ne h1

theorem not_perron_neg_inv_ρQ : ¬ IsPerronAt (-(ρ * Q)⁻¹) := by
  intro hP
  obtain ⟨s, -, -, hmax⟩ := perron_eq _ hP
  have h1 := hmax (φL (1, 1)) (fun σ => by
    rw [map_neg, map_neg, norm_neg, norm_neg]; exact (inv_max σ).1)
  have h2 := hmax (φL (2, 1)) (fun σ => by
    rw [map_neg, map_neg, norm_neg, norm_neg]; exact (inv_max σ).2)
  rw [← h2, map_neg, map_neg, neg_inj, map_inv₀, map_inv₀, inv_inj, map_mul, map_mul, φL_ρ, φL_ρ,
    φL_Q, φL_Q] at h1
  exact zs1_ws1_ne h1

/-- **C3(c).** A unit of degree 12 that minimises the Mahler measure among units of
degree 12 and is Perron (`IsPerronAt`) is `ρQ`. -/
theorem ruler_selection (u : (𝓞 L)ˣ) (hu : ℚ⟮((u : 𝓞 L) : L)⟯ = ⊤)
    (hmin : ∀ v : (𝓞 L)ˣ, ℚ⟮((v : 𝓞 L) : L)⟯ = ⊤ →
      ((minpoly ℤ ((u : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ ((v : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure)
    (hP : IsPerronAt ((u : 𝓞 L) : L)) : ((u : 𝓞 L) : L) = ρ * Q := by
  have h1 := hmin ρQunit ρQunit_top
  rw [ρQunit_coe] at h1
  have h2 := unit_deg12_mahler_ge u hu
  have hm := (unit_deg12_mahler_eq_iff u hu).1 (le_antisymm h1 h2)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h | h | h | h
  · exact h
  · rw [h] at hP; exact absurd hP not_perron_neg_ρQ
  · rw [h] at hP; exact absurd hP not_perron_inv_ρQ
  · rw [h] at hP; exact absurd hP not_perron_neg_inv_ρQ

/-- **Non-vacuity of `ruler_selection`.** `ρQ` satisfies all its hypotheses. -/
theorem ρQ_selected : IsPerronAt (ρ * Q) ∧ ℚ⟮ρ * Q⟯ = ⊤ ∧
    ∀ v : (𝓞 L)ˣ, ℚ⟮((v : 𝓞 L) : L)⟯ = ⊤ →
      ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
        ((minpoly ℤ ((v : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure :=
  ⟨ρQ_perron, HermiteCompositum.Assembly.adjoin_ρQ_eq_top, fun v hv => unit_deg12_mahler_ge v hv⟩

end

end RulerSelection.LaneC
