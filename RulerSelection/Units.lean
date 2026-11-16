module

public import Mathlib
public import RulerSelection.ControlsC
public import RulerSelection.ControlsA
public import HermiteCompositum.Assembly

/-!
# C3(b). Units of degree 12 (stage 2, lane C)

* `listed_small_not_top` : the ten listed elements `±1, ±ρ^{±1}, ±Q^{±1}` lie in a sector
  `S₃ = ℚ⟮ρ⟯` (degree 3) or `S₄ = ℚ⟮Q⟯` (degree 4), so none generates `L` (degree 12).
* `unit_deg12_ge` : for a unit `u` with `ℚ⟮u⟯ = ⊤`, `H(ρQ) ≤ H(u)`.
* `unit_deg12_eq_iff` : equality iff `u ∈ {ρQ, −ρQ, (ρQ)⁻¹, −(ρQ)⁻¹}`.
* Controls: `ρQunit` is a unit with `ℚ⟮ρQ⟯ = ⊤` (the hypothesis is satisfiable and the bound
  attained); `control_hu_needed` (without `ℚ⟮u⟯ = ⊤` the bound fails, `u = 1`).
-/

@[expose] public section

open NumberField IntermediateField

namespace RulerSelection.LaneC

noncomputable section

open RulerSelection.Emb RulerSelection.LaneB HermiteCompositum.Instance

theorem not_top_of_mem (F : IntermediateField ℚ L) (hF : Module.finrank ℚ F < 12) (y : L)
    (hy : y ∈ F) : ℚ⟮y⟯ ≠ ⊤ := by
  intro h
  have hle : ℚ⟮y⟯ ≤ F := (adjoin_simple_le_iff).2 hy
  rw [h, top_le_iff] at hle
  rw [hle, finrank_top', finrank_L] at hF
  exact lt_irrefl _ hF

theorem listed_small_not_top (y : L)
    (hy : y ∈ ({1, -1, ρ, -ρ, ρ⁻¹, -ρ⁻¹, Q, -Q, Q⁻¹, -Q⁻¹} : Set L)) : ℚ⟮y⟯ ≠ ⊤ := by
  have h3 : Module.finrank ℚ S₃ < 12 := by rw [finrank_S₃]; norm_num
  have h4 : Module.finrank ℚ S₄ < 12 := by rw [finrank_S₄]; norm_num
  have hρ : ρ ∈ S₃ := by rw [S₃]; exact mem_adjoin_simple_self ℚ ρ
  have hQ : Q ∈ S₄ := by rw [S₄]; exact mem_adjoin_simple_self ℚ Q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_top_of_mem S₃ h3 _ (one_mem _)
  · exact not_top_of_mem S₃ h3 _ (neg_mem (one_mem _))
  · exact not_top_of_mem S₃ h3 _ hρ
  · exact not_top_of_mem S₃ h3 _ (neg_mem hρ)
  · exact not_top_of_mem S₃ h3 _ (inv_mem hρ)
  · exact not_top_of_mem S₃ h3 _ (neg_mem (inv_mem hρ))
  · exact not_top_of_mem S₄ h4 _ hQ
  · exact not_top_of_mem S₄ h4 _ (neg_mem hQ)
  · exact not_top_of_mem S₄ h4 _ (inv_mem hQ)
  · exact not_top_of_mem S₄ h4 _ (neg_mem (inv_mem hQ))

/-- **C3(b).** A unit of degree 12 has height at least `H(ρQ)`. -/
theorem unit_deg12_ge (u : (𝓞 L)ˣ) (hu : ℚ⟮((u : 𝓞 L) : L)⟯ = ⊤) :
    embHeight (ρ * Q) ≤ embHeight ((u : 𝓞 L) : L) := by
  by_contra h
  push Not at h
  have hm := small_height_unit u h.le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  rotate_left 10
  · rw [h1] at h; exact lt_irrefl _ h
  · rw [h1, embHeight_neg_ρQ] at h; exact lt_irrefl _ h
  · rw [h1, embHeight_ρQ_inv] at h; exact lt_irrefl _ h
  · rw [h1, embHeight_neg_ρQ_inv] at h; exact lt_irrefl _ h
  all_goals
    exact listed_small_not_top ((u : 𝓞 L) : L) (by rw [h1]; simp) hu

/-- **C3(b), equality case.** Among units of degree 12, height `H(ρQ)` is attained exactly by
`±(ρQ)^{±1}`. -/
theorem unit_deg12_eq_iff (u : (𝓞 L)ˣ) (hu : ℚ⟮((u : 𝓞 L) : L)⟯ = ⊤) :
    embHeight ((u : 𝓞 L) : L) = embHeight (ρ * Q) ↔
      ((u : 𝓞 L) : L) ∈ ({ρ * Q, -(ρ * Q), (ρ * Q)⁻¹, -(ρ * Q)⁻¹} : Set L) := by
  constructor
  · intro h
    have hm := small_height_unit u h.le
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    rcases hm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    rotate_left 10
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
    all_goals
      exact absurd hu (listed_small_not_top ((u : 𝓞 L) : L) (by rw [h1]; simp))
  · intro hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [embHeight_neg_ρQ]
    · rw [embHeight_ρQ_inv]
    · rw [embHeight_neg_ρQ_inv]

/-- `ρQ` as a unit of `𝓞 L` (inverse `(ρ² − 1)(Q³ − 1)`). -/
def ρQunit : (𝓞 L)ˣ where
  val := ρ' * Q'
  inv := (ρ' ^ 2 - 1) * (Q' ^ 3 - 1)
  val_inv := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    simp only [map_mul, map_sub, map_pow, map_one, coe_ρ', coe_Q']
    rw [← ρ_inv, ← Q_inv, mul_mul_mul_comm, mul_inv_cancel₀ ρ_ne_zero',
      mul_inv_cancel₀ Q_ne_zero', one_mul]
  inv_val := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    simp only [map_mul, map_sub, map_pow, map_one, coe_ρ', coe_Q']
    rw [← ρ_inv, ← Q_inv, mul_mul_mul_comm, inv_mul_cancel₀ ρ_ne_zero',
      inv_mul_cancel₀ Q_ne_zero', one_mul]

theorem ρQunit_coe : ((ρQunit : 𝓞 L) : L) = ρ * Q := by
  rw [RingOfIntegers.coe_eq_algebraMap]
  show algebraMap (𝓞 L) L (ρ' * Q') = _
  rw [map_mul, coe_ρ', coe_Q']

/-- **Control.** The hypothesis `ℚ⟮u⟯ = ⊤` is satisfiable (by `ρQ`). -/
theorem ρQunit_top : ℚ⟮((ρQunit : 𝓞 L) : L)⟯ = ⊤ := by
  rw [ρQunit_coe]; exact HermiteCompositum.Assembly.adjoin_ρQ_eq_top

/-- **Control.** The bound of `unit_deg12_ge` is attained. -/
theorem unit_deg12_attained : embHeight ((ρQunit : 𝓞 L) : L) = embHeight (ρ * Q) := by
  rw [ρQunit_coe]

/-- **Control.** Without `ℚ⟮u⟯ = ⊤` the bound fails (`u = 1`). -/
theorem control_hu_needed :
    embHeight (((1 : (𝓞 L)ˣ) : 𝓞 L) : L) < embHeight (ρ * Q) := by
  have h1 : (((1 : (𝓞 L)ˣ) : 𝓞 L) : L) = 1 := by simp
  rw [h1, embHeight_one]; exact one_lt_embHeight_ρQ

end

end RulerSelection.LaneC
