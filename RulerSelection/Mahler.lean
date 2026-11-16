module

public import Mathlib
public import RulerSelection.Units

/-!
# C3(b), Mahler form: bridge B2 (easy form) and the Mahler-measure corollary (stage 2, lane C)

* `roots_eq_embeddings` : for `x ∈ L` with `ℚ⟮x⟯ = ⊤`, the complex roots of `minpoly ℚ x` are
  exactly the twelve values `σ x`, `σ : L →+* ℂ`, each once.
* `mahler_eq_embHeight` : for `x ∈ 𝓞 L` with `ℚ⟮x⟯ = ⊤`, the Mahler measure of `minpoly ℤ x`
  (mapped to `ℂ[X]`) equals `embHeight x` (Mathlib's `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`).
* `unit_deg12_mahler_ge`, `unit_deg12_mahler_eq_iff` : among units of `𝓞 L` of degree 12 the
  least Mahler measure is `M(minpoly ℤ (ρQ))`, attained exactly by `±(ρQ)^{±1}`.
-/

@[expose] public section

open NumberField IntermediateField Polynomial

namespace RulerSelection.LaneC

noncomputable section

open RulerSelection.Emb HermiteCompositum.Instance

theorem emb_injective_of_top (x : L) (hx : ℚ⟮x⟯ = ⊤) :
    Function.Injective (fun σ : L →+* ℂ => σ x) := by
  intro σ τ h
  have h' : σ x = τ x := h
  have hadj : Algebra.adjoin ℚ ({x} : Set L) = ⊤ := adjoin_eq_top_iff.1 hx
  have he : σ.toRatAlgHom = τ.toRatAlgHom := AlgHom.ext_of_adjoin_eq_top hadj (by
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    simpa [RingHom.toRatAlgHom_apply] using h')
  refine RingHom.ext fun y => ?_
  have := congrArg (fun f : L →ₐ[ℚ] ℂ => f y) he
  simpa [RingHom.toRatAlgHom_apply] using this

theorem roots_eq_embeddings (x : L) (hx : ℚ⟮x⟯ = ⊤) :
    ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots =
      Multiset.map (fun σ : L →+* ℂ => σ x) Finset.univ.val := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hne : (minpoly ℚ x).map (algebraMap ℚ ℂ) ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset (Multiset.Nodup.map (emb_injective_of_top x hx) Finset.univ.nodup)]
    intro a ha
    obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.1 ha
    rw [mem_roots hne, IsRoot.def, eval_map_algebraMap]
    have hσ : σ x = σ.toRatAlgHom x := rfl
    rw [hσ, aeval_algHom_apply, minpoly.aeval, map_zero]
  · calc Multiset.card ((minpoly ℚ x).map (algebraMap ℚ ℂ)).roots
        ≤ ((minpoly ℚ x).map (algebraMap ℚ ℂ)).natDegree := card_roots' _
      _ = (minpoly ℚ x).natDegree := natDegree_map _
      _ = 12 := by rw [← adjoin.finrank hint, hx, finrank_top', finrank_L]
      _ = Multiset.card (Multiset.map (fun σ : L →+* ℂ => σ x) Finset.univ.val) := by
        rw [Multiset.card_map, Finset.card_val, Finset.card_univ, card_emb]

theorem mahler_eq_embHeight_rat (x : L) (hx : ℚ⟮x⟯ = ⊤) :
    ((minpoly ℚ x).map (algebraMap ℚ ℂ)).mahlerMeasure = embHeight x := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, roots_eq_embeddings x hx,
    ((minpoly.monic hint).map _).leadingCoeff, norm_one, one_mul, Multiset.map_map, embHeight,
    Finset.prod_eq_multiset_prod]
  rfl

/-- **Bridge B2 (easy form).** For `x ∈ 𝓞 L` of degree 12, `M(minpoly ℤ x) = embHeight x`. -/
theorem mahler_eq_embHeight (x : 𝓞 L) (hx : ℚ⟮(x : L)⟯ = ⊤) :
    ((minpoly ℤ (x : L)).map (Int.castRingHom ℂ)).mahlerMeasure = embHeight (x : L) := by
  have hZ : IsIntegral ℤ (x : L) := RingOfIntegers.isIntegral_coe x
  have e := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hZ
  rw [← mahler_eq_embHeight_rat _ hx, e, Polynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)) (Int.castRingHom ℂ)]

/-- `M(minpoly ℤ (ρQ)) = H(ρQ)`. -/
theorem mahler_ρQ :
    ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure = embHeight (ρ * Q) := by
  have := mahler_eq_embHeight (ρQunit : 𝓞 L) ρQunit_top
  rwa [ρQunit_coe] at this

/-- **C3(b), Mahler form.** Every unit of `𝓞 L` of degree 12 has Mahler measure at least that of
`ρQ`. -/
theorem unit_deg12_mahler_ge (u : (𝓞 L)ˣ) (hu : ℚ⟮((u : 𝓞 L) : L)⟯ = ⊤) :
    ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ≤
      ((minpoly ℤ ((u : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [mahler_ρQ, mahler_eq_embHeight _ hu]; exact unit_deg12_ge u hu

/-- **C3(b), Mahler form, equality case.** -/
theorem unit_deg12_mahler_eq_iff (u : (𝓞 L)ˣ) (hu : ℚ⟮((u : 𝓞 L) : L)⟯ = ⊤) :
    ((minpoly ℤ ((u : 𝓞 L) : L)).map (Int.castRingHom ℂ)).mahlerMeasure =
        ((minpoly ℤ (ρ * Q)).map (Int.castRingHom ℂ)).mahlerMeasure ↔
      ((u : 𝓞 L) : L) ∈ ({ρ * Q, -(ρ * Q), (ρ * Q)⁻¹, -(ρ * Q)⁻¹} : Set L) := by
  rw [mahler_ρQ, mahler_eq_embHeight _ hu]; exact unit_deg12_eq_iff u hu

end

end RulerSelection.LaneC
