module

public import Mathlib
public import HermiteCompositum.Places
public import HermiteCompositum.Extras
public import RulerSelection.Kron
public import RulerSelection.MahlerT2
public import RulerSelection.T2
public import RulerSelection.Box
public import RulerSelection.Perron

/-!
# Name probe

A record of the Mathlib and package declarations that the `HeightT2` modules rely on, at the
pinned toolchain and Mathlib commit. Each `#check` prints the elaborated signature in the build
log. The `example` at the end composes existing lemmas into a form the later modules use;
it declares nothing.
-/

@[expose] public section

open NumberField HermiteCompositum.Instance

/-! ## Heights in Mathlib -/
#check @Height.mulHeight₁
#check Height.mulHeight₁_eq
#check NumberField.instAdmissibleAbsValues
#check NumberField.mulHeight₁_eq
#check NumberField.prod_archAbsVal_eq
#check NumberField.totalWeight_eq_finrank
#check Height.mulHeight₁_inv
#check Height.mulHeight₁_neg
#check Height.mulHeight₁_pow
#check Height.one_le_mulHeight₁
#check NumberField.finite_setOfPred_mulHeight₁_le

/-! ## Finite places -/
#check NumberField.FinitePlace
#check NumberField.FinitePlace.norm_le_one
#check NumberField.FinitePlace.norm_embedding_eq
#check NumberField.FinitePlace.norm_eq_one_iff_notMem
#check NumberField.FinitePlace.maximalIdeal

/-! ## Infinite places and embeddings -/
#check NumberField.InfinitePlace.mult
#check NumberField.InfinitePlace.card_filter_mk_eq
#check NumberField.InfinitePlace.sum_mult_eq
#check NumberField.InfinitePlace.prod_eq_abs_norm
#check NumberField.InfinitePlace.mk
#check NumberField.InfinitePlace.apply
#check NumberField.Embeddings.card
#check NumberField.Embeddings.range_eval_eq_rootSet_minpoly
#check NumberField.Embeddings.pow_eq_one_of_norm_le_one
#check NumberField.Embeddings.pow_eq_one_of_norm_eq_one
#check NumberField.Embeddings.finite_of_norm_le

/-! ## Mahler measure -/
#check Polynomial.mahlerMeasure
#check Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots
#check Polynomial.mahlerMeasure_X_sub_C
#check Polynomial.mahlerMeasure_mul
#check Polynomial.prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff
#check Polynomial.one_le_mahlerMeasure_of_ne_zero
#check Polynomial.pow_eq_one_of_mahlerMeasure_eq_one

/-! ## Compositum, Kronecker, intermediate fields -/
#check @IntermediateField.LinearDisjoint
#check Matrix.PosSemidef.kronecker
#check NumberField.of_intermediateField
#check NumberField.of_module_finite

/-! ## The registered compositum package -/
#check HermiteCompositum.minpoly_inv_eq_of_norm_eq_one
#check HermiteCompositum.embeddingsEquiv
#check HermiteCompositum.embeddingsEquiv_apply
#check HermiteCompositum.restrictPair
#check HermiteCompositum.Instance.L
#check HermiteCompositum.Instance.ρ
#check HermiteCompositum.Instance.Q
#check HermiteCompositum.Instance.minpoly_ρ
#check HermiteCompositum.Instance.minpoly_Q
#check HermiteCompositum.Instance.S₃

/-! ## The selection chain -/
#check RulerSelection.Emb.embHeight
#print RulerSelection.Emb.embHeight
#check RulerSelection.Emb.T2
#print RulerSelection.Emb.T2
#check RulerSelection.Emb.sum_norm_sq_tensor
#check RulerSelection.Emb.embHeight_ρQ
#check RulerSelection.Emb.embHeight_neg
#check RulerSelection.Kron.kron_ge_diag
#check RulerSelection.Kron.kron_form_mono
#check RulerSelection.sum_norm_sq_le_of_prod_max_norm_le
#check RulerSelection.sum_le_of_prod_max_le_sharp
#check RulerSelection.LaneB.box_of_qf
#check RulerSelection.LaneB.coord_sq_le
#check RulerSelection.LaneC.small_height
#check RulerSelection.LaneC.small_height_unit
#check RulerSelection.LaneC.listed_small_not_top
#check RulerSelection.LaneC.mahler_eq_embHeight
#check RulerSelection.LaneC.mahler_eq_embHeight_rat
#check RulerSelection.LaneC.unit_deg12_ge
#check RulerSelection.LaneC.unit_deg12_eq_iff
#check RulerSelection.LaneC.IsPerronAt
#print RulerSelection.LaneC.IsPerronAt
#check RulerSelection.LaneC.ρQ_perron
#check RulerSelection.LaneC.not_perron_neg_ρQ
#check RulerSelection.LaneC.not_perron_inv_ρQ
#check RulerSelection.LaneC.not_perron_neg_inv_ρQ
#check RulerSelection.LaneC.ruler_selection
#check RulerSelection.LaneC.ρQ_selected

/-! ## Compositions the later modules use -/

/-- Finite places are at most one on algebraic integers. -/
example {K : Type*} [Field K] [NumberField K] (w : FinitePlace K) (x : 𝓞 K) :
    w (x : K) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one K (FinitePlace.maximalIdeal w) x

end
