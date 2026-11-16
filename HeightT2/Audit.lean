module

public import Mathlib
public import HeightT2.Probe
public import HeightT2.Defs
public import HeightT2.Bridge
public import HeightT2.Bound
public import HeightT2.Equality
public import HeightT2.Compositum
public import HeightT2.Instance.Generators
public import HeightT2.Instance.Perron
public import HeightT2.Instance.SmallHeight
public import HeightT2.Instance.EqualityL
public import HeightT2.Instance.Box
public import HeightT2.Review.GeneratorsProbes
public import HeightT2.Review.BridgeProbes
public import HeightT2.Review.EqualityProbes
public import HeightT2.Review.CompositumProbes

/-!
# Axiom audit for the `HeightT2` modules

One `#print axioms` line for every public theorem and definition of every `HeightT2` module
(main results, supporting lemmas, controls, certificates and the statement reviewers' probes),
grouped by module in dependency order. Building `HeightT2.Audit` prints every line in the build
log; each must list a subset of `[propext, Classical.choice, Quot.sound]`.
(`HeightT2.Probe` holds `#check` lines and one `example` only; it declares nothing.)
-/

@[expose] public section

/-! ## `HeightT2.Defs` -/
#print axioms HeightT2.IsPerronNumber
#print axioms HeightT2.aeval_eq_zero_of_mem_aroots_minpoly
#print axioms HeightT2.isPerronNumber_intCast
#print axioms HeightT2.isPerronNumber_one
#print axioms HeightT2.isPerronNumber_two
#print axioms HeightT2.not_isPerronNumber_of_lt_one
#print axioms HeightT2.isPerronNumber_one_add_sqrt_two
#print axioms HeightT2.not_isPerronNumber_sqrt_two
#print axioms HeightT2.t2Gram
#print axioms HeightT2.t2GramRe

/-! ## `HeightT2.Bridge` -/
#print axioms HeightT2.prod_infinitePlace_eq_prod_embeddings
#print axioms HeightT2.finitePlace_le_one
#print axioms HeightT2.finprod_finitePlace_eq_one
#print axioms HeightT2.one_le_finprod_finitePlace
#print axioms HeightT2.prod_embeddings_le_mulHeight₁
#print axioms HeightT2.mulHeight₁_eq_prod_embeddings
#print axioms HeightT2.mulHeight₁_eq_prod_embeddings_of_isIntegral
#print axioms HeightT2.mulHeight₁_rat_two
#print axioms HeightT2.control_bridge_integral_needed

/-! ## `HeightT2.Bound` -/
#print axioms HeightT2.sum_norm_sq_le_mulHeight₁_sq_add
#print axioms HeightT2.control_bound_attained_one
#print axioms HeightT2.control_bound_attained_rat_two

/-! ## `HeightT2.Equality` -/
#print axioms HeightT2.sum_add_one_lt_prod_add_card
#print axioms HeightT2.max_one_sq_eq
#print axioms HeightT2.isIntegral_of_finitePlace_le_one
#print axioms HeightT2.eq_case_structure
#print axioms HeightT2.sum_norm_sq_eq_mulHeight₁_sq_add_iff
#print axioms HeightT2.sum_norm_sq_eq_mulHeight₁_sq_add_iff_of_integer
#print axioms HeightT2.control_finrank_two_needed
#print axioms HeightT2.control_strict_two

/-! ## `HeightT2.Compositum` -/
#print axioms HeightT2.t2Gram_apply
#print axioms HeightT2.t2GramRe_apply
#print axioms HeightT2.conjugate_involutive
#print axioms HeightT2.t2Gram_isHermitian
#print axioms HeightT2.star_t2Gram
#print axioms HeightT2.t2Gram_eq_ofReal
#print axioms HeightT2.t2GramRe_isHermitian
#print axioms HeightT2.sum_norm_sq_eq_form
#print axioms HeightT2.sum_norm_sq_eq_t2GramRe
#print axioms HeightT2.t2GramRe_one
#print axioms HeightT2.sum_embeddings_compositum
#print axioms HeightT2.t2Gram_compositum
#print axioms HeightT2.t2GramRe_compositum
#print axioms HeightT2.sum_norm_sq_compositum
#print axioms HeightT2.coord_sq_le_sum_norm_sq
#print axioms HeightT2.form_one_sub_diag
#print axioms HeightT2.control_t2Gram_compositum_needs_sup
#print axioms HeightT2.control_coord_sq_le_needs_linearDisjoint
#print axioms HeightT2.control_coord_sq_le_needs_signs

/-! ## `HeightT2.Instance.Generators` -/
#print axioms HeightT2.ne_zero_of_adjoin_eq_top
#print axioms HeightT2.embHeight_generator_ge
#print axioms HeightT2.embHeight_generator_eq_iff
#print axioms HeightT2.mahlerMeasure_generator_ge
#print axioms HeightT2.mahlerMeasure_generator_eq_iff
#print axioms HeightT2.mahlerMeasure_generator_min
#print axioms HeightT2.control_generator_needed
#print axioms HeightT2.control_generator_attained
#print axioms HeightT2.one_lt_rhoR_mul_QR
#print axioms HeightT2.twoρQ
#print axioms HeightT2.twoρQ_coe
#print axioms HeightT2.twoρQ_top
#print axioms HeightT2.twoρQ_not_isUnit
#print axioms HeightT2.control_nonunit_generator

/-! ## `HeightT2.Instance.Perron` -/
#print axioms HeightT2.perronAt_generator_selection
#print axioms HeightT2.ρQ_perronAt_generator_selected
#print axioms HeightT2.negρQ
#print axioms HeightT2.negρQ_coe
#print axioms HeightT2.negρQ_top
#print axioms HeightT2.control_perron_needed
#print axioms HeightT2.aroots_minpoly_eq
#print axioms HeightT2.minpoly_real_eq
#print axioms HeightT2.isPerronAt_iff_isPerronNumber
#print axioms HeightT2.perronNumber_generator_selection
#print axioms HeightT2.ρQ_perronNumber_generator_selected
#print axioms HeightT2.perron_selection

/-! ## `HeightT2.Instance.SmallHeight` -/
#print axioms HeightT2.mulHeight₁_eq_embHeight
#print axioms HeightT2.mulHeight₁_ρQ
#print axioms HeightT2.mulHeight₁_le_mulHeight₁_ρQ_iff
#print axioms HeightT2.control_mulHeight₁_attained
#print axioms HeightT2.control_mulHeight₁_excluded

/-! ## `HeightT2.Instance.EqualityL` -/
#print axioms HeightT2.ρQ_not_root_of_unity
#print axioms HeightT2.control_strict_ρQ

/-! ## `HeightT2.Instance.Box` -/
#print axioms HeightT2.famS
#print axioms HeightT2.famT
#print axioms HeightT2.coe_gen₃
#print axioms HeightT2.coe_gen₄
#print axioms HeightT2.famS_coe
#print axioms HeightT2.famT_coe
#print axioms HeightT2.form_t2GramRe
#print axioms HeightT2.sum_comp_S₃
#print axioms HeightT2.sum_comp_S₄
#print axioms HeightT2.wS
#print axioms HeightT2.wT
#print axioms HeightT2.form_famS
#print axioms HeightT2.form_famT
#print axioms HeightT2.famS_ge
#print axioms HeightT2.famT_ge
#print axioms HeightT2.famS_cert
#print axioms HeightT2.famT_cert
#print axioms HeightT2.famST_sum
#print axioms HeightT2.box_of_sum_norm_sq_lt
#print axioms HeightT2.box_of_mulHeight₁_le
#print axioms HeightT2.box_of_embHeight_le
#print axioms HeightT2.box_of_embHeight_le_chain
#print axioms HeightT2.box_routes_agree
#print axioms HeightT2.Sp_form_nonneg
#print axioms HeightT2.Tp_form_nonneg
#print axioms HeightT2.small_height_in_L12_via_compositum

/-! ## `HeightT2.Review.GeneratorsProbes` -/
#print axioms HeightT2.Review.adjoin_eq_top_iff_natDegree
#print axioms HeightT2.Review.half_ρQ_top
#print axioms HeightT2.Review.half_ρQ_not_isIntegral
#print axioms HeightT2.Review.integrality_needed
#print axioms HeightT2.Review.norm_lt_rhoR_of_root
#print axioms HeightT2.Review.ρ_cube_sub
#print axioms HeightT2.Review.φL00_ρ
#print axioms HeightT2.Review.ρ_perronAt
#print axioms HeightT2.Review.isPerronNumber_rhoR
#print axioms HeightT2.Review.coe_ρ'_eq
#print axioms HeightT2.Review.minpoly_ρ_map
#print axioms HeightT2.Review.mahler_ρ_le_three
#print axioms HeightT2.Review.hx_needed_perronAt
#print axioms HeightT2.Review.hx_needed_perronNumber
#print axioms HeightT2.Review.twoρQ_perronAt
#print axioms HeightT2.Review.hmin_needed
#print axioms HeightT2.Review.aroots_minpoly_nodup
#print axioms HeightT2.Review.algEquiv_eq_refl

/-! ## `HeightT2.Review.BridgeProbes` -/
#print axioms HeightT2.Review.mulHeight₁_unfold
#print axioms HeightT2.Review.mulHeight₁_two_eq_pow
#print axioms HeightT2.Review.prod_embeddings_two
#print axioms HeightT2.Review.mulHeight₁_two_of_finrank_two
#print axioms HeightT2.Review.half_of_finrank_two
#print axioms HeightT2.Review.bound_at_half_of_finrank_two
#print axioms HeightT2.Review.prod_lt_height_half_of_finrank_two
#print axioms HeightT2.Review.rat_half_mathlib
#print axioms HeightT2.Review.embHeight_unfold
#print axioms HeightT2.Review.small_height_hx_needed

/-! ## `HeightT2.Review.EqualityProbes` -/
#print axioms HeightT2.Review.eq_hK_needed
#print axioms HeightT2.Review.eq_integer_hK_needed
#print axioms HeightT2.Review.eq_hK_satisfiable
#print axioms HeightT2.Review.eq_equality_at_neg_one
#print axioms HeightT2.Review.eq_neg_one_values
#print axioms HeightT2.Review.eq_rootOfUnity_iff
#print axioms HeightT2.Review.eq_structure_second_nontrivial
#print axioms HeightT2.Review.strict_lemma_hij_needed
#print axioms HeightT2.Review.strict_lemma_hyj_needed
#print axioms HeightT2.Review.strict_lemma_hy_needed

/-! ## `HeightT2.Review.CompositumProbes` -/
#print axioms HeightT2.Review.kron_needs_linearDisjoint
#print axioms HeightT2.Review.coord_needs_hb
#print axioms HeightT2.Review.coord_needs_hc
#print axioms HeightT2.Review.coord_of_hs_only
#print axioms HeightT2.Review.coord_attained
#print axioms HeightT2.Review.t2GramRe_diag
#print axioms HeightT2.Review.t2Gram_eq_trace_of_isReal

end
