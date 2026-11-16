module
public import Solution
public import HeightT2.Equality
public import HeightT2.Compositum

@[expose] public section
/-!
# Axioms

`#print axioms` for the three compared statements (as proved in `Solution.lean`), the definitions
they use, and a selection of the uncompared supporting theorems and controls named in the README, formalization.yaml and the HeightT2 module docstrings. Build with
`lake build Axioms`; every line should read `[propext, Classical.choice, Quot.sound]` or a subset.
The full list for every declaration of the `HeightT2` library is `HeightT2/Audit.lean`.
`HeightT2.Equality` and `HeightT2.Compositum` are imported here, not in `Solution.lean`, for the
uncompared equality case `HeightT2.sum_norm_sq_eq_mulHeight₁_sq_add_iff`, the uncompared Gram
identity `HeightT2.t2Gram_compositum`, the uncompared coordinate bound
`HeightT2.coord_sq_le_sum_norm_sq`, and the theorems and controls of those modules.
-/

-- the three compared statements
#print axioms IntegralGeneratorHeights.mulHeight₁_le_mulHeight₁_ρQ_iff
#print axioms IntegralGeneratorHeights.mahlerMeasure_generator_min
#print axioms IntegralGeneratorHeights.perronNumber_generator_selection
-- the definitions the statements use
#print axioms HeightT2.IsPerronNumber
#print axioms HermiteCompositum.Instance.L
#print axioms HermiteCompositum.Instance.ρ
#print axioms HermiteCompositum.Instance.Q
-- the definitions of the uncompared Gram identity and coordinate bound
#print axioms HeightT2.t2Gram
#print axioms HeightT2.t2GramRe
-- uncompared supporting theorems and controls (README, formalization.yaml, HeightT2 docstrings):
-- the Gram identity and the coordinate bound (used by no compared proof), the inequality and its
-- equality case, and the library lemmas the compared proofs use in their place
#print axioms HeightT2.t2Gram_compositum
#print axioms HeightT2.coord_sq_le_sum_norm_sq
#print axioms RulerSelection.Emb.T2_le_embHeight_sq_add
#print axioms RulerSelection.Kron.kron_ge_diag
#print axioms HeightT2.sum_norm_sq_eq_mulHeight₁_sq_add_iff
#print axioms HeightT2.sum_norm_sq_le_mulHeight₁_sq_add
#print axioms HeightT2.mulHeight₁_eq_prod_embeddings
#print axioms HeightT2.prod_embeddings_le_mulHeight₁
#print axioms HeightT2.sum_norm_sq_eq_mulHeight₁_sq_add_iff_of_integer
#print axioms HeightT2.t2GramRe_compositum
#print axioms HeightT2.sum_norm_sq_compositum
#print axioms HeightT2.perronAt_generator_selection
#print axioms HeightT2.isPerronAt_iff_isPerronNumber
#print axioms HeightT2.perron_selection
#print axioms HeightT2.ρQ_perronNumber_generator_selected
#print axioms HeightT2.ρQ_perronAt_generator_selected
#print axioms HeightT2.control_perron_needed
#print axioms HeightT2.control_generator_needed
#print axioms HeightT2.control_nonunit_generator
#print axioms HeightT2.control_finrank_two_needed
#print axioms HeightT2.control_strict_two
#print axioms HeightT2.control_t2Gram_compositum_needs_sup
#print axioms HeightT2.control_coord_sq_le_needs_linearDisjoint
#print axioms HeightT2.control_coord_sq_le_needs_signs
#print axioms HeightT2.control_mulHeight₁_attained
#print axioms HeightT2.control_mulHeight₁_excluded
#print axioms RulerSelection.LaneC.ruler_selection
