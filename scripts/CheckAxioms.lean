/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import ProjectionConstants

/-!
# Axioms of the main results

Run with `lake env lean scripts/CheckAxioms.lean`. Every main result depends only on `propext`,
`Classical.choice` and `Quot.sound`: no `sorryAx`, and no `Lean.ofReduceBool` (`native_decide`).
-/

open ProjectionConstants.MainResults

-- Foundations
#print axioms maxProjConst_eq_iSup_maxRelProjConst
#print axioms absProjConst_le_sqrt
-- Chalmers–Lewicki, König–Lewis–Lin, quasimaximal constants
#print axioms maxRelProjConst_eq_sSup_parseval
#print axioms maxRelProjConst_le_delta
#print axioms existsETF_tfae
#print axioms maxProjConst_eq_quasiMaxConst
-- Bukh–Cox and the Gerzon bounds
#print axioms quasiRelConst_real_le
#print axioms quasiRelConst_complex_le
#print axioms maxProjConst_real_le_delta
#print axioms maxProjConst_real_eq_delta
#print axioms maxProjConst_complex_le_delta
#print axioms maxProjConst_complex_eq_delta
-- Explicit values
#print axioms maxProjConst_real_values
#print axioms maxProjConst_complex_eq_of_sic
#print axioms maxProjConst_complex_values
#print axioms maxProjConst_complex_eq_of_zaunerConjecture
-- Sign matrices
#print axioms maxProjConst_real_eq_sSup
#print axioms isGreatest_signMatrixValues_two
#print axioms ProjectionConstants.GrunbaumConjecture.maxProjConst_real_two
#print axioms maxRelProjConst_four_six
#print axioms maxRelProjConst_five_six
#print axioms ProjectionConstants.FourSix.kyFanSum_four_weightedSign_A1_le
#print axioms ProjectionConstants.FourSix.kyFanSum_four_weightedSign_A2_le
#print axioms ProjectionConstants.FourSix.isGreatest_kyFanSum_four_weightedSign_A3
-- Almost minimal orthogonal projections and monotonicity
#print axioms exists_almost_minimal_orthogonal_projection
#print axioms strictMono_maxProjConst_real
#print axioms maxProjConst_real_add_le_succ
-- Stabilization
#print axioms maxRelProjConst_eq_maxProjConst
#print axioms exists_weightedAbsSum_eq_maxProjConst
-- Sidelnikov–Welch and complementary dimensions
#print axioms recursive_welch_real
#print axioms recursive_welch_complex
#print axioms weighted_welch_real
#print axioms weighted_welch_complex
#print axioms weightedAbsSum_gram_le_real
#print axioms weightedAbsSum_gram_le_complex
#print axioms maxRelProjConst_compl_real
#print axioms maxRelProjConst_compl_complex
#print axioms maxRelProjConst_hyperplane
#print axioms maxRelProjConst_compl_values
-- Grünbaum: invariance, the Banach–Mazur estimate, `ℓ₁ⁿ` and the regular polygons
#print axioms absProjConst_congr
#print axioms absProjConst_eq_relProjConst
#print axioms absProjConst_le_mul_norm_mul_norm
#print axioms absProjConst_le_mul_of_le_of_le
#print axioms absProjConst_range_circulant
#print axioms absProjConst_l1
#print axioms absProjConst_l1_odd_eq_even
#print axioms absProjConst_regularPolygon
#print axioms absProjConst_regularPolygon_of_even
#print axioms absProjConst_regularPolygon_of_odd
#print axioms absProjConst_regularPolygon_two_pow
#print axioms absProjConst_regularPolygon_values
#print axioms absProjConst_regularPolygon_three_eq_maxProjConst
#print axioms absProjConst_le_four_thirds
-- Euclidean spaces
#print axioms absProjConst_euclideanSpace_eq
#print axioms absProjConst_euclideanSpace_real
#print axioms absProjConst_euclideanSpace_complex
#print axioms absProjConst_euclideanSpace_values
#print axioms absProjConst_euclideanSpace_real_eq_grunbaum
#print axioms absProjConst_euclideanSpace_real_odd
#print axioms ProjectionConstants.absProjConst_euclideanSpace
#print axioms ProjectionConstants.absProjConst_euclideanSpace_real_one
#print axioms ProjectionConstants.absProjConst_euclideanSpace_complex_one
-- Rudin: averaging, Rudin's principle, the circle
#print axioms exists_isProjectionOnto_isEquivariant
#print axioms relProjConst_eq_norm
#print axioms relProjConst_trigPoly
#print axioms relProjConst_trigPoly_values
#print axioms relProjConst_trigPoly_bounds
#print axioms tendsto_relProjConst_trigPoly_atTop
#print axioms exists_not_bddAbove_of_isProjectionOnto
#print axioms exists_not_bddAbove_fourierPartialSum_apply_zero
#print axioms exists_isProjectionOnto_spectralSubspace_iff
#print axioms exists_isProjectionOnto_spectralSubspace_of_periodic
#print axioms not_exists_isProjectionOnto_discAlgebra
#print axioms ProjectionConstants.IsRepresentation.exists_isProjectionOnto_isEquivariant_of_fintype
#print axioms ProjectionConstants.IsAddRepresentation.relProjConst_eq_norm
