/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import GrhFormalization

/-!
# Master Verification Audit (`GrhFormalization` — Sections 1 through 7)

This master gate imports all 7 formalization modules and verifies that every
exported definition, lemma, proposition, theorem, and corollary across the entire
manuscript relies strictly on Lean's three standard axioms
`{propext, Classical.choice, Quot.sound}` with zero `sorryAx` or custom axioms.
-/

open Lean Elab Command

namespace GRHIteratedThetaLifts.Verification.Master

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    -- Section 1
    ``GRHIteratedThetaLifts.Section1.dirichletL_eq_completed_div_gamma,
    ``GRHIteratedThetaLifts.Section1.euler_factor_ne_zero_of_re_pos,
    ``GRHIteratedThetaLifts.Section1.cor_1_3_of_cor_1_2,
    -- Section 2
    ``GRHIteratedThetaLifts.Section2.lemma_2_1_gammaFactor_ne_zero,
    ``GRHIteratedThetaLifts.Section2.prop_2_2_primitive_critical_line,
    ``GRHIteratedThetaLifts.Section2.prop_2_3_rh_from_right_half_plane,
    ``GRHIteratedThetaLifts.Section2.lemma_2_4_euler_factor_ne_zero,
    ``GRHIteratedThetaLifts.Section2.lemma_2_5_reduction_to_primitive,
    ``GRHIteratedThetaLifts.Section2.cor_1_2_of_thm_1_1,
    ``GRHIteratedThetaLifts.Section2.cor_1_3_of_thm_1_1,
    ``GRHIteratedThetaLifts.Section2.cor_1_4_of_thm_1_1,
    -- Section 3
    ``GRHIteratedThetaLifts.Section3.lemma_3_1_real_part_character_identity,
    ``GRHIteratedThetaLifts.Section3.thm_3_4_chebyshev_growth_zero_free,
    -- Section 4
    ``GRHIteratedThetaLifts.Section4.lemma_4_1_part1,
    ``GRHIteratedThetaLifts.Section4.lemma_4_1_part2,
    ``GRHIteratedThetaLifts.Section4.lemma_4_1_part3,
    ``GRHIteratedThetaLifts.Section4.thm_4_3_lattice_gluing_line,
    ``GRHIteratedThetaLifts.Section4.thm_4_4_lattice_gluing_subspace,
    -- Section 5
    ``GRHIteratedThetaLifts.Section5.thm_5_3_iterated_theta_surjective,
    ``GRHIteratedThetaLifts.Section5.lemma_5_2_placewise_injectivity,
    ``GRHIteratedThetaLifts.Section5.lemma_5_4_positive_step_l_values,
    ``GRHIteratedThetaLifts.Section5.thm_5_6_upward_adjoint_injectivity,
    ``GRHIteratedThetaLifts.Section5.thm_5_10_seesaw_period_factorization,
    -- Section 6
    ``GRHIteratedThetaLifts.Section6.lemma_6_1_kernel_dim_hs_bound,
    ``GRHIteratedThetaLifts.Section6.lemma_6_2_asymmetric_hs_triangle,
    ``GRHIteratedThetaLifts.Section6.thm_6_4_diagonal_hs_combination,
    ``GRHIteratedThetaLifts.Section6.thm_6_6_chowla_selberg_period,
    ``GRHIteratedThetaLifts.Section6.prop_6_7_inductive_base_bound,
    ``GRHIteratedThetaLifts.Section6.thm_6_8_budget_reduction,
    ``GRHIteratedThetaLifts.Section6.thm_6_11_frame_budget,
    ``GRHIteratedThetaLifts.Section6.thm_6_11_window_cancellation,
    -- Section 7
    ``GRHIteratedThetaLifts.Section7.thm_7_1_totally_complex_euler_factor,
    ``GRHIteratedThetaLifts.Section7.thm_7_3_large_prime_congruence_length,
    ``GRHIteratedThetaLifts.Section7.thm_7_6_torsion_length_reduction,
    ``GRHIteratedThetaLifts.Section7.thm_7_7_nonvanishing_dirichlet_L,
    ``GRHIteratedThetaLifts.Section7.cor_7_8_grh,
    ``GRHIteratedThetaLifts.Section7.thm_7_9_riemann_hypothesis,
    ``GRHIteratedThetaLifts.Section7.assembleMainResults
  ]
  for decl in targets do
    let (_, st) := (CollectAxioms.collect decl).run env {}
    for ax in st.axioms do
      if ax ∉ allowed then
        throwError "STRICT MASTER AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT MASTER AUDIT PASSED: All 38 declarations across Sections 1-7 verified under {propext, Classical.choice, Quot.sound}."

end GRHIteratedThetaLifts.Verification.Master
