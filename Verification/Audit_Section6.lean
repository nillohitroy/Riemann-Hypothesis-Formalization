import Lean
import GrhFormalization.Section6_CurvatureAndBostSlope

open Lean Elab Command
open GRHIteratedThetaLifts.Section6

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``lemma_6_1_kernel_dim_hs_bound,
    ``lemma_6_2_asymmetric_hs_triangle,
    ``thm_6_4_diagonal_hs_combination,
    ``thm_6_6_chowla_selberg_period,
    ``prop_6_7_inductive_base_bound,
    ``thm_6_8_budget_reduction,
    ``thm_6_11_frame_budget,
    ``thm_6_11_window_cancellation
  ]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax ∉ allowed then
        throwError "STRICT AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT AUDIT PASSED: Section 6 uses only {propext, Classical.choice, Quot.sound}."
