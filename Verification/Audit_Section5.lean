import Lean
import GrhFormalization.Section5_IteratedThetaLifts

open Lean Elab Command
open GRHIteratedThetaLifts.Section5

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``thm_5_3_iterated_theta_surjective,
    ``lemma_5_2_placewise_injectivity,
    ``lemma_5_4_positive_step_l_values,
    ``thm_5_6_upward_adjoint_injectivity,
    ``thm_5_10_seesaw_period_factorization
  ]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax ∉ allowed then
        throwError "STRICT AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT AUDIT PASSED: Section 5 uses only {propext, Classical.choice, Quot.sound}."
