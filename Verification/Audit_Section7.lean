/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import Lean
import GrhFormalization.Section7_CohomologyAndGRH

open Lean Elab Command
open GRHIteratedThetaLifts.Section1
open GRHIteratedThetaLifts.Section7

namespace GRHIteratedThetaLifts.Verification.Section7

#check (thm_7_7_nonvanishing_dirichlet_L :
  ∀ (γ_em : ℝ) (logDerivMap : Section3.PrimitiveChar → ℂ),
    Section3.LandauAnalyticBackend →
    Section6.Section6BreakthroughInterface γ_em logDerivMap →
    Section2.PrimitiveLFunctionTheory →
    Statement_Theorem_1_1)

#check (cor_7_8_grh :
  Statement_Theorem_1_1 → Section2.PrimitiveLFunctionTheory → Statement_Corollary_1_2)

#check (thm_7_9_riemann_hypothesis :
  Statement_Theorem_1_1 → Statement_Corollary_1_4)

#check (assembleMainResults :
  Statement_Theorem_1_1 → Section2.PrimitiveLFunctionTheory → ∃ _ : MainResultsBundle, True)

#print axioms thm_7_1_totally_complex_euler_factor
#print axioms thm_7_3_large_prime_congruence_length
#print axioms thm_7_6_torsion_length_reduction
#print axioms thm_7_7_nonvanishing_dirichlet_L
#print axioms cor_7_8_grh
#print axioms thm_7_9_riemann_hypothesis
#print axioms assembleMainResults

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``thm_7_1_totally_complex_euler_factor,
    ``thm_7_3_large_prime_congruence_length,
    ``thm_7_6_torsion_length_reduction,
    ``thm_7_7_nonvanishing_dirichlet_L,
    ``cor_7_8_grh,
    ``thm_7_9_riemann_hypothesis,
    ``assembleMainResults
  ]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax ∉ allowed then
        throwError "STRICT SECTION 7 AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT SECTION 7 AUDIT PASSED: All Section 7 theorems use only {propext, Classical.choice, Quot.sound}."

end GRHIteratedThetaLifts.Verification.Section7
