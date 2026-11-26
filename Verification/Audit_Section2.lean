import GrhFormalization.Section2_Reduction

open Lean Elab Command
open GRHIteratedThetaLifts.Section2

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``gammaR_ne_zero_of_re_pos,
    ``lemma_2_1_gammaFactor_ne_zero,
    ``prop_2_2_primitive_critical_line,
    ``cos_functional_eq_ne_zero,
    ``prop_2_3_rh_from_right_half_plane,
    ``lemma_2_4_euler_factor_ne_zero,
    ``lemma_2_5_reduction_to_primitive,
    ``cor_1_2_of_thm_1_1,
    ``cor_1_3_of_thm_1_1,
    ``cor_1_4_of_thm_1_1
  ]
  for decl in targets do
    let (_, st) := (CollectAxioms.collect decl).run env {}
    for ax in st.axioms do
      if ax ∉ allowed then
        throwError "STRICT AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT AUDIT PASSED: Section 2 uses only {propext, Classical.choice, Quot.sound}."
