import Lean
import GrhFormalization.Section3_LandauTauberian

open Lean Elab Command
open GRHIteratedThetaLifts.Section3

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``lemma_3_1_real_part_character_identity,
    ``CharacterLevel.multiplicity_pos,
    ``CharacterLevel.multiplicity_eq_mul_weight,
    ``CharacterLevel.multiplicity_inv,
    ``thm_3_4_chebyshev_growth_zero_free
  ]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax ∉ allowed then
        throwError "STRICT AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT AUDIT PASSED: Section 3 uses only {propext, Classical.choice, Quot.sound}."
