import Lean
import GrhFormalization.Section4_HermitianGluing

open Lean Elab Command
open GRHIteratedThetaLifts.Section4

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``lemma_4_1_part1,
    ``lemma_4_1_part2,
    ``lemma_4_1_part3,
    ``thm_4_3_lattice_gluing_line,
    ``thm_4_4_lattice_gluing_subspace
  ]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax ∉ allowed then
        throwError "STRICT AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT AUDIT PASSED: Section 4 uses only {propext, Classical.choice, Quot.sound}."
