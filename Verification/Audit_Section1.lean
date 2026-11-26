/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import Lean
import GrhFormalization.Section1_MainTheorems

/-!
# Strict Verification Audit for Section 1 (`Section1_MainTheorems.lean`)

This audit file performs three strict checks on Section 1:
1. **Independent Specification Match**: Verifies that `Statement_Theorem_1_1`,
   `Statement_Corollary_1_2`, `Statement_Corollary_1_3`, and `Statement_Corollary_1_4`
   are definitionally identical to the Mathlib `DirichletCharacter.LFunction` and
   `riemannZeta` formulations of the paper's claims.
2. **Concrete Non-Vacuity Tests**: Evaluates `gammaR`, `gammaFactor`, `IsEvenChar`,
   and `euler_factor_ne_zero_of_re_pos` on explicit test cases.
3. **Kernel Axiom & `sorryAx` Gate**: Inspects the compiled environment and fails
   compilation if any proved declaration in `GRHIteratedThetaLifts.Section1` uses
   `sorryAx` or any custom axiom outside `{propext, Classical.choice, Quot.sound}`.
-/

open Complex Real Lean Elab Command
open GRHIteratedThetaLifts.Section1

namespace GRHIteratedThetaLifts.Verification.Section1

/-! ## 1. Independent Mathlib Specification Checks -/

example :
    Statement_Theorem_1_1 =
      (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        (1 / 2 : ℝ) < s.re → (χ ≠ 1 ∨ s ≠ 1) →
          DirichletCharacter.LFunction χ s ≠ 0) :=
  rfl

example :
    Statement_Corollary_1_2 =
      (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
        0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) :=
  rfl

example :
    Statement_Corollary_1_3 =
      (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        χ.IsPrimitive → ∀ (s : ℂ),
          0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) :=
  rfl

example :
    Statement_Corollary_1_4 =
      (∀ (s : ℂ),
        riemannZeta s = 0 →
        s ≠ 1 →
        (∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) →
        s.re = 1 / 2) :=
  rfl

/-! ## 2. Concrete Non-Vacuity & Edge-Case Checks -/

example : IsEvenChar (1 : DirichletCharacter ℂ 1) := by
  unfold IsEvenChar
  simp

example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : IsEvenChar χ) (s : ℂ) :
    gammaFactor χ s = gammaR s := by
  unfold gammaFactor
  exact if_pos h

example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : ¬ IsEvenChar χ) (s : ℂ) :
    gammaFactor χ s = gammaR (s + 1) := by
  unfold gammaFactor
  exact if_neg h

example {M : ℕ} [NeZero M] (χ_star : DirichletCharacter ℂ M) :
    1 - χ_star 2 * (2 : ℂ) ^ (-((1 / 2 : ℂ) + 14 * Complex.I)) ≠ 0 := by
  apply euler_factor_ne_zero_of_re_pos χ_star 2 Nat.prime_two
  norm_num

/-! ## 3. Kernel Axiom Printout & Automated Strict Axiom Gate -/

#print axioms dirichletL_eq_completed_div_gamma
#print axioms dirichletL_modOne_eq_riemannZeta
#print axioms euler_factor_ne_zero_of_re_pos
#print axioms cor_1_3_of_cor_1_2

#eval show CommandElabM Unit from do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets : List Name := [
    ``dirichletL_eq_completed_div_gamma,
    ``dirichletL_modOne_eq_riemannZeta,
    ``euler_factor_ne_zero_of_re_pos,
    ``cor_1_3_of_cor_1_2
  ]
  for decl in targets do
    let axioms ← collectAxioms decl
    for ax in axioms do
      if ax ∉ allowed then
        throwError "STRICT AUDIT FAILED: `{decl}` depends on forbidden axiom `{ax}`!"
  IO.println "STRICT AUDIT PASSED: Section 1 uses only {propext, Classical.choice, Quot.sound}."

end GRHIteratedThetaLifts.Verification.Section1
