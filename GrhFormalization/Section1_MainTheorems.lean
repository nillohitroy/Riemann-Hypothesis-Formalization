/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Section 1: Introduction and Statement of Main Results

This file formalizes the definitions, conventions, and top-level theorem statements
from Section 1 of the manuscript using Mathlib's analytic continuation
`DirichletCharacter.LFunction`:
- Subsection 1.1: `Theorem 1.1` (`Statement_Theorem_1_1`),
  `Corollary 1.2` (`Statement_Corollary_1_2`),
  `Corollary 1.3` (`Statement_Corollary_1_3`),
  `Corollary 1.4` (`Statement_Corollary_1_4`), and
  `Remark 1.1` (`euler_factor_ne_zero_of_re_pos`).
- Subsection 1.2: Top-level reduction interface `MainResultsBundle`.
- Subsection 1.3: Parity of Dirichlet characters, archimedean gamma factors `γ_χ(s)`,
  and completed L-functions `Λ(s, χ)`.
-/

open Complex Real
open scoped BigOperators

namespace GRHIteratedThetaLifts.Section1

/-! ## Subsection 1.3: Notation and Conventions -/

/-- The Dirichlet L-function `L(s, χ)` defined via Mathlib's analytic continuation
`DirichletCharacter.LFunction`. -/
noncomputable def dirichletL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s

/-- A Dirichlet character `χ` modulo `N` is even if `χ (-1) = 1`, and odd otherwise. -/
def IsEvenChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  χ (-1) = 1

/-- The real archimedean gamma factor `Γ_ℝ(s) = π^(-s/2) Γ(s/2)` (Eq. 1.5). -/
noncomputable def gammaR (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The archimedean gamma factor `γ_χ(s)` of a Dirichlet character `χ` (Eq. 1.5):
`Γ_ℝ(s)` if `χ` is even, and `Γ_ℝ(s + 1)` if `χ` is odd. -/
noncomputable def gammaFactor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := by
  classical
  exact if IsEvenChar χ then gammaR s else gammaR (s + 1)

/-- The completed Dirichlet L-function `Λ(s, χ) = L(s, χ) * γ_χ(s)`. -/
noncomputable def completedLFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  dirichletL χ s * gammaFactor χ s

/-- Relation `L(s, χ) = Λ(s, χ) / γ_χ(s)` whenever `γ_χ(s) ≠ 0`. -/
lemma dirichletL_eq_completed_div_gamma {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hγ : gammaFactor χ s ≠ 0) :
    dirichletL χ s = completedLFunction χ s / gammaFactor χ s := by
  unfold completedLFunction
  exact (mul_div_cancel_right₀ _ hγ).symm

/-- For modulus `1`, `DirichletCharacter.LFunction` agrees with `riemannZeta`. -/
lemma dirichletL_modOne_eq_riemannZeta (χ : DirichletCharacter ℂ 1) (s : ℂ) :
    dirichletL χ s = riemannZeta s := by
  unfold dirichletL
  rw [DirichletCharacter.LFunction_modOne_eq]

/-! ## Subsection 1.1: Statement of Main Theorems -/

/-- **Theorem 1.1 (Non-Vanishing on `Re(s) > 1/2`)** (`thm:all-chi`):
For every positive integer `N`, every Dirichlet character `χ` modulo `N`, and every `s ∈ ℂ`
with `Re(s) > 1/2`, if either `χ ≠ 1` or `s ≠ 1`, then `L(s, χ) ≠ 0`. -/
def Statement_Theorem_1_1 : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (1 / 2 : ℝ) < s.re → (χ ≠ 1 ∨ s ≠ 1) → dirichletL χ s ≠ 0

/-- **Corollary 1.2 (Generalized Riemann Hypothesis)** (`cor:grh-intro`):
For every positive integer `N`, every Dirichlet character `χ` modulo `N`, and every `s ∈ ℂ`
with `0 < Re(s) < 1`, if `L(s, χ) = 0`, then `Re(s) = 1/2`. -/
def Statement_Corollary_1_2 : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → dirichletL χ s = 0 → s.re = 1 / 2

/-- **Corollary 1.3 (Generalized Riemann Hypothesis for Primitive Characters)**:
For every positive integer `N`, every primitive Dirichlet character `χ` modulo `N`,
and every `s ∈ ℂ` with `0 < Re(s) < 1`, if `L(s, χ) = 0`, then `Re(s) = 1/2`. -/
def Statement_Corollary_1_3 : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → ∀ (s : ℂ),
      0 < s.re → s.re < 1 → dirichletL χ s = 0 → s.re = 1 / 2

/-- **Corollary 1.4 (The Riemann Hypothesis)** (`cor:rh-intro`):
For every `s ∈ ℂ`, if `ζ(s) = 0`, `s ≠ 1`, and `s ≠ -2(n + 1)` for every `n ∈ ℕ`,
then `Re(s) = 1/2`. -/
def Statement_Corollary_1_4 : Prop :=
  ∀ (s : ℂ),
    riemannZeta s = 0 →
    s ≠ 1 →
    (∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) →
    s.re = 1 / 2

/-! ## Remark 1.1: Non-Vanishing of Extra Euler Factors in the Open Critical Strip -/

/-- **Remark 1.1 (`rem:lean-correspondence`):**
For any character `χ_star` modulo `M` and any prime `p`, the Euler factor
`1 - χ_star(p) p^(-s)` does not vanish when `Re(s) > 0` (in particular, inside `0 < Re(s) < 1`). -/
lemma euler_factor_ne_zero_of_re_pos {M : ℕ} [NeZero M]
    (χ_star : DirichletCharacter ℂ M) (p : ℕ) (hp : p.Prime)
    (s : ℂ) (hs : 0 < s.re) :
    1 - χ_star p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have heq : χ_star p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hp_gt_one : (1 : ℝ) < (p : ℝ) := Nat.one_lt_cast.mpr hp.one_lt
  have hnorm_pow : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp
  have hnorm_lt_one : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt_one (neg_lt_zero.mpr hs)
  have hnorm_char : ‖χ_star p‖ ≤ 1 := DirichletCharacter.norm_le_one χ_star p
  have hprod_lt_one : ‖χ_star p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖χ_star p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hnorm_char (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
      _ < 1 := hnorm_lt_one
  rw [heq, norm_one] at hprod_lt_one
  exact lt_irrefl 1 hprod_lt_one

/-! ## Subsection 1.2: Top-Level Architecture Interface -/

/-- Immediate deduction of `Corollary 1.3` from `Corollary 1.2` (Subsection 1.1). -/
theorem cor_1_3_of_cor_1_2 (hGRH : Statement_Corollary_1_2) : Statement_Corollary_1_3 := by
  intro N _ χ _ s hs0 hs1 hL
  exact hGRH N χ s hs0 hs1 hL

/-- Top-level theorem bundle assembled in Section 7.3 from `Statement_Theorem_1_1`
and the Section 2 reductions. -/
structure MainResultsBundle where
  /-- Theorem 1.1 (`Re(s) > 1/2` non-vanishing for all Dirichlet characters). -/
  thm_1_1 : Statement_Theorem_1_1
  /-- Corollary 1.2 (GRH for all Dirichlet characters). -/
  cor_1_2 : Statement_Corollary_1_2
  /-- Corollary 1.3 (GRH for primitive Dirichlet characters). -/
  cor_1_3 : Statement_Corollary_1_3
  /-- Corollary 1.4 (The classical Riemann Hypothesis). -/
  cor_1_4 : Statement_Corollary_1_4

end GRHIteratedThetaLifts.Section1
