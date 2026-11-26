/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import GrhFormalization.Section1_MainTheorems
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Section 2: Reduction to Non-Vanishing on `Re(s) > 1/2`

This file formalizes all results in Section 2 of the manuscript against Section 1's
analytic continuation `dirichletL`:
- **Lemma 2.1** (`lemma_2_1_gammaFactor_ne_zero`): `γ_χ(s) ≠ 0` on `Re(s) > 0`.
- **Proposition 2.2** (`prop_2_2_primitive_critical_line`): Critical-line confinement for
  primitive Dirichlet characters assuming Theorem 1.1 and the primitive functional equation.
- **Proposition 2.3** (`prop_2_3_rh_from_right_half_plane`): Riemann Hypothesis from
  right half-plane non-vanishing of `ζ(s)` via Riemann's functional equation.
- **Lemma 2.4** (`lemma_2_4_euler_factor_ne_zero`): Non-vanishing of local Euler factors.
- **Lemma 2.5** (`lemma_2_5_reduction_to_primitive`): Reduction of critical-strip zeros
  to the inducing primitive character `χ*`.
- **Subsection 2.3** (`cor_1_2_of_thm_1_1`, `cor_1_3_of_thm_1_1`, `cor_1_4_of_thm_1_1`).
-/

open Complex Real
open scoped BigOperators

namespace GRHIteratedThetaLifts.Section2

open GRHIteratedThetaLifts.Section1

/-! ## Subsection 2.1: Functional Equation and Symmetry of Zeros -/

/-- Real archimedean gamma factor `Γ_ℝ(w) = π^(-w/2) Γ(w/2)` does not vanish when `Re(w) > 0`. -/
lemma gammaR_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : gammaR w ≠ 0 := by
  unfold gammaR
  apply mul_ne_zero
  · rw [Ne, cpow_eq_zero_iff]
    push Not
    intro hpi
    exfalso
    exact Real.pi_ne_zero (Complex.ofReal_eq_zero.mp hpi)
  · apply Complex.Gamma_ne_zero_of_re_pos
    simpa using half_pos hw

/-- **Lemma 2.1 (Non-Vanishing of the Gamma Factor)**:
For every `N ≥ 1`, every Dirichlet character `χ` modulo `N`, and every `s ∈ ℂ` with
`Re(s) > 0`, we have `γ_χ(s) ≠ 0`. -/
lemma lemma_2_1_gammaFactor_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  unfold gammaFactor
  split_ifs
  · exact gammaR_ne_zero_of_re_pos hs
  · apply gammaR_ne_zero_of_re_pos
    simpa using add_pos hs zero_lt_one

/-- Analytic properties and functional equation package for `DirichletCharacter.LFunction`
used in Proposition 2.2, Lemma 2.5, and Theorem 7.7. -/
structure PrimitiveLFunctionTheory where
  /-- Functional equation relating `Λ(1 - s, χ⁻¹)` and `Λ(s, χ)` for primitive `χ`. -/
  functional_eq : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → ∀ (s : ℂ),
      ∃ ε_root : ℂ, completedLFunction χ⁻¹ (1 - s) = ε_root * completedLFunction χ s
  /-- Imprimitive level-change Euler product factorization
  `L(s, χ) = L(s, χ*) ∏_{p|N} (1 - χ*(p) p^{-s})` whenever `χ ≠ 1 ∨ s ≠ 1`. -/
  imprimitive_factorization : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {M : ℕ} [NeZero M] (χ_star : DirichletCharacter ℂ M),
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → χ p = χ_star p) →
    ∀ (s : ℂ), (χ ≠ 1 ∨ s ≠ 1) →
      dirichletL χ s =
        dirichletL χ_star s *
          ∏ p ∈ Nat.primeFactors N, (1 - χ_star p * (p : ℂ) ^ (-s))
  /-- Every Dirichlet character `χ` mod `N` is induced by a unique primitive character `χ*`
  mod `M | N`, and `χ = 1 ↔ χ* = 1`. -/
  prim_of_chi : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
    ∃ (M : ℕ) (_ : NeZero M) (χ_star : DirichletCharacter ℂ M),
      χ_star.IsPrimitive ∧ (χ = 1 ↔ χ_star = 1) ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → χ p = χ_star p
  /-- Dirichlet's theorem on non-vanishing at `s = 1` for non-principal primitive characters:
  `L(1, χ*) ≠ 0` when `χ* ≠ 1`. -/
  nonvanish_at_one : ∀ {M : ℕ} [NeZero M] (χ_star : DirichletCharacter ℂ M),
    χ_star.IsPrimitive → χ_star ≠ 1 → dirichletL χ_star 1 ≠ 0

/-- **Proposition 2.2 (Critical-Line Confinement for Primitive Characters)**:
Assume Theorem 1.1 and the primitive functional equation. For every `N ≥ 1`, every
primitive character `χ` modulo `N`, and `0 < Re(s) < 1`, `L(s, χ) = 0 → Re(s) = 1/2`. -/
theorem prop_2_2_primitive_critical_line
    (hThm11 : Statement_Theorem_1_1)
    (hFE : PrimitiveLFunctionTheory) :
    Statement_Corollary_1_3 := by
  intro N _ χ hprim s hs0 hs1 hL
  by_contra hne
  have hs_ne_zero : s ≠ 0 := by
    intro h0; rw [h0, zero_re] at hs0; exact lt_irrefl 0 hs0
  have hs_ne_one : s ≠ 1 := by
    intro h1; rw [h1, one_re] at hs1; exact lt_irrefl 1 hs1
  rcases lt_trichotomy s.re (1 / 2 : ℝ) with hlt | heq | hgt
  · -- Case 2: Re(s) < 1/2
    have hγ : gammaFactor χ s ≠ 0 := lemma_2_1_gammaFactor_ne_zero χ hs0
    have hΛ : completedLFunction χ s = 0 := by
      unfold completedLFunction
      rw [hL, zero_mul]
    obtain ⟨ε_root, hfunc⟩ := hFE.functional_eq χ hprim s
    have hΛ_ref : completedLFunction χ⁻¹ (1 - s) = 0 := by
      rw [hfunc, hΛ, mul_zero]
    have h1s_pos : 0 < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    have h1s_half : (1 / 2 : ℝ) < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    have h1s_ne_one : 1 - s ≠ 1 := by
      intro h1; apply hs_ne_zero; linear_combination -h1
    have hγ_inv : gammaFactor χ⁻¹ (1 - s) ≠ 0 :=
      lemma_2_1_gammaFactor_ne_zero χ⁻¹ h1s_pos
    have hL_ref : dirichletL χ⁻¹ (1 - s) = 0 := by
      rw [dirichletL_eq_completed_div_gamma χ⁻¹ (1 - s) hγ_inv, hΛ_ref, zero_div]
    exact hThm11 N χ⁻¹ (1 - s) h1s_half (Or.inr h1s_ne_one) hL_ref
  · exact hne heq
  · -- Case 1: Re(s) > 1/2
    exact hThm11 N χ s hgt (Or.inr hs_ne_one) hL

/-- Helper: `cos (π * (1 - s) / 2) ≠ 0` when `Re(s) < 1/2`, `s ≠ 0`, and `s ≠ -2(n+1)`. -/
lemma cos_functional_eq_ne_zero {s : ℂ} (hs_lt : s.re < 1 / 2)
    (hs0 : s ≠ 0) (htriv : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) :
    Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
  intro hcos
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs_eq : s = -2 * (k : ℂ) := by
    have hmul : (Real.pi : ℂ) * (1 - s) = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination 2 * hk
    have h1s : 1 - s = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hpi hmul
    linear_combination -h1s
  have hre : s.re = -2 * (k : ℝ) := by
    rw [hs_eq]; simp
  rcases lt_trichotomy k 0 with hk_neg | hk_zero | hk_pos
  · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    linarith
  · subst hk_zero
    apply hs0
    simpa using hs_eq
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.le_sub_one_of_lt hk_pos)
    have hk_nat : k = (n : ℤ) + 1 := by omega
    apply htriv n
    rw [hs_eq, hk_nat]
    push_cast
    ring

/-- **Proposition 2.3 (Riemann Hypothesis from Right Half-Plane Non-Vanishing)**:
Assume `ζ(s) ≠ 0` for all `Re(s) > 1/2` with `s ≠ 1`. Then every non-trivial zero of
`ζ(s)` satisfies `Re(s) = 1/2`. -/
theorem prop_2_3_rh_from_right_half_plane
    (hRight : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    Statement_Corollary_1_4 := by
  intro s hζ hs1 htriv
  rcases lt_trichotomy s.re (1 / 2 : ℝ) with hlt | heq | hgt
  · -- Case 3: Re(s) < 1/2
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, riemannZeta_zero] at hζ
      norm_num at hζ
    have h1s_ne_one : 1 - s ≠ 1 := by
      intro h1; apply hs0; linear_combination -h1
    have h1s_re : (1 / 2 : ℝ) < (1 - s).re := by
      rw [sub_re, one_re]; linarith
    have h1s_pos : 0 < (1 - s).re := by linarith
    have h1s_ne_neg_nat : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
      intro n hneg
      have hre_neg : (1 - s).re = -(n : ℝ) := by rw [hneg]; simp
      have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub h1s_ne_neg_nat h1s_ne_one
    rw [sub_sub_cancel, hζ] at hfe
    have hf1 : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      rw [Ne, cpow_eq_zero_iff]
      push Not
      intro h2pi
      exfalso
      apply mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h2pi
    have hf2 : Complex.Gamma (1 - s) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos h1s_pos
    have hf3 : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 :=
      cos_functional_eq_ne_zero hlt hs0 htriv
    have hf4 : riemannZeta (1 - s) ≠ 0 :=
      hRight (1 - s) h1s_re h1s_ne_one
    exfalso
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hf1 hf2) hf3) hf4 hfe.symm
  · exact heq
  · -- Case 2: Re(s) > 1/2
    exfalso
    exact hRight s hgt hs1 hζ

/-! ## Subsection 2.2: Imprimitive Characters and Euler Factors -/

/-- **Lemma 2.4 (Non-Vanishing of Local Euler Factors)**:
For every `M ≥ 1`, every Dirichlet character `ψ` modulo `M`, every `s ∈ ℂ` with `Re(s) > 0`,
and every prime `p`, `1 - ψ(p) p^(-s) ≠ 0`. -/
lemma lemma_2_4_euler_factor_ne_zero {M : ℕ} [NeZero M]
    (ψ : DirichletCharacter ℂ M) (p : ℕ) (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) :
    1 - ψ p * (p : ℂ) ^ (-s) ≠ 0 :=
  euler_factor_ne_zero_of_re_pos ψ p hp s hs

/-- **Lemma 2.5 (Reduction of Critical-Strip Zeros to Primitive Characters)**:
If `0 < Re(s) < 1` and `L(s, χ) = 0`, then `L(s, χ*) = 0` for the inducing primitive
character `χ*`. -/
theorem lemma_2_5_reduction_to_primitive
    (hFE : PrimitiveLFunctionTheory)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {M : ℕ} [NeZero M] (χ_star : DirichletCharacter ℂ M)
    (hind : ∀ p : ℕ, p.Prime → ¬ p ∣ N → χ p = χ_star p)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hL : dirichletL χ s = 0) :
    dirichletL χ_star s = 0 := by
  have hs_ne_one : s ≠ 1 := by
    intro h1; rw [h1, one_re] at hs1; exact lt_irrefl 1 hs1
  have hfac := hFE.imprimitive_factorization χ χ_star hind s (Or.inr hs_ne_one)
  rw [hL] at hfac
  rcases mul_eq_zero.mp hfac.symm with hL_star | hprod
  · exact hL_star
  · exfalso
    rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨p, hp_mem, hp_zero⟩ := hprod
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    exact lemma_2_4_euler_factor_ne_zero χ_star p hp_prime hs0 hp_zero

/-! ## Subsection 2.3: Proof of the Reduction -/

/-- **Subsection 2.3 (Proof of Corollary 1.2 from Theorem 1.1)**:
Every zero of `L(s, χ)` in `0 < Re(s) < 1` lies on `Re(s) = 1/2`. -/
theorem cor_1_2_of_thm_1_1
    (hThm11 : Statement_Theorem_1_1)
    (hFE : PrimitiveLFunctionTheory) :
    Statement_Corollary_1_2 := by
  intro N _ χ s hs0 hs1 hL
  obtain ⟨M, hM, χ_star, hprim, _, hind⟩ := hFE.prim_of_chi χ
  have hL_star : dirichletL χ_star s = 0 :=
    lemma_2_5_reduction_to_primitive hFE χ χ_star hind hs0 hs1 hL
  exact prop_2_2_primitive_critical_line hThm11 hFE M χ_star hprim s hs0 hs1 hL_star

/-- **Subsection 2.3 (Proof of Corollary 1.3 from Theorem 1.1)**. -/
theorem cor_1_3_of_thm_1_1
    (hThm11 : Statement_Theorem_1_1)
    (hFE : PrimitiveLFunctionTheory) :
    Statement_Corollary_1_3 :=
  prop_2_2_primitive_critical_line hThm11 hFE

/-- **Subsection 2.3 (Proof of Corollary 1.4 from Theorem 1.1)**
directly via Section 1's `dirichletL_modOne_eq_riemannZeta`. -/
theorem cor_1_4_of_thm_1_1
    (hThm11 : Statement_Theorem_1_1) :
    Statement_Corollary_1_4 := by
  apply prop_2_3_rh_from_right_half_plane
  intro s hs_re hs_ne1
  rw [← dirichletL_modOne_eq_riemannZeta (1 : DirichletCharacter ℂ 1) s]
  exact hThm11 1 (1 : DirichletCharacter ℂ 1) s hs_re (Or.inr hs_ne1)

end GRHIteratedThetaLifts.Section2
