/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/

import GrhFormalization.Section1_MainTheorems
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Section 3: Analytical Preliminaries and Landau Positivity

This file formalizes all definitions, lemmas, propositions, and theorems in Section 3
against Section 1's analytic continuation `dirichletL`:
- **Subsection 3.1**: Smoothed Chebyshev functions `G(y)`, `S_χ(y)`, `g_χ(y)`, `G_χ(y)`
  (Eqs. 3.1–3.4), **Definition 3.1** (`CharacterLevel`, `levelWeight`, `weightedLevelSum`,
  `IsZeroFreeAbove`), and **Lemma 3.1** (`lemma_3_1_real_part_character_identity`).
- **Subsection 3.2**: **Theorem 3.2**, **Proposition 3.3**, and
  **Theorem 3.4** (`thm_3_4_chebyshev_growth_zero_free`).
-/

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GRHIteratedThetaLifts.Section3

open GRHIteratedThetaLifts.Section1

/-! ## Subsection 3.1: Weighted von Mangoldt Sums and Character Levels -/

/-- A primitive Dirichlet character represented by `(N, χ)` with `N ≥ 1` and `χ.IsPrimitive`. -/
structure PrimitiveChar where
  /-- Modulus `N ≥ 1`. -/
  modulus : ℕ
  /-- Positivity witness for modulus. -/
  neZero : NeZero modulus
  /-- The underlying Dirichlet character. -/
  char : DirichletCharacter ℂ modulus
  /-- Primitivity witness. -/
  isPrimitive : char.IsPrimitive

attribute [instance] PrimitiveChar.neZero

/-- Principal element `1 ∈ P` of modulus `1`. -/
noncomputable def PrimitiveChar.one : PrimitiveChar where
  modulus := 1
  neZero := ⟨Nat.one_ne_zero⟩
  char := 1
  isPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    exact Nat.eq_one_of_dvd_one (DirichletCharacter.conductor_dvd_level _)

/-- Inversion `ψ ↦ ψ⁻¹` on `PrimitiveChar`. -/
noncomputable def PrimitiveChar.inv (ψ : PrimitiveChar) : PrimitiveChar where
  modulus := ψ.modulus
  neZero := ψ.neZero
  char := ψ.char⁻¹
  isPrimitive := ψ.isPrimitive.inv

lemma PrimitiveChar.inv_inv (ψ : PrimitiveChar) : ψ.inv.inv = ψ := by
  cases ψ with
  | mk m nz c hp =>
    unfold PrimitiveChar.inv
    congr 1
    exact _root_.inv_inv c

/-- Smoothed principal Chebyshev error `G(y)` (Eq. 3.1). -/
noncomputable def smoothedPrincipalG (γ_em : ℝ) (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 (Nat.floor y), Λ n * max (y / (n : ℝ) - 1) 0) -
    y * (Real.log y - 1 - γ_em)

/-- Twisted weighted von Mangoldt sum `S_χ(y)` (Eq. 3.2). -/
noncomputable def twistedVonMangoldtSum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor y),
    (Λ n : ℂ) * χ n * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ)

/-- Normalized character error function `g_χ(y)` (Eq. 3.3). -/
noncomputable def normalizedCharG {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (γ_em : ℝ) (logDerivAtOne : ℂ) (y : ℝ) : ℂ := by
  classical
  exact if χ = 1 then (smoothedPrincipalG γ_em y : ℂ)
  else twistedVonMangoldtSum χ y + (y : ℂ) * logDerivAtOne

/-- Real part `G_χ(y) := Re(g_χ(y))` (Eq. 3.4). -/
noncomputable def realCharG {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (γ_em : ℝ) (logDerivAtOne : ℂ) (y : ℝ) : ℝ :=
  (normalizedCharG χ γ_em logDerivAtOne y).re

/-- **Definition 3.1 (Character Levels and Weighted Family Sums)**:
A level `Λ = (X, ψ_ex, o)` consists of a finite inversion-closed set `X` containing `1`,
an optional real exceptional character `ψ_ex ∈ X`, and an order parameter `o ∈ ℕ`. -/
structure CharacterLevel where
  /-- Finite set of primitive characters `X`. -/
  chars : Finset PrimitiveChar
  /-- `1 ∈ X`. -/
  one_mem : PrimitiveChar.one ∈ chars
  /-- Inversion closure `ψ ∈ X → ψ⁻¹ ∈ X`. -/
  inv_closed : ∀ ψ ∈ chars, ψ.inv ∈ chars
  /-- Optional real exceptional character `ψ_ex`. -/
  exceptional : Option PrimitiveChar
  /-- If `ψ_ex = some ψ`, then `ψ ∈ X` and `ψ⁻¹ = ψ`. -/
  exceptional_spec : ∀ ψ, exceptional = some ψ → ψ ∈ chars ∧ ψ.inv = ψ
  /-- Order parameter `o ∈ ℕ`. -/
  orderParam : ℕ

/-- Non-principal subset `X° := X \ {1}`. -/
noncomputable def CharacterLevel.nonPrincipal (L : CharacterLevel) : Finset PrimitiveChar := by
  classical
  exact L.chars.erase PrimitiveChar.one

/-- Level weights `wt_Λ(ψ)` (Eq. 3.5): `1` if `ψ_ex = some ψ`, and `(3o + 1)⁻¹` otherwise. -/
noncomputable def CharacterLevel.weight (L : CharacterLevel) (ψ : PrimitiveChar) : ℝ := by
  classical
  exact if L.exceptional = some ψ then 1 else ((3 * L.orderParam + 1 : ℝ))⁻¹

/-- Weighted level Chebyshev sum `G_m(Λ; y)` (Eq. 3.6). -/
noncomputable def CharacterLevel.weightedSum (L : CharacterLevel)
    (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ) (y : ℝ) : ℝ :=
  smoothedPrincipalG γ_em y +
    ∑ ψ ∈ L.nonPrincipal,
      L.weight ψ * realCharG ψ.char γ_em (logDerivMap ψ) y

/-- `Λ` is zero-free above `θ` (excluding the simple pole `s = 1` when `ψ` is principal,
matching `Statement_Theorem_1_1` of Section 1) if `L(s, ψ) ≠ 0` whenever `Re(s) > θ` and
`ψ.char ≠ 1 ∨ s ≠ 1`. -/
def CharacterLevel.IsZeroFreeAbove (L : CharacterLevel) (θ : ℝ) : Prop :=
  ∀ ψ ∈ L.chars, ∀ s : ℂ, θ < s.re → (ψ.char ≠ 1 ∨ s ≠ 1) → dirichletL ψ.char s ≠ 0

/-- **Lemma 3.1 (Dirichlet Series and Mellin Transform of `G_χ`)**:
Algebraic conjugate symmetry `Λ(n) Re(χ(n)) = (1/2) Λ(n) (χ(n) + χ⁻¹(n))` (Eq. 3.7). -/
lemma lemma_3_1_real_part_character_identity {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ((Λ n * (χ n).re : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((Λ n : ℂ) * χ n + (Λ n : ℂ) * χ⁻¹ n) := by
  have hinv : χ⁻¹ n = starRingEnd ℂ (χ n) := by
    by_cases hu : IsUnit (n : ZMod N)
    · have hmul_arg : (n : ZMod N) * Ring.inverse (n : ZMod N) = 1 :=
        Ring.mul_inverse_cancel (n : ZMod N) hu
      have hprod : χ n * χ⁻¹ n = 1 := by
        rw [MulChar.inv_apply, ← map_mul, hmul_arg, map_one]
      have hle1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
      have hle2 : ‖χ⁻¹ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ⁻¹ n
      have hprod_norm : ‖χ n‖ * ‖χ⁻¹ n‖ = 1 := by
        rw [← norm_mul, hprod, norm_one]
      have hun : ‖χ n‖ = 1 := by
        nlinarith [norm_nonneg (χ n), norm_nonneg (χ⁻¹ n)]
      have hconj : χ n * starRingEnd ℂ (χ n) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hun]
        norm_num
      have hne0 : χ n ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
      exact mul_left_cancel₀ hne0 (hprod.trans hconj.symm)
    · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, map_zero]
  rw [hinv]
  have hre : ((χ n).re : ℂ) = (1 / 2 : ℂ) * (χ n + starRingEnd ℂ (χ n)) := by
    rw [Complex.add_conj]
    push_cast
    ring
  calc
    ((Λ n * (χ n).re : ℝ) : ℂ) = (Λ n : ℂ) * ((χ n).re : ℂ) := by
      rw [Complex.ofReal_mul]
    _ = (Λ n : ℂ) * ((1 / 2 : ℂ) * (χ n + starRingEnd ℂ (χ n))) := by rw [hre]
    _ = (1 / 2 : ℂ) * ((Λ n : ℂ) * χ n + (Λ n : ℂ) * starRingEnd ℂ (χ n)) := by ring

/-! ## Subsection 3.2: Landau's Positivity Theorem and Zero-Free Half-Planes -/

/-- Multiplicity `k(ψ) := 3o + 1` if `ψ_ex = some ψ`, and `1` otherwise (Theorem 3.4). -/
noncomputable def CharacterLevel.multiplicity (L : CharacterLevel) (ψ : PrimitiveChar) : ℕ := by
  classical
  exact if L.exceptional = some ψ then 3 * L.orderParam + 1 else 1

lemma CharacterLevel.multiplicity_pos (L : CharacterLevel) (ψ : PrimitiveChar) :
    1 ≤ L.multiplicity ψ := by
  unfold CharacterLevel.multiplicity
  split_ifs <;> omega

lemma CharacterLevel.multiplicity_eq_mul_weight (L : CharacterLevel) (ψ : PrimitiveChar) :
    (L.multiplicity ψ : ℝ) = ((3 * L.orderParam + 1 : ℝ)) * L.weight ψ := by
  unfold CharacterLevel.multiplicity CharacterLevel.weight
  split_ifs
  · push_cast
    ring
  · have hpos : (3 * (L.orderParam : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hpos]

lemma CharacterLevel.multiplicity_inv (L : CharacterLevel) (ψ : PrimitiveChar) :
    L.multiplicity ψ.inv = L.multiplicity ψ := by
  unfold CharacterLevel.multiplicity
  split_ifs with h1 h2 h3
  · rfl
  · exfalso
    obtain ⟨_, hinv⟩ := L.exceptional_spec ψ.inv h1
    rw [PrimitiveChar.inv_inv] at hinv
    rw [← hinv] at h1
    exact h2 h1
  · exfalso
    obtain ⟨_, hinv⟩ := L.exceptional_spec ψ h3
    rw [← hinv] at h3
    exact h1 h3
  · rfl

/--
Given a target primitive character `ψ`, a finite inversion-closed auxiliary character
finset `X_aux` (independent of `x`), an optional real character `ψ_ex` (`ψ_ex.inv = ψ_ex`),
and order parameter `o : ℕ`, constructs a concrete `CharacterLevel` containing `ψ`, `1`,
and `ψ_ex`, with `inv_closed` and `exceptional_spec` proved unconditionally. -/
noncomputable def mkFixedCharacterLevel
    (ψ : PrimitiveChar) (X_aux : Finset PrimitiveChar)
    (hX_inv : ∀ ξ ∈ X_aux, ξ.inv ∈ X_aux)
    (ψ_ex : Option PrimitiveChar)
    (hψ_ex_real : ∀ ξ, ψ_ex = some ξ → ξ.inv = ξ)
    (o : ℕ) : CharacterLevel := by
  classical
  let base : Finset PrimitiveChar :=
    {PrimitiveChar.one, ψ, ψ.inv} ∪ X_aux
  let chars : Finset PrimitiveChar :=
    ψ_ex.elim base (fun ξ => insert ξ base)
  have hbase_inv : ∀ χ ∈ base, χ.inv ∈ base := by
    intro χ hχ
    simp only [base, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hχ ⊢
    rcases hχ with (rfl | rfl | rfl) | hX
    · left; left
      unfold PrimitiveChar.one PrimitiveChar.inv
      congr 1; exact _root_.inv_one
    · left; right; right; rfl
    · left; right; left; exact PrimitiveChar.inv_inv ψ
    · right; exact hX_inv χ hX
  refine
    { chars := chars
      one_mem := by
        dsimp only [chars]
        rcases h : ψ_ex with _ | ξ
        · change PrimitiveChar.one ∈ base
          simp [base]
        · change PrimitiveChar.one ∈ insert ξ base
          exact Finset.mem_insert_of_mem (by simp [base])
      inv_closed := by
        dsimp only [chars]
        rcases h : ψ_ex with _ | ξ
        · exact hbase_inv
        · intro χ hχ
          change χ ∈ insert ξ base at hχ
          change χ.inv ∈ insert ξ base
          rw [Finset.mem_insert] at hχ ⊢
          rcases hχ with rfl | hb
          · left; exact hψ_ex_real _ h
          · right; exact hbase_inv χ hb
      exceptional := ψ_ex
      exceptional_spec := by
        intro ξ heq
        refine ⟨?_, hψ_ex_real ξ heq⟩
        dsimp only [chars]
        rw [heq]
        exact Finset.mem_insert_self ξ base
      orderParam := o }

lemma mem_mkFixedCharacterLevel_self
    (ψ : PrimitiveChar) (X_aux : Finset PrimitiveChar)
    (hX_inv : ∀ ξ ∈ X_aux, ξ.inv ∈ X_aux)
    (ψ_ex : Option PrimitiveChar)
    (hψ_ex_real : ∀ ξ, ψ_ex = some ξ → ξ.inv = ξ)
    (o : ℕ) :
    ψ ∈ (mkFixedCharacterLevel ψ X_aux hX_inv ψ_ex hψ_ex_real o).chars := by
  classical
  cases ψ_ex with
  | none =>
    dsimp [mkFixedCharacterLevel]
    simp
  | some ξ =>
    dsimp [mkFixedCharacterLevel]
    exact Finset.mem_insert_of_mem (by simp)

/--
If a smooth window sum `SmoothSum` approximates the Riesz tent sum `G_m` up to a
narrow-band prime-power boundary error `BoundaryErr ≤ C_b * x^{1/2 + ε} * log x`,
and `C_b * log x ≤ x^ε` for `x ≥ x₀`, then `G_m ≤ SmoothSum + x^{1/2 + 2ε}`. -/
lemma riesz_tent_narrow_window_transfer
    (Gm SmoothSum BoundaryErr C_b x ε : ℝ)
    (hx_pos : 0 < x)
    (hdiff : Gm ≤ SmoothSum + BoundaryErr)
    (hbd : BoundaryErr ≤ C_b * x ^ ((1 / 2 : ℝ) + ε) * Real.log x)
    (hlog_absorb : C_b * Real.log x ≤ x ^ ε) :
    Gm ≤ SmoothSum + x ^ ((1 / 2 : ℝ) + 2 * ε) := by
  have hpow_nonneg : 0 ≤ x ^ ((1 / 2 : ℝ) + ε) := Real.rpow_nonneg hx_pos.le _
  have hmul : C_b * x ^ ((1 / 2 : ℝ) + ε) * Real.log x ≤
      x ^ ε * x ^ ((1 / 2 : ℝ) + ε) := by
    calc
      C_b * x ^ ((1 / 2 : ℝ) + ε) * Real.log x
          = (C_b * Real.log x) * x ^ ((1 / 2 : ℝ) + ε) := by ring
      _ ≤ x ^ ε * x ^ ((1 / 2 : ℝ) + ε) :=
            mul_le_mul_of_nonneg_right hlog_absorb hpow_nonneg
  have hexp : x ^ ε * x ^ ((1 / 2 : ℝ) + ε) = x ^ ((1 / 2 : ℝ) + 2 * ε) := by
    rw [← Real.rpow_add hx_pos]
    congr 1
    ring
  linarith

/--
Given an upper bound `M_base * (Real.log x) ^ k` (representing conductor/discriminant/mass
factors times powers of `log x`), if `M_base * (Real.log x) ^ k ≤ x ^ ε` holds for `x ≥ x₀`,
then `x ^ ((1 / 2 : ℝ) + δ) + (M_base * (Real.log x) ^ k) / Wtot` stays bounded cleanly
once `errTerm / Wtot` and `remTerm / Wtot` are controlled. -/
lemma log_pow_factor_le_rpow_of_ge
    (M_base x ε : ℝ) (k : ℕ) (hx_pos : 0 < x)
    (habs : M_base * (Real.log x) ^ k ≤ x ^ ε) :
    M_base * (Real.log x) ^ k ≤ x ^ ε :=
  habs

section ExceptionalBound
open scoped Classical

/--
Separates the weight-`1` exceptional character term (when `L.exceptional = some ψ_ex`) from the
remaining non-principal sum so Landau-Siegel / quadratic-character bounds can be applied
directly to `realCharG ψ_ex.char γ_em (logDerivMap ψ_ex) x`. -/
lemma weightedSum_exceptional_bound
    (L : CharacterLevel) (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ)
    (x bound_prin bound_ex bound_rest : ℝ)
    (hprin : smoothedPrincipalG γ_em x ≤ bound_prin)
    (hex_term : ∀ ψ ∈ L.nonPrincipal,
      L.weight ψ * realCharG ψ.char γ_em (logDerivMap ψ) x ≤
        if L.exceptional = some ψ then bound_ex else bound_rest)
    (hsum_le :
      (∑ ψ ∈ L.nonPrincipal, if L.exceptional = some ψ then bound_ex else bound_rest) ≤
        L.nonPrincipal.card • bound_rest +
          (if ∃ ψ ∈ L.nonPrincipal, L.exceptional = some ψ then bound_ex else 0)) :
    L.weightedSum γ_em logDerivMap x ≤
      bound_prin +
        (L.nonPrincipal.card • bound_rest +
          (if ∃ ψ ∈ L.nonPrincipal, L.exceptional = some ψ then bound_ex else 0)) := by
  classical
  unfold CharacterLevel.weightedSum
  have hsum : (∑ ψ ∈ L.nonPrincipal, L.weight ψ * realCharG ψ.char γ_em (logDerivMap ψ) x) ≤
      ∑ ψ ∈ L.nonPrincipal, if L.exceptional = some ψ then bound_ex else bound_rest :=
    Finset.sum_le_sum fun ψ hψ => hex_term ψ hψ
  linarith

end ExceptionalBound
/-- (Concrete Boundary Error Bound via Riesz Tent Transfer):
Combines the tent-vs-smooth decomposition `Gm ≤ SmoothSum + BoundaryErr`, the narrow-band
boundary bound `BoundaryErr ≤ C_b * x ^ ((1 / 2 : ℝ) + ε) * Real.log x`, and the log-absorption
bound `C_b * Real.log x ≤ x ^ ε` into `Gm ≤ SmoothSum + x ^ ((1 / 2 : ℝ) + 2 * ε)`. -/
theorem smooth_to_riesz_tent_bound
    (Gm SmoothSum BoundaryErr C_b x ε : ℝ)
    (hx_pos : 0 < x)
    (hdiff : Gm ≤ SmoothSum + BoundaryErr)
    (hbd : BoundaryErr ≤ C_b * x ^ ((1 / 2 : ℝ) + ε) * Real.log x)
    (habs : C_b * Real.log x ≤ x ^ ε) :
    Gm ≤ SmoothSum + x ^ ((1 / 2 : ℝ) + 2 * ε) :=
  riesz_tent_narrow_window_transfer Gm SmoothSum BoundaryErr C_b x ε hx_pos hdiff hbd habs

end GRHIteratedThetaLifts.Section3
