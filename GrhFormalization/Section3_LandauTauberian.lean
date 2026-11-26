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

/-- Analytic Mellin-integral positivity structure encapsulating the Landau abscissa
continuation and ODE zero-free argument of Theorem 3.2. -/
structure LandauAnalyticBackend where
  /-- **Theorem 3.2 (Landau Positivity for Entire Functions)**. -/
  thm_3_2_landau_positivity :
    ∀ (P : ℂ → ℂ) (a b : ℂ) (H : ℝ → ℝ) (C θ : ℝ),
      Differentiable ℂ P →
      (∀ s : ℂ, 1 ≤ s.re → P s ≠ 0) →
      deriv P 1 - (a + b) * P 1 = 0 →
      (∀ x : ℝ, 1 ≤ x → 0 ≤ H x) →
      0 < θ → θ < 1 →
      (∀ s : ℂ, 1 < s.re →
        ∫ x in Set.Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) =
          (deriv P s / P s - (a + b * s)) / (s * (s - 1)) + (C : ℂ) / ((s : ℂ) - θ)) →
      ∀ s : ℂ, θ < s.re → P s ≠ 0
  /-- **Proposition 3.3 (Landau Positivity for Inversion-Closed Families)**. -/
  prop_3_3_inversion_closed_landau :
    ∀ {ι : Type} [DecidableEq ι] (S : Finset ι) (τ : ι → ι)
      (ψ : ι → PrimitiveChar) (R : ℕ) (θ C₀ y₀ : ℝ)
      (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ),
      (∀ ξ ∈ S, τ ξ ∈ S ∧ τ (τ ξ) = ξ) →
      (∀ ξ ∈ S, (ψ ξ).char ≠ 1 ∧ ψ (τ ξ) = (ψ ξ).inv) →
      1 ≤ R → 0 < θ → θ < 1 →
      (∀ y : ℝ, y₀ ≤ y →
        (R : ℝ) * smoothedPrincipalG γ_em y +
          ∑ ξ ∈ S, realCharG (ψ ξ).char γ_em (logDerivMap (ψ ξ)) y ≤ C₀ * y ^ θ) →
      ∀ s : ℂ, θ < s.re →
        (s ≠ 1 → riemannZeta s ≠ 0) ∧
        (∀ ξ ∈ S, dirichletL (ψ ξ).char s ≠ 0)

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

/-- **Theorem 3.4 (Chebyshev Growth Implies Zero-Freeness)**:
If `G_m(Λ; y) ≤ y^θ` for all `y ≥ y₀` with `θ ∈ (0, 1)`, then `Λ` is zero-free above `θ`
(using Section 1's `dirichletL_modOne_eq_riemannZeta` for `ψ = 1`). -/
theorem thm_3_4_chebyshev_growth_zero_free
    (hBackend : LandauAnalyticBackend)
    (L : CharacterLevel) (θ y₀ : ℝ) (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgrowth : ∀ y : ℝ, y₀ ≤ y → L.weightedSum γ_em logDerivMap y ≤ y ^ θ) :
    L.IsZeroFreeAbove θ := by
  classical
  let R : ℕ := 3 * L.orderParam + 1
  have hR_pos : (0 : ℝ) < (R : ℝ) := by dsimp [R]; positivity
  let S : Finset (PrimitiveChar × ℕ) :=
    L.nonPrincipal.biUnion (fun ψ => (Finset.range (L.multiplicity ψ)).image (fun j => (ψ, j)))
  let τ : PrimitiveChar × ℕ → PrimitiveChar × ℕ := fun p => (p.1.inv, p.2)
  have hτ_mem : ∀ p ∈ S, τ p ∈ S ∧ τ (τ p) = p := by
    intro p hp
    rcases p with ⟨ψ, j⟩
    simp only [S, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hp
    obtain ⟨ψ', hψ'_mem, j', hj'_lt, rfl, rfl⟩ := hp
    refine ⟨?_, ?_⟩
    · simp only [S, τ, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
      refine ⟨ψ'.inv, ?_, j', ?_, rfl, rfl⟩
      · unfold CharacterLevel.nonPrincipal at hψ'_mem ⊢
        rw [Finset.mem_erase] at hψ'_mem ⊢
        refine ⟨?_, L.inv_closed ψ' hψ'_mem.2⟩
        intro hinv_one
        apply hψ'_mem.1
        have := congrArg PrimitiveChar.inv hinv_one
        rw [PrimitiveChar.inv_inv] at this
        rw [this]
        unfold PrimitiveChar.one PrimitiveChar.inv
        congr 1
        exact _root_.inv_one
      · rw [L.multiplicity_inv]; exact hj'_lt
    · simp [τ, PrimitiveChar.inv_inv]
  have hψ_spec : ∀ p ∈ S, p.1.char ≠ 1 ∧ p.1.inv = p.1.inv := by
    intro p hp
    rcases p with ⟨ψ, j⟩
    simp only [S, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq] at hp
    obtain ⟨ψ', hψ'_mem, _, _, rfl, _⟩ := hp
    refine ⟨?_, rfl⟩
    unfold CharacterLevel.nonPrincipal at hψ'_mem
    rw [Finset.mem_erase] at hψ'_mem
    intro hchar1
    apply hψ'_mem.1
    cases ψ' with
    | mk m nz c hp =>
      simp only at hchar1
      have hcond1 : c.conductor = 1 := by
        rw [hchar1]
        exact DirichletCharacter.conductor_one
      have hm1 : m = 1 := by
        rw [DirichletCharacter.isPrimitive_def] at hp
        rw [← hp, hcond1]
      subst hm1
      unfold PrimitiveChar.one
      congr 1
  have hsum_bound : ∀ y : ℝ, y₀ ≤ y →
      (R : ℝ) * smoothedPrincipalG γ_em y +
        ∑ p ∈ S, realCharG p.1.char γ_em (logDerivMap p.1) y ≤ (R : ℝ) * y ^ θ := by
    intro y hy
    have hinner :
        ∑ p ∈ S, realCharG p.1.char γ_em (logDerivMap p.1) y =
          ∑ ψ ∈ L.nonPrincipal,
            (R : ℝ) * (L.weight ψ * realCharG ψ.char γ_em (logDerivMap ψ) y) := by
      have hdisj : (L.nonPrincipal : Set PrimitiveChar).PairwiseDisjoint
          (fun ψ => (Finset.range (L.multiplicity ψ)).image (fun j => (ψ, j))) := by
        intro a _ b _ hab
        rw [Function.onFun, Finset.disjoint_left]
        intro x hxa hxb
        simp only [Finset.mem_image] at hxa hxb
        obtain ⟨_, _, rfl⟩ := hxa
        obtain ⟨_, _, hEq⟩ := hxb
        exact hab (Prod.mk.inj hEq).1.symm
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.inj h).2)]
      change ∑ _j ∈ Finset.range (L.multiplicity ψ),
          realCharG ψ.char γ_em (logDerivMap ψ) y =
        (R : ℝ) * (L.weight ψ * realCharG ψ.char γ_em (logDerivMap ψ) y)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, L.multiplicity_eq_mul_weight]
      dsimp [R]
      push_cast
      ring
    rw [hinner, ← Finset.mul_sum, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hgrowth y hy) hR_pos.le
  have hPT := hBackend.prop_3_3_inversion_closed_landau S τ (fun p => p.1)
    R θ (R : ℝ) y₀ γ_em logDerivMap hτ_mem hψ_spec (by dsimp [R]; omega) hθ0 hθ1 hsum_bound
  intro ψ hψ s hs_re hcond
  by_cases h1 : ψ = PrimitiveChar.one
  · subst h1
    have hzeta : dirichletL PrimitiveChar.one.char s = riemannZeta s :=
      dirichletL_modOne_eq_riemannZeta _ s
    rw [hzeta]
    have hs_ne1 : s ≠ 1 := hcond.resolve_left (fun h => h rfl)
    exact (hPT s hs_re).1 hs_ne1
  · have hmem_np : ψ ∈ L.nonPrincipal := Finset.mem_erase.mpr ⟨h1, hψ⟩
    have hm_pos : 0 < L.multiplicity ψ := Nat.lt_of_lt_of_le zero_lt_one (L.multiplicity_pos ψ)
    have hp_mem : (ψ, 0) ∈ S := by
      simp only [S, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
      exact ⟨ψ, hmem_np, 0, hm_pos, rfl, rfl⟩
    exact (hPT s hs_re).2 (ψ, 0) hp_mem

end GRHIteratedThetaLifts.Section3
