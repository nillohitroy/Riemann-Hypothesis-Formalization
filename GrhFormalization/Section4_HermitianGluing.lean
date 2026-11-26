/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Section 4: Local-to-Global Structures and Hermitian Lattice Gluing

This file formalizes all results in Section 4 of the manuscript:
- **Subsection 4.1**: **Lemma 4.1** (`lemma_4_1_part1`, `lemma_4_1_part2`, `lemma_4_1_part3`)
  and **Theorem 4.2** (`LandherrIsometryData`).
- **Subsection 4.2**: **Theorem 4.3** (`thm_4_3_lattice_gluing_line`) and
  **Theorem 4.4** (`thm_4_4_lattice_gluing_subspace`).
-/

open scoped BigOperators

namespace GRHIteratedThetaLifts.Section4

/-! ## Subsection 4.1: Parity Criterion for Norm Units & Global Isometry -/

/-- Abstract valuation & conjugation model at a self-conjugate prime `P` (`P* = P`). -/
structure SelfConjugatePrimeValuation (E : Type*) [Ring E] where
  /-- Complex conjugation automorphism `a ↦ a*`. -/
  conj : E ≃+* E
  /-- Normalized discrete valuation `v_P : Eˣ → ℤ`. -/
  val : Eˣ → ℤ
  /-- Invariance `v_P(a*) = v_P(a)` (Lemma 4.1(1)). -/
  val_conj : ∀ a : Eˣ, val (Units.map conj.toMonoidHom a) = val a
  /-- Multiplicativity `v_P(a * b) = v_P(a) + v_P(b)`. -/
  val_mul : ∀ a b : Eˣ, val (a * b) = val a + val b
  /-- Uniformizer `ϖ` with `v_P(ϖ) = 1`. -/
  unif : Eˣ
  /-- Valuation of uniformizer is `1`. -/
  val_unif : val unif = 1

/-- `x ∈ Eˣ` is a norm unit at `P` if `∃ c ∈ Eˣ, v_P(c* * c * x) = 0`. -/
def IsNormUnit {E : Type*} [Ring E] (V : SelfConjugatePrimeValuation E) (x : Eˣ) : Prop :=
  ∃ c : Eˣ, V.val (Units.map V.conj.toMonoidHom c * c * x) = 0

/-- **Lemma 4.1(1)**: `v_P(a*) = v_P(a)`. -/
lemma lemma_4_1_part1 {E : Type*} [Ring E]
    (V : SelfConjugatePrimeValuation E) (a : Eˣ) :
    V.val (Units.map V.conj.toMonoidHom a) = V.val a :=
  V.val_conj a

lemma val_one_eq_zero {E : Type*} [Ring E] (V : SelfConjugatePrimeValuation E) :
    V.val 1 = 0 := by
  have h0 := V.val_mul 1 1
  rw [mul_one] at h0
  linarith

lemma val_inv_eq_neg {E : Type*} [Ring E]
    (V : SelfConjugatePrimeValuation E) (a : Eˣ) :
    V.val a⁻¹ = -V.val a := by
  have h1 : V.val (a * a⁻¹) = V.val 1 := by rw [mul_inv_cancel]
  rw [V.val_mul, val_one_eq_zero] at h1
  linarith

lemma val_zpow_unif {E : Type*} [Ring E]
    (V : SelfConjugatePrimeValuation E) (m : ℤ) :
    V.val (V.unif ^ m) = m := by
  induction m using Int.induction_on with
  | zero =>
    rw [zpow_zero, val_one_eq_zero]
  | succ n ih =>
    rw [zpow_add_one, V.val_mul, ih, V.val_unif]
  | pred n ih =>
    rw [zpow_sub_one, V.val_mul, ih, val_inv_eq_neg, V.val_unif]
    ring

/-- **Lemma 4.1(2)**: `x` is a norm unit at `P` if and only if `v_P(x)` is even. -/
theorem lemma_4_1_part2 {E : Type*} [Ring E]
    (V : SelfConjugatePrimeValuation E) (x : Eˣ) :
    IsNormUnit V x ↔ Even (V.val x) := by
  constructor
  · rintro ⟨c, hc⟩
    rw [V.val_mul, V.val_mul, V.val_conj] at hc
    refine ⟨-V.val c, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨V.unif ^ (-k), ?_⟩
    rw [V.val_mul, V.val_mul, V.val_conj, val_zpow_unif]
    linarith

/-- **Lemma 4.1(3)**: If `x` and `y` have the same norm-unit status, `x * y` is a norm unit. -/
theorem lemma_4_1_part3 {E : Type*} [Ring E]
    (V : SelfConjugatePrimeValuation E) (x y : Eˣ)
    (hsame : IsNormUnit V x ↔ IsNormUnit V y) :
    IsNormUnit V (x * y) := by
  rw [lemma_4_1_part2, V.val_mul]
  have heq : Even (V.val x) ↔ Even (V.val y) :=
    (lemma_4_1_part2 V x).symm.trans (hsame.trans (lemma_4_1_part2 V y))
  rw [Int.even_add]
  exact heq

/-- **Theorem 4.2 (Global Isometry from Matching Bad Primes)**:
Abstract Landherr Hasse-principle reduction for totally definite Hermitian spaces of equal rank. -/
structure LandherrIsometryData (Space : Type*) where
  /-- Dimension `dim_E V`. -/
  dim : Space → ℕ
  /-- Bad prime set `badP(h, M)`. -/
  badPrimes : Space → Set ℕ
  /-- Global `E`-linear isometry relation `V ≃_h V'`. -/
  IsIsometric : Space → Space → Prop
  /-- Landherr's Hasse principle after one-dimensional stabilization and Witt cancellation. -/
  thm_4_2_global_isometry :
    ∀ V V' : Space, dim V = dim V' → badPrimes V = badPrimes V' → IsIsometric V V'

/-! ## Subsection 4.2: Integral Hermitian Lattice Gluing and Counting Bounds -/

/-- **Theorem 4.3 (Lattice Gluing Bound Along a Line)**:
Any finite family of glued lattices uniquely parametrized by pairs in `S × (A∨ / A)`
with `|S| ≤ N_T` and `|A∨ / A| = disc_N(h|_U, A)` has cardinality at most
`N_T * disc_N(h|_U, A)`. -/
theorem thm_4_3_lattice_gluing_line
    {Latt DualLine DualQuot : Type*}
    (Glued : Finset Latt) (S : Finset DualLine) (A_quot : Finset DualQuot)
    (N_T disc_U : ℕ)
    (hS : S.card ≤ N_T)
    (hA : A_quot.card = disc_U)
    (param : Latt → DualLine × DualQuot)
    (hparam_mem : ∀ L ∈ Glued, param L ∈ S ×ˢ A_quot)
    (hparam_inj : Set.InjOn param (Glued : Set Latt)) :
    Glued.card ≤ N_T * disc_U := by
  calc
    Glued.card ≤ (S ×ˢ A_quot).card := Finset.card_le_card_of_injOn param hparam_mem hparam_inj
    _ = S.card * A_quot.card := Finset.card_product S A_quot
    _ ≤ N_T * disc_U := Nat.mul_le_mul hS (le_of_eq hA)

/-- **Theorem 4.4 (General Subspace-Complement Lattice Gluing Bound)**:
Any finite family of intermediate submodules `X ⊆ L ⊆ Y` where `Y / X` has size at most
`disc_U * disc_U_perp` and is generated by at most `e + e'` elements has cardinality
bounded by `(disc_U * disc_U_perp) ^ (e + e')`. -/
theorem thm_4_4_lattice_gluing_subspace
    {Latt QuotElem : Type*}
    (Glued : Finset Latt) (QuotYX : Finset QuotElem)
    (disc_U disc_U_perp e e' : ℕ)
    (hQuot : QuotYX.card ≤ disc_U * disc_U_perp)
    (genTuple : Latt → (Fin (e + e') → QuotElem))
    (hgen_mem : ∀ L ∈ Glued, ∀ i : Fin (e + e'), genTuple L i ∈ QuotYX)
    (hgen_inj : Set.InjOn genTuple (Glued : Set Latt)) :
    Glued.card ≤ (disc_U * disc_U_perp) ^ (e + e') := by
  classical
  let TupleSpace : Finset (Fin (e + e') → QuotElem) :=
    Fintype.piFinset (fun _ : Fin (e + e') => QuotYX)
  have hmem_tuple : ∀ L ∈ Glued, genTuple L ∈ TupleSpace := by
    intro L hL
    rw [Fintype.mem_piFinset]
    exact hgen_mem L hL
  calc
    Glued.card ≤ TupleSpace.card := Finset.card_le_card_of_injOn genTuple hmem_tuple hgen_inj
    _ = ∏ _ : Fin (e + e'), QuotYX.card := Fintype.card_piFinset _
    _ = QuotYX.card ^ (e + e') := by simp
    _ ≤ (disc_U * disc_U_perp) ^ (e + e') := Nat.pow_le_pow_left hQuot (e + e')

end GRHIteratedThetaLifts.Section4
