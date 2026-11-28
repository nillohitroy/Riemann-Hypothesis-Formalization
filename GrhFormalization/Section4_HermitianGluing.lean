/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Parity
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

universe uE uS uP

/-! ## Subsection 4.1: Parity Criterion for Norm Units & Global Isometry -/

/-- Abstract valuation & conjugation model at a self-conjugate prime `P` (`P* = P`). -/
structure SelfConjugatePrimeValuation (E : Type uE) [Ring E] where
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
def IsNormUnit {E : Type uE} [Ring E] (V : SelfConjugatePrimeValuation.{uE} E) (x : Eˣ) : Prop :=
  ∃ c : Eˣ, V.val (Units.map V.conj.toMonoidHom c * c * x) = 0

/-- **Lemma 4.1(1)**: `v_P(a*) = v_P(a)`. -/
lemma lemma_4_1_part1 {E : Type uE} [Ring E]
    (V : SelfConjugatePrimeValuation.{uE} E) (a : Eˣ) :
    V.val (Units.map V.conj.toMonoidHom a) = V.val a :=
  V.val_conj a

lemma val_one_eq_zero {E : Type uE} [Ring E] (V : SelfConjugatePrimeValuation.{uE} E) :
    V.val 1 = 0 := by
  have h0 := V.val_mul 1 1
  rw [mul_one] at h0
  linarith

lemma val_inv_eq_neg {E : Type uE} [Ring E]
    (V : SelfConjugatePrimeValuation.{uE} E) (a : Eˣ) :
    V.val a⁻¹ = -V.val a := by
  have h1 : V.val (a * a⁻¹) = V.val 1 := by rw [mul_inv_cancel]
  rw [V.val_mul, val_one_eq_zero] at h1
  linarith

lemma val_zpow_unif {E : Type uE} [Ring E]
    (V : SelfConjugatePrimeValuation.{uE} E) (m : ℤ) :
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
theorem lemma_4_1_part2 {E : Type uE} [Ring E]
    (V : SelfConjugatePrimeValuation.{uE} E) (x : Eˣ) :
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
theorem lemma_4_1_part3 {E : Type uE} [Ring E]
    (V : SelfConjugatePrimeValuation.{uE} E) (x y : Eˣ)
    (hsame : IsNormUnit V x ↔ IsNormUnit V y) :
    IsNormUnit V (x * y) := by
  rw [lemma_4_1_part2, V.val_mul]
  have heq : Even (V.val x) ↔ Even (V.val y) :=
    (lemma_4_1_part2 V x).symm.trans (hsame.trans (lemma_4_1_part2 V y))
  rw [Int.even_add]
  exact heq

/-- **Theorem 4.2 (Global Isometry from Matching Bad Primes — Stabilization & Witt Cancellation)**:
Explicitly universe-polymorphic over `(E : Type uE)`, `(Space : Type uS)`, and `(PrimeIdx : Type uP)`
so `PrimeIdx` unifies cleanly with `IsDedekindDomain.HeightOneSpectrum (𝓞 K)` in any universe. -/
structure HermitianCMSystem (E : Type uE) [CommRing E] (Space : Type uS) where
  /-- Rank `dim_K V`. -/
  dim : Space → ℕ
  /-- Gram determinant `β(V) ∈ Eˣ` in an orthogonal `K`-basis. -/
  gramDet : Space → Eˣ
  /-- Self-conjugate maximal ideals `P* = P` indexed by `PrimeIdx : Type uP`. -/
  PrimeIdx : Type uP
  /-- Normalized valuation at each self-conjugate prime. -/
  valAt : PrimeIdx → SelfConjugatePrimeValuation.{uE} E
  /-- Bad primes `badP(h, M)`: self-conjugate primes where `gramDet` is not a norm unit. -/
  badPrimes : Space → Set PrimeIdx
  /-- Gram-determinant characterization of `badP(h, M)`. -/
  mem_badPrimes_iff : ∀ (X : Space) (P : PrimeIdx),
    P ∈ badPrimes X ↔ ¬ IsNormUnit (valAt P) (gramDet X)
  /-- Global `K`-linear isometry `V ≃_h V'`. -/
  IsIsometric : Space → Space → Prop
  /-- Orthogonal stabilization `(V ⊕ K, h ⊥ ⟨β⟩)`. -/
  stabilize : Space → Eˣ → Space
  /-- Stabilization increments rank by `1`. -/
  dim_stabilize : ∀ (X : Space) (β : Eˣ), dim (stabilize X β) = dim X + 1
  /-- Stabilization multiplies Gram determinant by `β`. -/
  gramDet_stabilize : ∀ (X : Space) (β : Eˣ), gramDet (stabilize X β) = gramDet X * β
  /-- Landherr Hasse principle: totally definite spaces of equal rank with empty bad-prime set
  (unimodular at all self-conjugate primes) are globally isometric. -/
  landherr_unimodular_isometry :
    ∀ W W' : Space, dim W = dim W' → badPrimes W = ∅ → badPrimes W' = ∅ → IsIsometric W W'
  /-- Witt cancellation along a common orthogonal line `⟨β⟩`. -/
  witt_cancel :
    ∀ (X X' : Space) (β : Eˣ), IsIsometric (stabilize X β) (stabilize X' β) → IsIsometric X X'

/-- **Theorem 4.2 (Unconditional Deduction from Lemma 4.1, Stabilization, Landherr & Witt)**:
If `(V, h)` and `(V', h')` have `dim V = dim V'` and `badP(h, M) = badP(h', M')`, then
`(V, h) ≃ (V', h')`. -/
theorem thm_4_2_global_isometry_of_same_bad_primes
    {E : Type uE} [CommRing E] {Space : Type uS}
    (H : HermitianCMSystem.{uE, uS, uP} E Space) (V V' : Space)
    (hdim : H.dim V = H.dim V')
    (hbad : H.badPrimes V = H.badPrimes V') :
    H.IsIsometric V V' := by
  let β : Eˣ := H.gramDet V
  have hbad_stab1 : H.badPrimes (H.stabilize V β) = ∅ := by
    ext P
    simp only [Set.mem_empty_iff_false, iff_false]
    rw [H.mem_badPrimes_iff, H.gramDet_stabilize]
    intro hnot
    apply hnot
    exact lemma_4_1_part3 (H.valAt P) (H.gramDet V) β Iff.rfl
  have hbad_stab2 : H.badPrimes (H.stabilize V' β) = ∅ := by
    ext P
    simp only [Set.mem_empty_iff_false, iff_false]
    rw [H.mem_badPrimes_iff, H.gramDet_stabilize]
    intro hnot
    apply hnot
    refine lemma_4_1_part3 (H.valAt P) (H.gramDet V') β ?_
    have hP_iff : P ∈ H.badPrimes V' ↔ P ∈ H.badPrimes V := by rw [hbad]
    rw [H.mem_badPrimes_iff, H.mem_badPrimes_iff] at hP_iff
    exact not_iff_not.mp hP_iff
  have hdim_stab : H.dim (H.stabilize V β) = H.dim (H.stabilize V' β) := by
    rw [H.dim_stabilize, H.dim_stabilize, hdim]
  have hiso_stab : H.IsIsometric (H.stabilize V β) (H.stabilize V' β) :=
    H.landherr_unimodular_isometry _ _ hdim_stab hbad_stab1 hbad_stab2
  exact H.witt_cancel V V' β hiso_stab

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

/--
If an `E`-linear isometry `Φ : V × E →ₗ[E] V' × E` between stabilized Hermitian spaces
`(V × E, h ⊥ ⟨β⟩)` and `(V' × E, h' ⊥ ⟨β⟩)` maps `(0, 1) ↦ (0, 1)`, then its first-coordinate
restriction `x ↦ (Φ (x, 0)).1` is an `E`-linear isometry `(V, h) →ₗ[E] (V', h')`. -/
theorem concrete_witt_cancellation
    {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
    (conj : E ≃+* E)
    (h : V → V → E) (h' : V' → V' → E)
    (β : E) (hβ : β ≠ 0)
    (Φ : (V × E) →ₗ[E] (V' × E))
    (hΦ_iso : ∀ u w : V × E,
      h' (Φ u).1 (Φ w).1 + β * conj (Φ u).2 * (Φ w).2 =
      h u.1 w.1 + β * conj u.2 * w.2)
    (hΦ_fix : Φ (0, 1) = (0, 1))
    (hh_zero_right : ∀ x : V, h x 0 = 0)
    (hh'_zero_right : ∀ y : V', h' y 0 = 0) :
    ∃ f : V →ₗ[E] V', ∀ x y : V, h' (f x) (f y) = h x y := by
  have hcomp_zero : ∀ x : V, (Φ (x, 0)).2 = 0 := by
    intro x
    have horth := hΦ_iso (x, 0) (0, 1)
    rw [hΦ_fix, hh'_zero_right, hh_zero_right] at horth
    simp only [map_zero, zero_mul, mul_one, zero_add] at horth
    have hconj0 : conj (Φ (x, 0)).2 = 0 := mul_left_cancel₀ hβ horth
    exact conj.injective (hconj0.trans (map_zero conj).symm)
  refine ⟨{ toFun := fun x => (Φ (x, 0)).1
            map_add' := fun x y => by
              have : (x + y, (0 : E)) = (x, 0) + (y, 0) := by simp
              rw [this, map_add, Prod.fst_add]
            map_smul' := fun c x => by
              have : (c • x, (0 : E)) = c • (x, 0) := by simp
              rw [this, map_smul, Prod.smul_fst, RingHom.id_apply] }, ?_⟩
  intro x y
  have hiso := hΦ_iso (x, 0) (y, 0)
  rw [hcomp_zero x, hcomp_zero y] at hiso
  simpa using hiso

/--
If every glued lattice `L ∈ Glued` is recovered from `param L ∈ S ×ˢ A_quot` via
`reconstruct (param L) = L`, injectivity holds automatically and `Glued.card ≤ N_T * disc_U`. -/
theorem thm_4_3_lattice_gluing_of_reconstruct
    {Latt DualLine DualQuot : Type*}
    (Glued : Finset Latt) (S : Finset DualLine) (A_quot : Finset DualQuot)
    (N_T disc_U : ℕ)
    (hS : S.card ≤ N_T) (hA : A_quot.card = disc_U)
    (param : Latt → DualLine × DualQuot)
    (reconstruct : DualLine × DualQuot → Latt)
    (hparam_mem : ∀ L ∈ Glued, param L ∈ S ×ˢ A_quot)
    (hreconstruct : ∀ L ∈ Glued, reconstruct (param L) = L) :
    Glued.card ≤ N_T * disc_U :=
  thm_4_3_lattice_gluing_line Glued S A_quot N_T disc_U hS hA param hparam_mem
    (fun L₁ h₁ L₂ h₂ hEq => by rw [← hreconstruct L₁ h₁, ← hreconstruct L₂ h₂, hEq])

/-- **Item 9B (Concrete Generator-Tuple Span Parametrization for Theorem 4.4)**:
If every intermediate lattice `L ∈ Glued` is spanned over `X` by an `(e + e')`-tuple of
coset representatives `genTuple L : Fin (e + e') → QuotYX` via `spanCosets (genTuple L) = L`,
then `Glued.card ≤ (disc_U * disc_U_perp) ^ (e + e')`. -/
theorem thm_4_4_lattice_gluing_of_span
    {Latt QuotElem : Type*}
    (Glued : Finset Latt) (QuotYX : Finset QuotElem)
    (disc_U disc_U_perp e e' : ℕ)
    (hQuot : QuotYX.card ≤ disc_U * disc_U_perp)
    (genTuple : Latt → (Fin (e + e') → QuotElem))
    (spanCosets : (Fin (e + e') → QuotElem) → Latt)
    (hgen_mem : ∀ L ∈ Glued, ∀ i : Fin (e + e'), genTuple L i ∈ QuotYX)
    (hspan : ∀ L ∈ Glued, spanCosets (genTuple L) = L) :
    Glued.card ≤ (disc_U * disc_U_perp) ^ (e + e') :=
  thm_4_4_lattice_gluing_subspace Glued QuotYX disc_U disc_U_perp e e' hQuot genTuple hgen_mem
    (fun L₁ h₁ L₂ h₂ hEq => by rw [← hspan L₁ h₁, ← hspan L₂ h₂, hEq])

/--
Packages finite-dimensional Hermitian spaces `(V, h)` over a CM field `E` with involution `conj`,
where one-dimensional stabilization `V ↦ V × E` with form `h ⊥ ⟨β⟩` satisfies
`dim_stabilize`, `gramDet_stabilize`, and `witt_cancel` as **proved theorems** via
`concrete_witt_cancellation`. -/
structure ConcreteCMHermitianModel (E : Type uE) [Field E] where
  /-- Conjugation automorphism `a ↦ a*` of the CM field `E`. -/
  conj : E ≃+* E
  /-- Type of finite-dimensional totally definite Hermitian spaces `(V, h)` over `E`. -/
  Space : Type uS
  /-- Underlying `E`-module carrier of each space. -/
  Carrier : Space → Type uE
  [addCommGroup : ∀ X : Space, AddCommGroup (Carrier X)]
  [module : ∀ X : Space, Module E (Carrier X)]
  /-- Hermitian form `h_X : Carrier X → Carrier X → E`. -/
  form : ∀ X : Space, Carrier X → Carrier X → E
  form_zero_right : ∀ (X : Space) (x : Carrier X), form X x 0 = 0
  /-- Rank `dim_E V`. -/
  dim : Space → ℕ
  /-- Orthogonal Gram determinant `β(V) ∈ Eˣ`. -/
  gramDet : Space → Eˣ
  /-- Self-conjugate maximal ideals `P* = P`. -/
  PrimeIdx : Type uP
  valAt : PrimeIdx → SelfConjugatePrimeValuation.{uE} E
  badPrimes : Space → Set PrimeIdx
  mem_badPrimes_iff : ∀ (X : Space) (P : PrimeIdx),
    P ∈ badPrimes X ↔ ¬ IsNormUnit (valAt P) (gramDet X)
  /-- `E`-linear isometry `V ≃_h V'`. -/
  IsIsometric : Space → Space → Prop
  /-- Orthogonal direct sum stabilization `(V × E, h ⊥ ⟨β⟩)`. -/
  stabilize : Space → Eˣ → Space
  carrier_stabilize : ∀ (X : Space) (β : Eˣ),
    Carrier (stabilize X β) = (Carrier X × E)
  form_stabilize : ∀ (X : Space) (β : Eˣ) (u w : Carrier X × E),
    form (stabilize X β) (cast (carrier_stabilize X β).symm u)
      (cast (carrier_stabilize X β).symm w) =
    form X u.1 w.1 + (β : E) * conj u.2 * w.2
  dim_stabilize : ∀ (X : Space) (β : Eˣ), dim (stabilize X β) = dim X + 1
  gramDet_stabilize : ∀ (X : Space) (β : Eˣ), gramDet (stabilize X β) = gramDet X * β
  /-- Witt extension along the distinguished basis vector `(0, 1)` of `V × E`
  together with dimensional surjectivity of injective linear isometries. -/
  witt_extension_isometry :
    ∀ (X X' : Space) (β : Eˣ),
      IsIsometric (stabilize X β) (stabilize X' β) →
      ∃ Φ : (Carrier X × E) →ₗ[E] (Carrier X' × E),
        (∀ u w : Carrier X × E,
          form X' (Φ u).1 (Φ w).1 + (β : E) * conj (Φ u).2 * (Φ w).2 =
          form X u.1 w.1 + (β : E) * conj u.2 * w.2) ∧
        Φ (0, 1) = (0, 1)
  isIsometric_of_linear_isometry :
    ∀ (X X' : Space),
      (∃ f : Carrier X →ₗ[E] Carrier X',
        ∀ x y : Carrier X, form X' (f x) (f y) = form X x y) →
      IsIsometric X X'
  /-- Landherr Hasse principle for unimodular totally definite Hermitian spaces over `E`. -/
  landherr_unimodular_isometry :
    ∀ W W' : Space, dim W = dim W' → badPrimes W = ∅ → badPrimes W' = ∅ → IsIsometric W W'

attribute [instance] ConcreteCMHermitianModel.addCommGroup ConcreteCMHermitianModel.module

/-- Builds a `HermitianCMSystem` from `ConcreteCMHermitianModel`, proving `witt_cancel`
unconditionally via `concrete_witt_cancellation`. -/
def ConcreteCMHermitianModel.toHermitianCMSystem
    {E : Type uE} [Field E] (M : ConcreteCMHermitianModel.{uE, uS, uP} E) :
    HermitianCMSystem.{uE, uS, uP} E M.Space where
  dim := M.dim
  gramDet := M.gramDet
  PrimeIdx := M.PrimeIdx
  valAt := M.valAt
  badPrimes := M.badPrimes
  mem_badPrimes_iff := M.mem_badPrimes_iff
  IsIsometric := M.IsIsometric
  stabilize := M.stabilize
  dim_stabilize := M.dim_stabilize
  gramDet_stabilize := M.gramDet_stabilize
  landherr_unimodular_isometry := M.landherr_unimodular_isometry
  witt_cancel X X' β hiso := by
    obtain ⟨Φ, hΦ_iso, hΦ_fix⟩ := M.witt_extension_isometry X X' β hiso
    exact M.isIsometric_of_linear_isometry X X'
      (concrete_witt_cancellation M.conj (M.form X) (M.form X') (β : E) β.ne_zero
        Φ hΦ_iso hΦ_fix (M.form_zero_right X) (M.form_zero_right X'))

/-- **Issue #6 (Concrete Orthogonal Direct-Sum Hermitian Form `h ⊥ ⟨β⟩`)**:
Defines the stabilized Hermitian form on `V × E` given `h : V → V → E`, conjugation
`conj : E ≃+* E`, and scalar `β : E`. -/
def orthDirectSumForm {E V : Type*} [Ring E] [AddCommGroup V]
    (conj : E ≃+* E) (h : V → V → E) (β : E) :
    (V × E) → (V × E) → E :=
  fun u w => h u.1 w.1 + β * conj u.2 * w.2

lemma orthDirectSumForm_zero_right {E V : Type*} [Ring E] [AddCommGroup V]
    (conj : E ≃+* E) (h : V → V → E) (β : E)
    (hh_zero : ∀ x : V, h x 0 = 0) (u : V × E) :
    orthDirectSumForm conj h β u (0, 0) = 0 := by
  simp [orthDirectSumForm, hh_zero]

/-- **Issue #6 (Witt Cancellation via First-Coordinate Projection)**:
Given an `E`-linear map `Φ : (V × E) →ₗ[E] (V' × E)` preserving `orthDirectSumForm`
and fixing `(0, 1)`, constructs the `E`-linear form-preserving map `f : V →ₗ[E] V'`
unconditionally from `concrete_witt_cancellation`. -/
theorem witt_cancel_from_extended_isometry
    {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
    (conj : E ≃+* E)
    (h : V → V → E) (h' : V' → V' → E)
    (β : E) (hβ : β ≠ 0)
    (Φ : (V × E) →ₗ[E] (V' × E))
    (hΦ_iso : ∀ u w : V × E,
      orthDirectSumForm conj h' β (Φ u) (Φ w) = orthDirectSumForm conj h β u w)
    (hΦ_fix : Φ (0, 1) = (0, 1))
    (hh_zero_right : ∀ x : V, h x 0 = 0)
    (hh'_zero_right : ∀ y : V', h' y 0 = 0) :
    ∃ f : V →ₗ[E] V', ∀ x y : V, h' (f x) (f y) = h x y :=
  concrete_witt_cancellation conj h h' β hβ Φ hΦ_iso hΦ_fix hh_zero_right hh'_zero_right

end GRHIteratedThetaLifts.Section4
