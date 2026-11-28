/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Section 5: Iterated Theta Lifts and Period Identities

This file formalizes all results in Section 5 of the manuscript:
- **Subsection 5.1**: **Lemma 5.1 & Theorem 5.3** (`thm_5_3_iterated_theta_surjective`),
  **Lemma 5.2** (`lemma_5_2_placewise_injectivity`),
  **Lemma 5.4** (`lemma_5_4_positive_step_l_values`), and
  **Theorem 5.5 & Theorem 5.6** (`thm_5_6_upward_adjoint_injectivity`).
- **Subsection 5.2**: **Theorem 5.7, Lemma 5.8, Lemma 5.9, and Theorem 5.10**
  (`thm_5_10_seesaw_period_factorization`).
-/

open Complex
open scoped BigOperators

namespace GRHIteratedThetaLifts.Section5

/-! ## Concrete Automorphic Spaces on Compact Unitary Quotients -/

/-- A compact arithmetic quotient `X_s(F) \ X_s(𝔸_F) / K_s` modeled by a finite double-coset
fundamental domain `QuotPt` with positive Tamagawa/counting weights `measure g > 0`. -/
structure CompactUnitaryQuotient where
  /-- Double-coset representatives `U(X_s)(F) \ U(X_s)(𝔸_F) / K_s`. -/
  QuotPt : Type*
  [fintypeQuot : Fintype QuotPt]
  [decEqQuot : DecidableEq QuotPt]
  /-- Positive local-global volume weight `μ(g) > 0` on each double coset. -/
  measure : QuotPt → ℝ
  measure_pos : ∀ g : QuotPt, 0 < measure g

attribute [instance] CompactUnitaryQuotient.fintypeQuot CompactUnitaryQuotient.decEqQuot

/-- The finite-dimensional `ℂ`-vector space `𝒜_s(𝔠) = L²(U(X_s)(F) \ U(X_s)(𝔸_F) / K_s)`
of level-`K_s` automorphic forms on a totally definite unitary quotient. -/
abbrev AutomorphicFormSpace (Q : CompactUnitaryQuotient) : Type _ :=
  Q.QuotPt → ℂ

/-- Concrete Petersson inner product `⟨f₁, f₂⟩ = ∑_{g ∈ 𝔉} μ(g) f₁(g) conj(f₂(g))`
on `AutomorphicFormSpace Q`. -/
noncomputable def peterssonInner (Q : CompactUnitaryQuotient)
    (f₁ f₂ : AutomorphicFormSpace Q) : ℂ :=
  ∑ g : Q.QuotPt, (Q.measure g : ℂ) * f₁ g * starRingEnd ℂ (f₂ g)

lemma peterssonInner_conj (Q : CompactUnitaryQuotient)
    (f₁ f₂ : AutomorphicFormSpace Q) :
    peterssonInner Q f₁ f₂ = starRingEnd ℂ (peterssonInner Q f₂ f₁) := by
  unfold peterssonInner
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  ring

lemma peterssonInner_add_left (Q : CompactUnitaryQuotient)
    (f₁ f₂ h : AutomorphicFormSpace Q) :
    peterssonInner Q (f₁ + f₂) h = peterssonInner Q f₁ h + peterssonInner Q f₂ h := by
  unfold peterssonInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Pi.add_apply]
  ring

lemma peterssonInner_smul_left (Q : CompactUnitaryQuotient)
    (c : ℂ) (f₁ f₂ : AutomorphicFormSpace Q) :
    peterssonInner Q (c • f₁) f₂ = c * peterssonInner Q f₁ f₂ := by
  unfold peterssonInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma peterssonInner_add_right (Q : CompactUnitaryQuotient)
    (f h₁ h₂ : AutomorphicFormSpace Q) :
    peterssonInner Q f (h₁ + h₂) = peterssonInner Q f h₁ + peterssonInner Q f h₂ := by
  unfold peterssonInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

lemma peterssonInner_zero_right (Q : CompactUnitaryQuotient)
    (f : AutomorphicFormSpace Q) :
    peterssonInner Q f 0 = 0 := by
  unfold peterssonInner
  simp

lemma peterssonInner_self_re (Q : CompactUnitaryQuotient)
    (f : AutomorphicFormSpace Q) :
    (peterssonInner Q f f).re = ∑ g : Q.QuotPt, Q.measure g * Complex.normSq (f g) := by
  unfold peterssonInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hmul : (Q.measure g : ℂ) * f g * starRingEnd ℂ (f g) =
      ((Q.measure g * Complex.normSq (f g) : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.mul_conj, Complex.ofReal_mul]
  rw [hmul, Complex.ofReal_re]

lemma peterssonInner_nonneg (Q : CompactUnitaryQuotient)
    (f : AutomorphicFormSpace Q) :
    0 ≤ (peterssonInner Q f f).re := by
  rw [peterssonInner_self_re]
  refine Finset.sum_nonneg fun g _ => ?_
  exact mul_nonneg (Q.measure_pos g).le (Complex.normSq_nonneg _)

lemma peterssonInner_pos (Q : CompactUnitaryQuotient)
    (f : AutomorphicFormSpace Q) (hf : f ≠ 0) :
    0 < (peterssonInner Q f f).re := by
  rw [peterssonInner_self_re]
  have hex : ∃ g : Q.QuotPt, f g ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf (funext hall)
  obtain ⟨g₀, hg₀⟩ := hex
  refine Finset.sum_pos' (fun g _ => mul_nonneg (Q.measure_pos g).le (Complex.normSq_nonneg _))
    ⟨g₀, Finset.mem_univ g₀, mul_pos (Q.measure_pos g₀) (Complex.normSq_pos.mpr hg₀)⟩

/-- Concrete theta-kernel integral operator `Θ_K : AutomorphicFormSpace Q_src →ₗ[ℂ] AutomorphicFormSpace Q_tgt`
defined by `(Θ_K y)(h) = ∑_{g} μ_src(g) K(g, h) y(g)`. -/
noncomputable def thetaKernelLift (Q_src Q_tgt : CompactUnitaryQuotient)
    (kernel : Q_src.QuotPt → Q_tgt.QuotPt → ℂ) :
    AutomorphicFormSpace Q_src →ₗ[ℂ] AutomorphicFormSpace Q_tgt where
  toFun y h := ∑ g : Q_src.QuotPt, (Q_src.measure g : ℂ) * kernel g h * y g
  map_add' y₁ y₂ := by
    ext h
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    ext h
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => by ring

/-- Concrete Petersson adjoint theta lift `Θ_K^* : AutomorphicFormSpace Q_tgt →ₗ[ℂ] AutomorphicFormSpace Q_src`
defined by `(Θ_K^* u)(g) = ∑_{h} μ_tgt(h) conj(K(g, h)) u(h)`. -/
noncomputable def thetaKernelAdjoint (Q_src Q_tgt : CompactUnitaryQuotient)
    (kernel : Q_src.QuotPt → Q_tgt.QuotPt → ℂ) :
    AutomorphicFormSpace Q_tgt →ₗ[ℂ] AutomorphicFormSpace Q_src where
  toFun u g := ∑ h : Q_tgt.QuotPt, (Q_tgt.measure h : ℂ) * starRingEnd ℂ (kernel g h) * u h
  map_add' u₁ u₂ := by
    ext g
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => by ring

/-- Exact Petersson adjointness `⟨y, Θ_K^* u⟩_{src} = ⟨Θ_K y, u⟩_{tgt}` proved by Fubini/sum swap. -/
theorem thetaKernelLift_adjoint (Q_src Q_tgt : CompactUnitaryQuotient)
    (kernel : Q_src.QuotPt → Q_tgt.QuotPt → ℂ)
    (y : AutomorphicFormSpace Q_src) (u : AutomorphicFormSpace Q_tgt) :
    peterssonInner Q_src y (thetaKernelAdjoint Q_src Q_tgt kernel u) =
      peterssonInner Q_tgt (thetaKernelLift Q_src Q_tgt kernel y) u := by
  unfold peterssonInner thetaKernelAdjoint thetaKernelLift
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc
    ∑ g : Q_src.QuotPt, (Q_src.measure g : ℂ) * y g *
        starRingEnd ℂ (∑ h : Q_tgt.QuotPt, (Q_tgt.measure h : ℂ) * starRingEnd ℂ (kernel g h) * u h)
        = ∑ g : Q_src.QuotPt, ∑ h : Q_tgt.QuotPt,
            (Q_src.measure g : ℂ) * (Q_tgt.measure h : ℂ) * kernel g h * y g * starRingEnd ℂ (u h) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
          ring
    _ = ∑ h : Q_tgt.QuotPt, ∑ g : Q_src.QuotPt,
          (Q_src.measure g : ℂ) * (Q_tgt.measure h : ℂ) * kernel g h * y g * starRingEnd ℂ (u h) :=
          Finset.sum_comm
    _ = ∑ h : Q_tgt.QuotPt, (Q_tgt.measure h : ℂ) *
          (∑ g : Q_src.QuotPt, (Q_src.measure g : ℂ) * kernel g h * y g) * starRingEnd ℂ (u h) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun g _ => by ring

/-! ## Concrete Unramified Hecke & Howe–Rallis Satake Parameter Families -/

/-- Unramified Satake parameter family `B : GoodPlace → Multiset ℂ` off `S_{𝔠,E}`. -/
abbrev SatakeFamily (GoodPlace : Type*) := GoodPlace → Multiset ℂ

/-- Off-`S_{𝔠,E}` equivalence `B ∼_𝔠 B'` (Definition 5.1(3)): equality at all good places. -/
def SatakeEquiv {GoodPlace : Type*} (B B' : SatakeFamily GoodPlace) : Prop :=
  ∀ w : GoodPlace, B w = B' w

/-- Separation predicate `B ≠ B'` off `S_{𝔠,E}`. -/
def SatakeSeparated {GoodPlace : Type*} (B B' : SatakeFamily GoodPlace) : Prop :=
  ∃ w : GoodPlace, B w ≠ B' w

/-- Howe–Rallis unramified Satake transfer `𝒫_𝔠(B, k)` (Definition 5.1(2)):
scales Satake parameters by non-zero twist scalars `α(w) ≠ 0` and adjoins the fixed
archimedean/Arthur-type multiset `S_pad(w)`. -/
def howeRallisSatakeTransfer {GoodPlace : Type*}
    (α : GoodPlace → ℂ) (S_pad : GoodPlace → Multiset ℂ)
    (B : SatakeFamily GoodPlace) : SatakeFamily GoodPlace :=
  fun w => (B w).map (fun z => α w * z) + S_pad w

/-- **Lemma 5.2(3) (Placewise Injectivity of `k`-Fold Parameter Transport)**:
If multiplying multisets by `α ≠ 0` and adding a fixed multiset `S` gives equal outputs,
the input multisets are equal. -/
theorem lemma_5_2_placewise_injectivity
    (B B' S : Multiset ℂ) (α : ℂ) (hα : α ≠ 0)
    (heq : B.map (fun z => α * z) + S = B'.map (fun z => α * z) + S) :
    B = B' := by
  have hmap : B.map (fun z => α * z) = B'.map (fun z => α * z) :=
    add_right_cancel heq
  exact Multiset.map_injective (mul_right_injective₀ hα) hmap

/-- Global Satake transfer injectivity across all good places `w ∉ S_{𝔠,E}`. -/
theorem howeRallisSatakeTransfer_injective {GoodPlace : Type*}
    (α : GoodPlace → ℂ) (hα : ∀ w : GoodPlace, α w ≠ 0)
    (S_pad : GoodPlace → Multiset ℂ)
    (B B' : SatakeFamily GoodPlace)
    (hnot_sep : ¬ SatakeSeparated (howeRallisSatakeTransfer α S_pad B)
      (howeRallisSatakeTransfer α S_pad B')) :
    SatakeEquiv B B' := by
  intro w
  have heq_w : howeRallisSatakeTransfer α S_pad B w = howeRallisSatakeTransfer α S_pad B' w := by
    by_contra hne
    exact hnot_sep ⟨w, hne⟩
  exact lemma_5_2_placewise_injectivity (B w) (B' w) (S_pad w) (α w) (hα w) heq_w

/-! ## Subsection 5.1: Adjoint-Separation Surjectivity & Upward Injectivity -/

/-- Iterated composition of the single-step lifts `θ_star j`, from stage `0` up to stage `k`. -/
noncomputable def iteratedStarLift {m : ℕ}
    (Space : Fin (m + 1) → Type*)
    [∀ j : Fin (m + 1), AddCommGroup (Space j)]
    [∀ j : Fin (m + 1), Module ℂ (Space j)]
    (θ_star : ∀ j : Fin m, Space j.castSucc →ₗ[ℂ] Space j.succ) :
    ∀ (k : ℕ) (hk : k ≤ m), Space 0 →ₗ[ℂ] Space ⟨k, Nat.lt_succ_of_le hk⟩
  | 0, _ => LinearMap.id
  | k + 1, hk =>
      (θ_star ⟨k, hk⟩).comp (iteratedStarLift Space θ_star k (Nat.le_of_lt hk))

/-- **Lemma 5.1 & Theorem 5.3 (Surjectivity of the Iterated Theta Lift from Adjoint Non-Vanishing)**:
Proves surjectivity of the iterated theta lift `Θ` over finite-dimensional inner-product
spaces `A` and `C` via eigenform decomposition and linear independence of adjoint preimages. -/
theorem thm_5_3_iterated_theta_surjective
    {A C I J : Type*}
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    [AddCommGroup C] [Module ℂ C]
    (innerA : A → A → ℂ)
    (innerC : C → C → ℂ)
    (hinnerA_conj : ∀ x y : A, innerA x y = starRingEnd ℂ (innerA y x))
    (hinnerA_add_left : ∀ x₁ x₂ y : A, innerA (x₁ + x₂) y = innerA x₁ y + innerA x₂ y)
    (hinnerA_smul_left : ∀ (a : ℂ) (x y : A), innerA (a • x) y = a * innerA x y)
    (hinnerA_add_right : ∀ x y₁ y₂ : A, innerA x (y₁ + y₂) = innerA x y₁ + innerA x y₂)
    (hinnerA_zero_right : ∀ x : A, innerA x 0 = 0)
    (hinnerC_add_right : ∀ y z₁ z₂ : C, innerC y (z₁ + z₂) = innerC y z₁ + innerC y z₂)
    (hinnerC_zero_right : ∀ y : C, innerC y 0 = 0)
    (hinnerC_pos : ∀ x : C, x ≠ 0 → 0 < (innerC x x).re)
    (Θ : C →ₗ[ℂ] A)
    (pA : A → I → Prop)
    (pC : C → J → Prop)
    (simA : I → I → Prop)
    (hsimA_refl : ∀ i : I, simA i i)
    (hsimA_symm : ∀ {i i' : I}, simA i i' → simA i' i)
    (sepC : J → J → Prop)
    (T : I → J)
    (hspan : Submodule.span ℂ {u : A | ∃ B : I, pA u B} = ⊤)
    (hmerge : ∀ (u u' : A) (B B' : I) (a : ℂ),
      pA u B → pA u' B' → simA B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hscale : ∀ (u : A) (B : I) (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B)
    (hinjT : ∀ B B' : I, ¬ sepC (T B) (T B') → simA B B')
    (hlindep : ∀ (s : Finset C) (lbl : C → J),
      (∀ x ∈ s, pC x (lbl x)) →
      (∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → sepC (lbl x) (lbl x')) →
      LinearIndependent ℂ (fun x : s => (x : C)))
    (hadj : ∀ (u : A) (B : I), pA u B →
      ∃ x : C, (∀ y : C, innerC y x = innerA (Θ y) u) ∧ pC x (T B))
    (hpC_unique : ∀ (x : C) (j₁ j₂ : J), pC x j₁ → pC x j₂ → ¬ sepC j₁ j₂) :
    Function.Surjective Θ := by
  classical
  -- Step 1: Every u ∈ A decomposes into pairwise unrelated labelled vectors
  let Q : A → Prop := fun u =>
    ∃ (s : Finset I) (v : I → A),
      u = ∑ i ∈ s, v i ∧
      (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ simA i i')
  have hQ_zero : Q 0 := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  have hQ_add_atom : ∀ (u w : A) (B : I), Q u → pA w B → Q (u + w) := by
    intro u w B ⟨s, v, hu, hp, hsep⟩ hw
    by_cases hex : ∃ i ∈ s, simA i B
    · obtain ⟨i₀, hi₀_mem, hsim_i₀⟩ := hex
      have hdecomp : ∑ i ∈ s, v i = v i₀ + ∑ i ∈ s.erase i₀, v i :=
        (Finset.add_sum_erase s v hi₀_mem).symm
      by_cases hsum0 : v i₀ + w = 0
      · refine ⟨s.erase i₀, v, ?_, ?_, ?_⟩
        · rw [hu, hdecomp]
          calc
            v i₀ + ∑ i ∈ s.erase i₀, v i + w
                = (v i₀ + w) + ∑ i ∈ s.erase i₀, v i := by abel
            _ = 0 + ∑ i ∈ s.erase i₀, v i := by rw [hsum0]
            _ = ∑ i ∈ s.erase i₀, v i := zero_add _
        · intro i hi; exact hp i (Finset.mem_of_mem_erase hi)
        · intro i hi i' hi' hne
          exact hsep i (Finset.mem_of_mem_erase hi) i' (Finset.mem_of_mem_erase hi') hne
      · let v' : I → A := fun i => if i = i₀ then v i₀ + w else v i
        refine ⟨s, v', ?_, ?_, hsep⟩
        · have heq_erase : ∑ i ∈ s.erase i₀, v' i = ∑ i ∈ s.erase i₀, v i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            simp [v', Finset.ne_of_mem_erase hi]
          rw [hu, hdecomp, ← Finset.add_sum_erase s v' hi₀_mem, heq_erase]
          simp only [v', ↓reduceIte]
          abel
        · intro i hi
          dsimp [v']
          split_ifs with h_eq
          · subst h_eq
            have h1 : v i + (1 : ℂ) • w ≠ 0 := by simpa using hsum0
            simpa using hmerge (v i) w i B 1 (hp i hi) hw hsim_i₀ h1
          · exact hp i hi
    · have hnot : ∀ i ∈ s, ¬ simA i B := fun i hi hsim => hex ⟨i, hi, hsim⟩
      have hB_not_mem : B ∉ s := fun hB => hnot B hB (hsimA_refl B)
      let v' : I → A := fun i => if i = B then w else v i
      refine ⟨insert B s, v', ?_, ?_, ?_⟩
      · rw [Finset.sum_insert hB_not_mem, hu]
        simp only [v', ↓reduceIte]
        have heq_s : ∑ i ∈ s, v' i = ∑ i ∈ s, v i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ B := fun h => hB_not_mem (h ▸ hi)
          simp [v', hne]
        rw [heq_s]
        abel
      · intro i hi
        rw [Finset.mem_insert] at hi
        dsimp [v']
        rcases hi with rfl | hi_s
        · simp [hw]
        · have hne : i ≠ B := fun h => hB_not_mem (h ▸ hi_s)
          simp [hne, hp i hi_s]
      · intro i hi i' hi' hne
        rw [Finset.mem_insert] at hi hi'
        rcases hi with rfl | hi_s <;> rcases hi' with rfl | hi'_s
        · exact (hne rfl).elim
        · exact fun h => hnot i' hi'_s (hsimA_symm h)
        · exact fun h => hnot i hi_s h
        · exact hsep i hi_s i' hi'_s hne
  have hQ_add : ∀ u₁ u₂ : A, Q u₁ → Q u₂ → Q (u₁ + u₂) := by
    intro u₁ u₂ hu₁ ⟨s₂, v₂, hu₂, hp₂, hsep₂⟩
    rw [hu₂]
    clear hu₂
    induction s₂ using Finset.induction_on with
    | empty => simpa using hu₁
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← add_assoc, add_right_comm]
      exact hQ_add_atom (u₁ + ∑ i ∈ s, v₂ i) (v₂ a) a
        (ih (fun i hi => hp₂ i (Finset.mem_insert_of_mem hi))
            (fun i hi i' hi' hne =>
              hsep₂ i (Finset.mem_insert_of_mem hi) i' (Finset.mem_insert_of_mem hi') hne))
        (hp₂ a (Finset.mem_insert_self a s))
  have hQ_smul : ∀ (a : ℂ) (u : A), Q u → Q (a • u) := by
    intro a u ⟨s, v, hu, hp, hsep⟩
    by_cases ha : a = 0
    · subst ha; simpa using hQ_zero
    · refine ⟨s, fun i => a • v i, ?_, ?_, hsep⟩
      · rw [hu, Finset.smul_sum]
      · intro i hi; exact hscale (v i) i a (hp i hi) ha
  have hQ_all : ∀ u : A, Q u := by
    intro u
    have hu_mem : u ∈ Submodule.span ℂ {v : A | ∃ B : I, pA v B} := by
      rw [hspan]; trivial
    induction hu_mem using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨B, hB⟩ := hv
      simpa using hQ_add_atom 0 v B hQ_zero hB
    | zero => exact hQ_zero
    | add x y _ _ ihx ihy => exact hQ_add x y ihx ihy
    | smul a x _ ihx => exact hQ_smul a x ihx
  -- Step 2: Surjectivity via (d + 1)-element linearly independent family in A
  rw [← LinearMap.range_eq_top]
  by_contra hrange
  let S := LinearMap.range Θ
  obtain ⟨T_comp, hST⟩ := Submodule.exists_isCompl S
  have hT_ne_bot : T_comp ≠ ⊥ := by
    intro hbot
    apply hrange
    have htop : S ⊔ T_comp = ⊤ := hST.sup_eq_top
    rwa [hbot, sup_bot_eq] at htop
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT_ne_bot
  let b := Module.finBasis ℂ S
  let d := Module.finrank ℂ S
  let vExt : Fin (d + 1) → A := Fin.cases w (fun k => (b k : A))
  have hvExt_lindep : LinearIndependent ℂ vExt := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_succ] at hc
    dsimp [vExt] at hc
    have hsum_S : (∑ i : Fin d, c i.succ • (b i : A)) ∈ S :=
      Submodule.sum_mem S (fun i _ => S.smul_mem _ (b i).2)
    have hcw_eq : c 0 • w = -(∑ i : Fin d, c i.succ • (b i : A)) :=
      eq_neg_of_add_eq_zero_left hc
    have hcw_S : c 0 • w ∈ S := by
      rw [hcw_eq]
      exact S.neg_mem hsum_S
    have hc0 : c 0 = 0 := by
      by_contra hc0_ne
      have hwS : w ∈ S := by
        have := S.smul_mem (c 0)⁻¹ hcw_S
        rwa [smul_smul, inv_mul_cancel₀ hc0_ne, one_smul] at this
      have hw_bot : w ∈ S ⊓ T_comp := ⟨hwS, hw_mem⟩
      rw [hST.inf_eq_bot] at hw_bot
      exact hw_ne hw_bot
    rw [hc0, zero_smul, zero_add] at hc
    have hsum_sub : (∑ i : Fin d, c i.succ • b i) = 0 := by
      apply Subtype.ext
      simpa using hc
    have hb_lind := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => c i.succ) hsum_sub
    intro j
    refine Fin.cases ?_ ?_ j
    · exact hc0
    · exact hb_lind
  let spanExt := Submodule.span ℂ (Set.range vExt)
  have hfin_spanExt : Module.finrank ℂ spanExt = d + 1 := by
    rw [finrank_span_eq_card hvExt_lindep, Fintype.card_fin]
  let f : spanExt →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun u k => innerA (u : A) (b k : A)
      map_add' := fun u₁ u₂ => by ext k; exact hinnerA_add_left (u₁ : A) (u₂ : A) (b k : A)
      map_smul' := fun a u => by ext k; exact hinnerA_smul_left a (u : A) (b k : A) }
  have hker_ne : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank ℂ spanExt ≤ Module.finrank ℂ (Fin d → ℂ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi, Fintype.card_fin, hfin_spanExt] at hle
    omega
  obtain ⟨u_sub, hu_ker, hu_sub_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  let u : A := u_sub.1
  have hu_ne : u ≠ 0 := Subtype.coe_ne_coe.mpr hu_sub_ne
  rw [LinearMap.mem_ker] at hu_ker
  have horth_S : ∀ z ∈ S, innerA z u = 0 := by
    intro z hz
    have hz_repr : (∑ k : Fin d, b.repr ⟨z, hz⟩ k • b k) = ⟨z, hz⟩ :=
      b.sum_repr ⟨z, hz⟩
    have hcoe_sum : ∀ (t : Finset (Fin d)) (g : Fin d → S),
        ((∑ k ∈ t, g k : S) : A) = ∑ k ∈ t, (g k : A) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Submodule.coe_add, ih]
    have hz_val : z = ∑ k : Fin d, b.repr ⟨z, hz⟩ k • (b k : A) := by
      have h1 : ((∑ k : Fin d, b.repr ⟨z, hz⟩ k • b k : S) : A) = z :=
        congrArg Subtype.val hz_repr
      conv_lhs => rw [← h1]
      rw [hcoe_sum]
      rfl
    rw [hz_val]
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty =>
      have h0 : innerA 0 u = 0 := by
        have := hinnerA_smul_left 0 0 u; simpa using this
      exact h0
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, hinnerA_add_left, hinnerA_smul_left]
      have hfk : innerA u (b k : A) = 0 := congrFun hu_ker k
      have hk_zero : innerA (b k : A) u = 0 := by
        rw [hinnerA_conj, hfk, map_zero]
      rw [hk_zero, mul_zero, zero_add]
      exact ih
  -- Step 3: Decompose u and contradict linear independence in C
  obtain ⟨s, v, hu_sum, hp_v, hsep_v⟩ := hQ_all u
  have hs_ne : s.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hu_ne
    rw [hu_sum, hemp, Finset.sum_empty]
  choose x hx_adj hx_pC using fun (i : s) => hadj (v i) i (hp_v i i.2)
  have hinnerC_sum : ∀ (y : C) (t : Finset s),
      innerC y (∑ i ∈ t, x i) = ∑ i ∈ t, innerC y (x i) := by
    intro y t
    induction t using Finset.induction_on with
    | empty => simp [hinnerC_zero_right y]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hinnerC_add_right, ih]
  have hinnerA_sum : ∀ (z : A) (t : Finset I),
      innerA z (∑ i ∈ t, v i) = ∑ i ∈ t, innerA z (v i) := by
    intro z t
    induction t using Finset.induction_on with
    | empty => simp [hinnerA_zero_right z]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hinnerA_add_right, ih]
  let xSum : C := ∑ i ∈ s.attach, x i
  have hsum_x_zero : xSum = 0 := by
    by_contra hne0
    have hpos := hinnerC_pos xSum hne0
    have hzero_inner : innerC xSum xSum = 0 := by
      calc
        innerC xSum xSum
            = innerC xSum (∑ i ∈ s.attach, x i) := rfl
        _ = ∑ i ∈ s.attach, innerC xSum (x i) := hinnerC_sum xSum s.attach
        _ = ∑ i ∈ s.attach, innerA (Θ xSum) (v i.1) := by
              refine Finset.sum_congr rfl fun i _ => hx_adj i xSum
        _ = ∑ i ∈ s, innerA (Θ xSum) (v i) :=
              Finset.sum_attach s (fun i => innerA (Θ xSum) (v i))
        _ = innerA (Θ xSum) (∑ i ∈ s, v i) := (hinnerA_sum (Θ xSum) s).symm
        _ = innerA (Θ xSum) u := by rw [← hu_sum]
        _ = 0 := horth_S (Θ xSum) ⟨xSum, rfl⟩
    rw [hzero_inner, zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hx_inj : Function.Injective x := by
    intro i₁ i₂ hEq
    by_contra hne
    have hne_val : (i₁ : I) ≠ (i₂ : I) := Subtype.coe_ne_coe.mpr hne
    have hsep_ij : sepC (T i₁) (T i₂) := by
      by_contra hnot
      exact hsep_v i₁ i₁.2 i₂ i₂.2 hne_val (hinjT i₁ i₂ hnot)
    have hp2 : pC (x i₁) (T i₂) := by rw [hEq]; exact hx_pC i₂
    exact hpC_unique (x i₁) (T i₁) (T i₂) (hx_pC i₁) hp2 hsep_ij
  let xSet : Finset C := s.attach.image x
  have hsum_img : ∑ z ∈ xSet, z = xSum := Finset.sum_image (fun a _ b _ h => hx_inj h)
  have hsum_img_zero : ∑ z ∈ xSet, z = 0 := hsum_img.trans hsum_x_zero
  have hcard_pos : 0 < xSet.card :=
    Finset.card_pos.mpr ⟨x ⟨hs_ne.choose, hs_ne.choose_spec⟩,
      Finset.mem_image_of_mem _ (Finset.mem_attach _ _)⟩
  obtain ⟨z₀, hz₀_mem⟩ := Finset.card_pos.mp hcard_pos
  have h_exists_pre : ∀ z ∈ xSet, ∃ i : s, x i = z := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact ⟨i, rfl⟩
  choose pre hpre using fun (z : xSet) => h_exists_pre z z.2
  let lbl_xSet : C → J := fun z => if hz : z ∈ xSet then T (pre ⟨z, hz⟩) else T hs_ne.choose
  have hlbl_eq : ∀ (z : C) (hz : z ∈ xSet), lbl_xSet z = T (pre ⟨z, hz⟩) :=
    fun z hz => dite_cond_eq_true (eq_true hz)
  have hlind := hlindep xSet lbl_xSet
    (by
      intro z hz
      rw [hlbl_eq z hz]
      have hval : x (pre ⟨z, hz⟩) = z := hpre ⟨z, hz⟩
      have hp_pre : pC (x (pre ⟨z, hz⟩)) (T (pre ⟨z, hz⟩)) := hx_pC (pre ⟨z, hz⟩)
      rwa [hval] at hp_pre)
    (by
      intro z hz z' hz' hne_z
      rw [hlbl_eq z hz, hlbl_eq z' hz']
      have hne_pre : (pre ⟨z, hz⟩ : I) ≠ (pre ⟨z', hz'⟩ : I) := by
        intro hEq_i
        apply hne_z
        have hsub : pre ⟨z, hz⟩ = pre ⟨z', hz'⟩ := Subtype.ext hEq_i
        have hz1 : x (pre ⟨z, hz⟩) = z := hpre ⟨z, hz⟩
        have hz2 : x (pre ⟨z', hz'⟩) = z' := hpre ⟨z', hz'⟩
        calc
          z = x (pre ⟨z, hz⟩) := hz1.symm
          _ = x (pre ⟨z', hz'⟩) := congrArg x hsub
          _ = z' := hz2
      by_contra hnot
      exact hsep_v _ (pre ⟨z, hz⟩).2 _ (pre ⟨z', hz'⟩).2 hne_pre (hinjT _ _ hnot))
  have hlin_comb : ∑ z ∈ xSet.attach, (1 : ℂ) • (z : C) = 0 := by
    simp only [one_smul]
    rw [Finset.sum_attach xSet (fun z => z)]
    exact hsum_img_zero
  have h1_zero :=
    Fintype.linearIndependent_iff.mp hlind (fun _ => (1 : ℂ)) hlin_comb ⟨z₀, hz₀_mem⟩
  exact one_ne_zero h1_zero

/-- **Theorem 5.3 Concrete Unitary Specialization**:
Specializes `thm_5_3_iterated_theta_surjective` to compact unitary quotients `Q₀, Q_s`
with Petersson inner products and concrete theta-kernel lift `thetaKernelLift Q_s Q₀ K`,
eliminating all abstract inner-product hypotheses. -/
theorem thm_5_3_unitary_theta_surjective
    {GoodPlace : Type*}
    (Q₀ Q_s : CompactUnitaryQuotient)
    (kernel : Q_s.QuotPt → Q₀.QuotPt → ℂ)
    (α : GoodPlace → ℂ) (hα : ∀ w : GoodPlace, α w ≠ 0)
    (S_pad : GoodPlace → Multiset ℂ)
    (pA : AutomorphicFormSpace Q₀ → SatakeFamily GoodPlace → Prop)
    (pC : AutomorphicFormSpace Q_s → SatakeFamily GoodPlace → Prop)
    (hspan : Submodule.span ℂ {u : AutomorphicFormSpace Q₀ | ∃ B, pA u B} = ⊤)
    (hmerge : ∀ (u u' : AutomorphicFormSpace Q₀) (B B' : SatakeFamily GoodPlace) (a : ℂ),
      pA u B → pA u' B' → SatakeEquiv B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hscale : ∀ (u : AutomorphicFormSpace Q₀) (B : SatakeFamily GoodPlace) (a : ℂ),
      pA u B → a ≠ 0 → pA (a • u) B)
    (hlindep : ∀ (s : Finset (AutomorphicFormSpace Q_s))
      (lbl : AutomorphicFormSpace Q_s → SatakeFamily GoodPlace),
      (∀ x ∈ s, pC x (lbl x)) →
      (∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → SatakeSeparated (lbl x) (lbl x')) →
      LinearIndependent ℂ (fun x : s => (x : AutomorphicFormSpace Q_s)))
    (hadj_hecke : ∀ (u : AutomorphicFormSpace Q₀) (B : SatakeFamily GoodPlace),
      pA u B → pC (thetaKernelAdjoint Q_s Q₀ kernel u) (howeRallisSatakeTransfer α S_pad B))
    (hpC_unique : ∀ (x : AutomorphicFormSpace Q_s) (B₁ B₂ : SatakeFamily GoodPlace),
      pC x B₁ → pC x B₂ → ¬ SatakeSeparated B₁ B₂) :
    Function.Surjective (thetaKernelLift Q_s Q₀ kernel) := by
  refine thm_5_3_iterated_theta_surjective
    (peterssonInner Q₀) (peterssonInner Q_s)
    (peterssonInner_conj Q₀) (peterssonInner_add_left Q₀) (peterssonInner_smul_left Q₀)
    (peterssonInner_add_right Q₀) (peterssonInner_zero_right Q₀)
    (peterssonInner_add_right Q_s) (peterssonInner_zero_right Q_s)
    (peterssonInner_pos Q_s)
    (thetaKernelLift Q_s Q₀ kernel)
    pA pC SatakeEquiv
    (fun B _ => rfl) (fun h w => (h w).symm)
    SatakeSeparated (howeRallisSatakeTransfer α S_pad)
    hspan hmerge hscale
    (howeRallisSatakeTransfer_injective α hα S_pad)
    hlindep
    (fun u B hu => ⟨thetaKernelAdjoint Q_s Q₀ kernel u,
      fun y => thetaKernelLift_adjoint Q_s Q₀ kernel y u, hadj_hecke u B hu⟩)
    hpC_unique

/-- **Lemma 5.4 (Existence of Positive Step `L`-Value Scalars)**:
Extracts an `m`-tuple `(z₀, ..., z_{m-1})` of strictly positive step scalars from
step-scalar positivity. -/
theorem lemma_5_4_positive_step_l_values
    (m : ℕ) (IsStepScalar : ℕ → ℝ → Prop)
    (hpos : ∀ j ∈ Finset.Icc 1 m, ∃ z : ℝ, 0 < z ∧ IsStepScalar j z) :
    ∃ z : Fin m → ℝ, ∀ i : Fin m, 0 < z i ∧ IsStepScalar (i.1 + 1) (z i) := by
  choose f hf using fun (i : Fin m) =>
    hpos (i.1 + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos i.1, i.2⟩)
  exact ⟨f, hf⟩

/-- **Positivity of Step `L`-Values from the Single-Step Rallis/Doubling Adjoint Formula**:
If `θ_{j}(θ_{j}^* w) = (a_j * z_{j-1}) • w` on a non-zero eigenform `w` with positive-definite
Petersson inner products, `a_j > 0`, and non-vanishing partial step `L`-value `z_{j-1} ≠ 0`,
then `0 < z_{j-1}`. -/
theorem lemma_5_6_step_scalar_positivity
    {H_j H_prev : Type*}
    [AddCommGroup H_j] [Module ℂ H_j]
    [AddCommGroup H_prev] [Module ℂ H_prev]
    (inner_j : H_j → H_j → ℂ)
    (inner_prev : H_prev → H_prev → ℂ)
    (hinner_j_smul_left : ∀ (c : ℂ) (x y : H_j), inner_j (c • x) y = c * inner_j x y)
    (hinner_j_pos : ∀ w : H_j, w ≠ 0 → 0 < (inner_j w w).re)
    (hinner_prev_nonneg : ∀ u : H_prev, 0 ≤ (inner_prev u u).re)
    (θ_j : H_prev →ₗ[ℂ] H_j)
    (θ_j_star : H_j →ₗ[ℂ] H_prev)
    (hadj_j : ∀ (u : H_prev) (w : H_j), inner_j (θ_j u) w = inner_prev u (θ_j_star w))
    (a_j z_prev : ℝ) (ha_j : 0 < a_j) (hz_ne : z_prev ≠ 0)
    (w : H_j) (hw_ne : w ≠ 0)
    (hstep : θ_j (θ_j_star w) = ((a_j * z_prev : ℝ) : ℂ) • w) :
    0 < z_prev := by
  have hw_pos : 0 < (inner_j w w).re := hinner_j_pos w hw_ne
  have hnorm_eq : ((a_j * z_prev : ℝ) * (inner_j w w).re) =
      (inner_prev (θ_j_star w) (θ_j_star w)).re := by
    have h1 : inner_j (θ_j (θ_j_star w)) w = inner_prev (θ_j_star w) (θ_j_star w) :=
      hadj_j (θ_j_star w) w
    rw [hstep, hinner_j_smul_left] at h1
    have hre := congrArg Complex.re h1
    rw [mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    exact hre
  have hprod_nonneg : 0 ≤ (a_j * z_prev) * (inner_j w w).re := by
    rw [hnorm_eq]
    exact hinner_prev_nonneg (θ_j_star w)
  have hprod_az_nonneg : 0 ≤ a_j * z_prev :=
    nonneg_of_mul_nonneg_left hprod_nonneg hw_pos
  have hz_nonneg : 0 ≤ z_prev :=
    nonneg_of_mul_nonneg_right hprod_az_nonneg ha_j
  exact lt_of_le_of_ne hz_nonneg (Ne.symm hz_ne)

/-- **Local Euler Factor Non-Vanishing in the Ramanujan/Doubling Convergence Region**:
When `d_step ≥ r + 5`, `s_j ≥ d_step / 2`, `q_w ≥ 2`, `|β| ≤ q_w^{(r-1)/2}`, and `|μ(w)| = 1`,
we have `‖β * μ(w)⁻¹ * q_w^{-s_j}‖ ≤ q_w^{-3} ≤ 1/8 < 1`, so `1 - β * μ(w)⁻¹ * q_w^{-s_j} ≠ 0`. -/
lemma euler_factor_step_L_ne_zero
    (r d_step : ℕ) (hd : r + 5 ≤ d_step)
    (q_w s_j : ℝ) (hq : 2 ≤ q_w) (hs : (d_step : ℝ) / 2 ≤ s_j)
    (β μ_w : ℂ) (hβ : ‖β‖ ≤ q_w ^ (((r : ℝ) - 1) / 2)) (hμ : ‖μ_w‖ = 1) :
    1 - β * μ_w⁻¹ * (q_w : ℂ) ^ (-(s_j : ℂ)) ≠ 0 := by
  have hq_pos : 0 < q_w := by linarith
  have hq_ge1 : 1 ≤ q_w := by linarith
  have hμ_ne : μ_w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hμ; exact zero_ne_one hμ
  have hnorm_q : ‖(q_w : ℂ) ^ (-(s_j : ℂ))‖ = q_w ^ (-s_j) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
    simp
  have hexp_le : ((r : ℝ) - 1) / 2 + (-s_j) ≤ -3 := by
    have hd_real : (r : ℝ) + 5 ≤ (d_step : ℝ) := by exact_mod_cast hd
    linarith
  have hnorm_prod : ‖β * μ_w⁻¹ * (q_w : ℂ) ^ (-(s_j : ℂ))‖ < 1 := by
    rw [norm_mul, norm_mul, norm_inv, hμ, inv_one, mul_one, hnorm_q]
    calc
      ‖β‖ * q_w ^ (-s_j)
          ≤ q_w ^ (((r : ℝ) - 1) / 2) * q_w ^ (-s_j) :=
            mul_le_mul_of_nonneg_right hβ (Real.rpow_nonneg hq_pos.le _)
      _ = q_w ^ (((r : ℝ) - 1) / 2 + (-s_j)) :=
            (Real.rpow_add hq_pos _ _).symm
      _ ≤ q_w ^ (-3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hq_ge1 hexp_le
      _ ≤ (2 : ℝ) ^ (-3 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
      _ < 1 := by norm_num
  intro hsub
  have heq : β * μ_w⁻¹ * (q_w : ℂ) ^ (-(s_j : ℂ)) = 1 := (sub_eq_zero.mp hsub).symm
  rw [heq, norm_one] at hnorm_prod
  exact lt_irrefl 1 hnorm_prod

/-- **Theorem 5.5 & Theorem 5.6 (Positive Scalar Adjoint Iteration & Upward Adjoint Injectivity)**:
Iterating the single-step Rallis/doubling adjoint formula across `m` stages `V_0 → V_1 → ⋯ → V_m`
with positive volume constants `a_j > 0` and non-vanishing step `L`-values `z_j ≠ 0` proves
`z_j > 0`, establishes the chain bilinear form identity `Θ(Θ*(x)) = (κ₀ ∏ z_j) • x` with
`κ₀ = ∏ a_j > 0`, and deduces upward injectivity of `Θ*`. -/
theorem thm_5_6_positive_scalar_adjoint_and_injectivity
    {m : ℕ}
    (Space : Fin (m + 1) → Type*)
    [∀ j : Fin (m + 1), AddCommGroup (Space j)]
    [∀ j : Fin (m + 1), Module ℂ (Space j)]
    (inner : ∀ j : Fin (m + 1), Space j → Space j → ℂ)
    (hinner_smul_left : ∀ (j : Fin m) (c : ℂ) (x y : Space j.castSucc),
      inner j.castSucc (c • x) y = c * inner j.castSucc x y)
    (hinner_pos : ∀ (j : Fin m) (x : Space j.castSucc), x ≠ 0 → 0 < (inner j.castSucc x x).re)
    (hinner_nonneg : ∀ (j : Fin m) (x : Space j.succ), 0 ≤ (inner j.succ x x).re)
    (θ : ∀ j : Fin m, Space j.succ →ₗ[ℂ] Space j.castSucc)
    (θ_star : ∀ j : Fin m, Space j.castSucc →ₗ[ℂ] Space j.succ)
    (hadj : ∀ (j : Fin m) (u : Space j.succ) (w : Space j.castSucc),
      inner j.castSucc (θ j u) w = inner j.succ u (θ_star j w))
    {Eig : Type*}
    (E : ∀ j : Fin (m + 1), Eig → Submodule ℂ (Space j))
    (hE_nonempty : ∀ c : Eig, ∃ w : Space 0, w ∈ E 0 c ∧ w ≠ 0)
    (hE_star_mem : ∀ (j : Fin m) (c : Eig) (w : Space j.castSucc),
      w ∈ E j.castSucc c → θ_star j w ∈ E j.succ c)
    (hE_star_ne : ∀ (j : Fin m) (c : Eig) (w : Space j.castSucc),
      w ∈ E j.castSucc c → w ≠ 0 → θ_star j w ≠ 0)
    (a z : Eig → Fin m → ℝ)
    (ha_pos : ∀ (c : Eig) (j : Fin m), 0 < a c j)
    (hz_ne : ∀ (c : Eig) (j : Fin m), z c j ≠ 0)
    (hstep : ∀ (j : Fin m) (c : Eig) (w : Space j.castSucc),
      w ∈ E j.castSucc c →
      θ j (θ_star j w) = ((a c j * z c j : ℝ) : ℂ) • w)
    (hspan : ∀ x : Space 0, ∃ (s : Finset Eig) (v : Eig → Space 0),
      (∀ c ∈ s, v c ∈ E 0 c) ∧ x = ∑ c ∈ s, v c)
    (hindep : ∀ (s : Finset Eig) (v : Eig → Space 0),
      (∀ c ∈ s, v c ∈ E 0 c) → (∑ c ∈ s, v c) = 0 → ∀ c ∈ s, v c = 0) :
    (∀ (c : Eig) (j : Fin m), 0 < z c j) ∧
    Function.Injective (iteratedStarLift Space θ_star m le_rfl) := by
  let liftStar := iteratedStarLift Space θ_star
  have hliftStar_zero : ∀ (hk : 0 ≤ m) (x : Space 0), liftStar 0 hk x = x :=
    fun _ _ => rfl
  have hliftStar_succ : ∀ (k : ℕ) (hk : k + 1 ≤ m) (x : Space 0),
      liftStar (k + 1) hk x = θ_star ⟨k, hk⟩ (liftStar k (Nat.le_of_lt hk) x) :=
    fun _ _ _ => rfl
  have hliftStar_mem : ∀ (k : ℕ) (hk : k ≤ m) (c : Eig) (x : Space 0),
      x ∈ E 0 c → liftStar k hk x ∈ E ⟨k, Nat.lt_succ_of_le hk⟩ c := by
    intro k
    induction k with
    | zero =>
      intro hk c x hx
      rw [hliftStar_zero]
      exact hx
    | succ k ih =>
      intro hk c x hx
      rw [hliftStar_succ]
      exact hE_star_mem ⟨k, hk⟩ c _ (ih (Nat.le_of_lt hk) c x hx)
  have hliftStar_ne : ∀ (k : ℕ) (hk : k ≤ m) (c : Eig) (x : Space 0),
      x ∈ E 0 c → x ≠ 0 → liftStar k hk x ≠ 0 := by
    intro k
    induction k with
    | zero =>
      intro hk c x _ hx_ne
      rw [hliftStar_zero]
      exact hx_ne
    | succ k ih =>
      intro hk c x hx hx_ne
      rw [hliftStar_succ]
      exact hE_star_ne ⟨k, hk⟩ c _
        (hliftStar_mem k (Nat.le_of_lt hk) c x hx)
        (ih (Nat.le_of_lt hk) c x hx hx_ne)
  -- Step 1: Positivity 0 < z c j for every stage j : Fin m
  have hz_pos : ∀ (c : Eig) (j : Fin m), 0 < z c j := by
    intro c j
    obtain ⟨w₀, hw₀_mem, hw₀_ne⟩ := hE_nonempty c
    let w_j : Space j.castSucc := liftStar j.1 (Nat.le_of_lt j.2) w₀
    have hw_j_mem : w_j ∈ E j.castSucc c :=
      hliftStar_mem j.1 (Nat.le_of_lt j.2) c w₀ hw₀_mem
    have hw_j_ne : w_j ≠ 0 :=
      hliftStar_ne j.1 (Nat.le_of_lt j.2) c w₀ hw₀_mem hw₀_ne
    exact lemma_5_6_step_scalar_positivity
      (inner j.castSucc) (inner j.succ)
      (hinner_smul_left j) (hinner_pos j) (hinner_nonneg j)
      (θ j) (θ_star j) (hadj j)
      (a c j) (z c j) (ha_pos c j) (hz_ne c j)
      w_j hw_j_ne (hstep j c w_j hw_j_mem)
  -- Step 2: Iterative bilinear identity across all m stages
  let Θ_down : ∀ (k : ℕ) (hk : k ≤ m), Space ⟨k, Nat.lt_succ_of_le hk⟩ →ₗ[ℂ] Space 0 :=
    Nat.rec
      (fun _ => LinearMap.id)
      (fun k ih hk => (ih (Nat.le_of_lt hk)).comp (θ ⟨k, hk⟩))
  have hΘ_down_zero : ∀ (hk : 0 ≤ m) (y : Space ⟨0, Nat.lt_succ_of_le hk⟩),
      Θ_down 0 hk y = y :=
    fun _ _ => rfl
  have hΘ_down_succ : ∀ (k : ℕ) (hk : k + 1 ≤ m)
      (y : Space ⟨k + 1, Nat.lt_succ_of_le hk⟩),
      Θ_down (k + 1) hk y = Θ_down k (Nat.le_of_lt hk) (θ ⟨k, hk⟩ y) :=
    fun _ _ _ => rfl
  have hΘ_iter : ∀ (k : ℕ) (hk : k ≤ m) (c : Eig) (x : Space 0),
      x ∈ E 0 c →
      Θ_down k hk (liftStar k hk x) =
        ((∏ i : Fin k, a c (Fin.castLE hk i) * z c (Fin.castLE hk i) : ℝ) : ℂ) • x := by
    intro k
    induction k with
    | zero =>
      intro hk c x _
      rw [hΘ_down_zero, hliftStar_zero]
      simp
    | succ k ih =>
      intro hk c x hx
      let j : Fin m := ⟨k, hk⟩
      have hk_le : k ≤ m := Nat.le_of_lt hk
      have hmem_k : liftStar k hk_le x ∈ E j.castSucc c :=
        hliftStar_mem k hk_le c x hx
      have hstep_k : θ j (θ_star j (liftStar k hk_le x)) =
          ((a c j * z c j : ℝ) : ℂ) • liftStar k hk_le x :=
        hstep j c (liftStar k hk_le x) hmem_k
      rw [hΘ_down_succ, hliftStar_succ]
      change Θ_down k hk_le (θ j (θ_star j (liftStar k hk_le x))) = _
      rw [hstep_k, map_smul, ih hk_le c x hx, smul_smul]
      congr 1
      have hprod_split :
          (∏ i : Fin (k + 1), a c (Fin.castLE hk i) * z c (Fin.castLE hk i)) =
          (∏ i : Fin k, a c (Fin.castLE hk_le i) * z c (Fin.castLE hk_le i)) *
            (a c j * z c j) := by
        rw [Fin.prod_univ_castSucc]
        rfl
      rw [hprod_split]
      push_cast
      ring
  -- Step 3: Upward injectivity of liftStar m le_rfl via LinearMap.ker_eq_bot
  refine ⟨hz_pos, ?_⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h0 : Θ_down m le_rfl (liftStar m le_rfl x) = 0 := by
    rw [hx, map_zero]
  obtain ⟨s, v, hv_mem, hx_sum⟩ := hspan x
  rw [hx_sum, map_sum, map_sum] at h0
  have hterm : ∑ c ∈ s,
      ((∏ i : Fin m, a c (Fin.castLE le_rfl i) * z c (Fin.castLE le_rfl i) : ℝ) : ℂ) • v c = 0 := by
    refine Eq.trans ?_ h0
    refine Finset.sum_congr rfl fun c hc => ?_
    exact (hΘ_iter m le_rfl c (v c) (hv_mem c hc)).symm
  have hall_zero : ∀ c ∈ s,
      ((∏ i : Fin m, a c (Fin.castLE le_rfl i) * z c (Fin.castLE le_rfl i) : ℝ) : ℂ) • v c = 0 :=
    hindep s _ (fun c hc => Submodule.smul_mem _ _ (hv_mem c hc)) hterm
  have hx0 : x = 0 := by
    rw [hx_sum]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hsc_pos : 0 < ∏ i : Fin m, a c (Fin.castLE le_rfl i) * z c (Fin.castLE le_rfl i) :=
      Finset.prod_pos fun i _ =>
        mul_pos (ha_pos c (Fin.castLE le_rfl i)) (hz_pos c (Fin.castLE le_rfl i))
    exact (smul_eq_zero.mp (hall_zero c hc)).resolve_left
      (Complex.ofReal_ne_zero.mpr hsc_pos.ne')
  rw [hx0]
  exact Submodule.zero_mem ⊥

/-- **Theorem 5.6 Concrete Unitary Tower Specialization**:
Instantiates `thm_5_6_positive_scalar_adjoint_and_injectivity` on an `(m + 1)`-stage
compact unitary quotient tower `Q : Fin (m + 1) → CompactUnitaryQuotient` with
single-step theta kernels `kernel j`, proving `z c j > 0` and injectivity of the
upward iterated theta lift without any abstract inner-product hypotheses. -/
theorem thm_5_6_unitary_tower_adjoint_injective
    {m : ℕ}
    (Q : Fin (m + 1) → CompactUnitaryQuotient)
    (kernel : ∀ j : Fin m, (Q j.succ).QuotPt → (Q j.castSucc).QuotPt → ℂ)
    {Eig : Type*}
    (E : ∀ j : Fin (m + 1), Eig → Submodule ℂ (AutomorphicFormSpace (Q j)))
    (hE_nonempty : ∀ c : Eig, ∃ w : AutomorphicFormSpace (Q 0), w ∈ E 0 c ∧ w ≠ 0)
    (hE_star_mem : ∀ (j : Fin m) (c : Eig) (w : AutomorphicFormSpace (Q j.castSucc)),
      w ∈ E j.castSucc c →
      thetaKernelAdjoint (Q j.succ) (Q j.castSucc) (kernel j) w ∈ E j.succ c)
    (hE_star_ne : ∀ (j : Fin m) (c : Eig) (w : AutomorphicFormSpace (Q j.castSucc)),
      w ∈ E j.castSucc c → w ≠ 0 →
      thetaKernelAdjoint (Q j.succ) (Q j.castSucc) (kernel j) w ≠ 0)
    (a z : Eig → Fin m → ℝ)
    (ha_pos : ∀ (c : Eig) (j : Fin m), 0 < a c j)
    (hz_ne : ∀ (c : Eig) (j : Fin m), z c j ≠ 0)
    (hstep : ∀ (j : Fin m) (c : Eig) (w : AutomorphicFormSpace (Q j.castSucc)),
      w ∈ E j.castSucc c →
      thetaKernelLift (Q j.succ) (Q j.castSucc) (kernel j)
        (thetaKernelAdjoint (Q j.succ) (Q j.castSucc) (kernel j) w) =
        ((a c j * z c j : ℝ) : ℂ) • w)
    (hspan : ∀ x : AutomorphicFormSpace (Q 0),
      ∃ (s : Finset Eig) (v : Eig → AutomorphicFormSpace (Q 0)),
        (∀ c ∈ s, v c ∈ E 0 c) ∧ x = ∑ c ∈ s, v c)
    (hindep : ∀ (s : Finset Eig) (v : Eig → AutomorphicFormSpace (Q 0)),
      (∀ c ∈ s, v c ∈ E 0 c) → (∑ c ∈ s, v c) = 0 → ∀ c ∈ s, v c = 0) :
    (∀ (c : Eig) (j : Fin m), 0 < z c j) ∧
    Function.Injective
      (iteratedStarLift (fun j => AutomorphicFormSpace (Q j))
        (fun j => thetaKernelAdjoint (Q j.succ) (Q j.castSucc) (kernel j)) m le_rfl) :=
  thm_5_6_positive_scalar_adjoint_and_injectivity
    (fun j => AutomorphicFormSpace (Q j))
    (fun j => peterssonInner (Q j))
    (fun j => peterssonInner_smul_left (Q j.castSucc))
    (fun j => peterssonInner_pos (Q j.castSucc))
    (fun j => peterssonInner_nonneg (Q j.succ))
    (fun j => thetaKernelLift (Q j.succ) (Q j.castSucc) (kernel j))
    (fun j => thetaKernelAdjoint (Q j.succ) (Q j.castSucc) (kernel j))
    (fun j u w => (thetaKernelLift_adjoint (Q j.succ) (Q j.castSucc) (kernel j) u w).symm)
    E hE_nonempty hE_star_mem hE_star_ne a z ha_pos hz_ne hstep hspan hindep

/-! ## Subsection 5.2: Rallis Inner Product Formula and Seesaw Period Factorization -/

/-- **Theorem 5.7, Lemma 5.8, Lemma 5.9, and Theorem 5.10 (Seesaw Period Factorization)**:
Given the class-sum decomposition over `cl_T` and the archimedean branching factorization
`branchInt β d' = a * l_func β d'` where `a` is witnessed by a non-vanishing archimedean
test-vector period `branchInt β₀ d₀ ≠ 0`, we deduce `a ≠ 0` and factor the global Seesaw period. -/
theorem thm_5_10_seesaw_period_factorization
    {Beta ClT : Type*} (B_set : Finset Beta) (cl_T : Finset ClT)
    (vol_T : ℂ) (stab : ClT → ℂ) (l_func : Beta → ClT → ℂ)
    (branchInt : Beta → ClT → ℂ) (a : ℂ)
    (hbranch : ∀ β ∈ B_set, ∀ d' ∈ cl_T, branchInt β d' = a * l_func β d')
    (harch_test : ∃ β₀ ∈ B_set, ∃ d₀ ∈ cl_T, branchInt β₀ d₀ ≠ 0) :
    a ≠ 0 ∧
    (∑ β ∈ B_set, vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * branchInt β d') =
      a * vol_T * ∑ β ∈ B_set, ∑ d' ∈ cl_T, (stab d')⁻¹ * l_func β d' := by
  obtain ⟨β₀, hβ₀, d₀, hd₀, htest_ne⟩ := harch_test
  have ha : a ≠ 0 := by
    intro ha0
    apply htest_ne
    rw [hbranch β₀ hβ₀ d₀ hd₀, ha0, zero_mul]
  refine ⟨ha, ?_⟩
  have hinner : ∀ β ∈ B_set,
      vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * branchInt β d' =
        a * vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * l_func β d' := by
    intro β hβ
    calc
      vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * branchInt β d'
          = vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * (a * l_func β d') := by
              congr 1
              refine Finset.sum_congr rfl fun d' hd' => ?_
              rw [hbranch β hβ d' hd']
      _ = vol_T * (a * ∑ d' ∈ cl_T, (stab d')⁻¹ * l_func β d') := by
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d' _ => by ring
      _ = a * vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * l_func β d' := by ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

/-- **Theorem 5.10 Concrete Unitary Seesaw Specialization**:
Instantiates `thm_5_10_seesaw_period_factorization` for concrete stabilizer cardinalities
`stabCard : ClT → ℕ` (`stabCard d' ≥ 1`) and positive torus volume `vol_T : ℝ` (`vol_T > 0`),
yielding `a * vol_T ≠ 0` along with the factored global Seesaw period identity. -/
theorem thm_5_10_unitary_seesaw_period_factorization
    {Beta ClT : Type*} (B_set : Finset Beta) (cl_T : Finset ClT)
    (vol_T : ℝ) (hvol : 0 < vol_T)
    (stabCard : ClT → ℕ)
    (l_func : Beta → ClT → ℂ)
    (branchInt : Beta → ClT → ℂ) (a : ℂ)
    (hbranch : ∀ β ∈ B_set, ∀ d' ∈ cl_T, branchInt β d' = a * l_func β d')
    (harch_test : ∃ β₀ ∈ B_set, ∃ d₀ ∈ cl_T, branchInt β₀ d₀ ≠ 0) :
    a * (vol_T : ℂ) ≠ 0 ∧
    (∑ β ∈ B_set, (vol_T : ℂ) * ∑ d' ∈ cl_T, ((stabCard d' : ℂ))⁻¹ * branchInt β d') =
      a * (vol_T : ℂ) * ∑ β ∈ B_set, ∑ d' ∈ cl_T, ((stabCard d' : ℂ))⁻¹ * l_func β d' := by
  obtain ⟨ha, hfac⟩ := thm_5_10_seesaw_period_factorization
    B_set cl_T (vol_T : ℂ) (fun d' => (stabCard d' : ℂ)) l_func branchInt a hbranch harch_test
  exact ⟨mul_ne_zero ha (Complex.ofReal_ne_zero.mpr hvol.ne'), hfac⟩

/--
If non-zero automorphic forms `x ∈ s` on a `CompactUnitaryQuotient Q` carry pairwise separated
Satake parameter families `lbl x` at good places where unramified Hecke operators are normal,
making distinct eigenforms Petersson-orthogonal (`⟨x, x'⟩ = 0` for `x ≠ x'`), then they are
unconditionally `ℂ`-linearly independent. -/
theorem linearIndependent_of_petersson_orthogonal
    (Q : CompactUnitaryQuotient)
    (s : Finset (AutomorphicFormSpace Q))
    (hne_zero : ∀ x ∈ s, x ≠ 0)
    (horth : ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → peterssonInner Q x x' = 0) :
    LinearIndependent ℂ (fun x : s => (x : AutomorphicFormSpace Q)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  have hinner : peterssonInner Q (∑ i : s, c i • (i : AutomorphicFormSpace Q))
      (i₀ : AutomorphicFormSpace Q) = 0 := by
    rw [hc]
    unfold peterssonInner
    simp
  have hsum_left : ∀ (t : Finset s) (g : s → AutomorphicFormSpace Q) (w : AutomorphicFormSpace Q),
      peterssonInner Q (∑ i ∈ t, g i) w = ∑ i ∈ t, peterssonInner Q (g i) w := by
    intro t g w
    classical
    induction t using Finset.induction_on with
    | empty =>
      unfold peterssonInner
      simp
    | insert a u ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, peterssonInner_add_left, ih]
  rw [hsum_left] at hinner
  have hsingle : (∑ i : s, peterssonInner Q (c i • (i : AutomorphicFormSpace Q))
      (i₀ : AutomorphicFormSpace Q)) =
      c i₀ * peterssonInner Q (i₀ : AutomorphicFormSpace Q) (i₀ : AutomorphicFormSpace Q) := by
    rw [Finset.sum_eq_single i₀]
    · exact peterssonInner_smul_left Q (c i₀) _ _
    · intro i _ hne
      rw [peterssonInner_smul_left, horth i.1 i.2 i₀.1 i₀.2 (Subtype.coe_ne_coe.mpr hne), mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ i₀))
  rw [hsingle] at hinner
  have hpos_re : 0 < (peterssonInner Q (i₀ : AutomorphicFormSpace Q)
      (i₀ : AutomorphicFormSpace Q)).re :=
    peterssonInner_pos Q i₀.1 (hne_zero i₀.1 i₀.2)
  have hne0 : peterssonInner Q (i₀ : AutomorphicFormSpace Q) (i₀ : AutomorphicFormSpace Q) ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hpos_re
    exact lt_irrefl 0 hpos_re
  exact (mul_eq_zero.mp hinner).resolve_right hne0

end GRHIteratedThetaLifts.Section5
