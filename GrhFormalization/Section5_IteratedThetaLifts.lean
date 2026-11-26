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
import Mathlib.Basic.Complex.Basic
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

/-! ## Subsection 5.1: Adjoint-Separation Surjectivity & Upward Injectivity -/

/-- **Lemma 5.1 & Theorem 5.3 (Surjectivity of the Iterated Theta Lift from Adjoint Non-Vanishing)**:
If `A` is finite-dimensional over `ℂ` with a Hermitian inner product, `C` carries a
positive-definite Hermitian inner product, `A` is spanned by labelled vectors whose
transported labels under `Θ*` yield `ℂ`-linearly independent elements in `C`, then
`Θ : C →ₗ[ℂ] A` is surjective. -/
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
  -- Step 2: Surjectivity via complement subspace of strictly larger finrank
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

/-- **Theorem 5.5 & Theorem 5.6 (Upward Adjoint Injectivity from the Chain Bilinear Form)**:
If `H` is spanned by eigenspaces `E(c)` on each of which `Θ(Θ*(x)) = (κ₀ ∏ z_i) x` with
`κ₀ > 0` and `z_i > 0`, and distinct eigenspaces are linearly independent, then `Θ*` is
injective. -/
theorem thm_5_6_upward_adjoint_injectivity
    {H V Eig : Type*}
    [AddCommGroup H] [Module ℂ H]
    [AddCommGroup V] [Module ℂ V]
    (Θ : V →ₗ[ℂ] H) (Θ_star : H →ₗ[ℂ] V)
    (E : Eig → Submodule ℂ H)
    (κ₀ : ℝ) (hκ₀ : 0 < κ₀)
    (z : Eig → ℕ → ℝ) (m : ℕ)
    (hz_pos : ∀ c : Eig, ∀ i ∈ Finset.range m, 0 < z c i)
    (hbilinear : ∀ (c : Eig) (x : H), x ∈ E c →
      Θ (Θ_star x) = ((κ₀ * ∏ i ∈ Finset.range m, z c i : ℝ) : ℂ) • x)
    (hspan : ∀ x : H, ∃ (s : Finset Eig) (v : Eig → H),
      (∀ c ∈ s, v c ∈ E c) ∧ x = ∑ c ∈ s, v c)
    (hindep : ∀ (s : Finset Eig) (v : Eig → H),
      (∀ c ∈ s, v c ∈ E c) → (∑ c ∈ s, v c) = 0 → ∀ c ∈ s, v c = 0) :
    Function.Injective Θ_star := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨s, v, hv_mem, hx_sum⟩ := hspan x
  have hΘ_zero : Θ (Θ_star x) = 0 := by rw [hx, map_zero]
  rw [hx_sum, map_sum, map_sum] at hΘ_zero
  have hterm : ∑ c ∈ s,
      ((κ₀ * ∏ i ∈ Finset.range m, z c i : ℝ) : ℂ) • v c = 0 := by
    refine Eq.trans ?_ hΘ_zero
    refine Finset.sum_congr rfl fun c hc => ?_
    exact (hbilinear c (v c) (hv_mem c hc)).symm
  have hall_zero : ∀ c ∈ s,
      ((κ₀ * ∏ i ∈ Finset.range m, z c i : ℝ) : ℂ) • v c = 0 :=
    hindep s (fun c => ((κ₀ * ∏ i ∈ Finset.range m, z c i : ℝ) : ℂ) • v c)
      (fun c hc => (E c).smul_mem _ (hv_mem c hc)) hterm
  have hx0 : x = 0 := by
    rw [hx_sum]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hsc_pos : 0 < κ₀ * ∏ i ∈ Finset.range m, z c i :=
      mul_pos hκ₀ (Finset.prod_pos (hz_pos c))
    have hsc_ne : ((κ₀ * ∏ i ∈ Finset.range m, z c i : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hsc_pos)
    exact (smul_eq_zero.mp (hall_zero c hc)).resolve_left hsc_ne
  rw [hx0]
  exact Submodule.zero_mem ⊥

/-! ## Subsection 5.2: Rallis Inner Product Formula and Seesaw Period Factorization -/

/-- **Theorem 5.7, Lemma 5.8, Lemma 5.9, and Theorem 5.10 (Seesaw Period Factorization)**:
Given the class-sum decomposition over `cl_T` and the archimedean branching factorization
with universal non-zero scalar `a ∈ ℂˣ`, the global Seesaw period factors with `a ≠ 0`. -/
theorem thm_5_10_seesaw_period_factorization
    {Beta ClT : Type*} (B_set : Finset Beta) (cl_T : Finset ClT)
    (vol_T : ℂ) (stab : ClT → ℂ) (l_func : Beta → ClT → ℂ)
    (branchInt : Beta → ClT → ℂ) (a : ℂ) (ha : a ≠ 0)
    (hbranch : ∀ β ∈ B_set, ∀ d' ∈ cl_T, branchInt β d' = a * l_func β d') :
    a ≠ 0 ∧
    (∑ β ∈ B_set, vol_T * ∑ d' ∈ cl_T, (stab d')⁻¹ * branchInt β d') =
      a * vol_T * ∑ β ∈ B_set, ∑ d' ∈ cl_T, (stab d')⁻¹ * l_func β d' := by
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

end GRHIteratedThetaLifts.Section5
