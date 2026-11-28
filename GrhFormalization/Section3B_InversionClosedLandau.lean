/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/
import GrhFormalization.Section3A_LandauPositivity
import GrhFormalization.Section3_LandauTauberian
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.HurwitzZeta

open Complex Real Filter Topology MeasureTheory Set
open scoped BigOperators ENNReal NNReal ArithmeticFunction.vonMangoldt

namespace GRHIteratedThetaLifts.Section3B

open GRHIteratedThetaLifts.Section1
open GRHIteratedThetaLifts.Section3
open GRHIteratedThetaLifts.Section3A

/-! ## Part 1: Desingularized Entire Product P(s) for $\{\zeta\} \cup \{\psi_\xi : \xi \in S\}$ -/

/-- Desingularized Riemann zeta factor `(s - 1) * ζ(s)`, extended by `1` at `s = 1`. -/
noncomputable def zetaDesing : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

lemma zetaDesing_eq_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    zetaDesing s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

lemma zetaDesing_one : zetaDesing 1 = 1 :=
  Function.update_self _ _ _

/-- `zetaDesing` is entire on `ℂ` via removable singularity at `s = 1` (`riemannZeta_residue_one`). -/
theorem differentiable_zetaDesing : Differentiable ℂ zetaDesing := by
  rw [← differentiableOn_univ]
  have hlim : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (𝓝 1) :=
    riemannZeta_residue_one
  have hdiff_punct : DifferentiableOn ℂ (fun s : ℂ => (s - 1) * riemannZeta s) (univ \ {(1 : ℂ)}) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    exact ((differentiable_id.sub (differentiable_const 1)) s).differentiableWithinAt.mul
      (differentiableAt_riemannZeta hs1).differentiableWithinAt
  have hlo : ((fun s : ℂ => (s - 1) * riemannZeta s - (1 - 1) * riemannZeta 1)
      =o[nhdsWithin 1 {1}ᶜ] fun s : ℂ => (s - 1)⁻¹) := by
    simp only [sub_self, zero_mul, sub_zero]
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have hmul : Tendsto
          (fun s : ℂ => ((s - 1) * riemannZeta s) * (s - 1))
          (nhdsWithin 1 {1}ᶜ) (𝓝 (1 * (1 - 1))) :=
        hlim.mul ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      simp only [sub_self, mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s _
      rw [div_inv_eq_mul]
    · filter_upwards [self_mem_nhdsWithin] with s hs hinv
      exfalso
      exact inv_ne_zero (sub_ne_zero.mpr hs) hinv
  have hlim_under : (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ).limUnder
      (fun s : ℂ => (s - 1) * riemannZeta s) = 1 :=
    hlim.limUnder_eq
  have hupd := Complex.differentiableOn_update_limUnder_of_isLittleO
    (univ_mem : (univ : Set ℂ) ∈ 𝓝 (1 : ℂ)) hdiff_punct hlo
  rw [hlim_under] at hupd
  exact hupd

/-- `zetaDesing s ≠ 0` for all `Re(s) ≥ 1`. -/
theorem zetaDesing_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : zetaDesing s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; rw [zetaDesing_one]; exact one_ne_zero
  · rw [zetaDesing_eq_of_ne_one hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs)

private lemma differentiable_finset_prod {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ ξ ∈ S, Differentiable ℂ (f ξ)) :
    Differentiable ℂ (fun z : ℂ => ∏ ξ ∈ S, f ξ z) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using differentiable_const (1 : ℂ)
  | insert a s ha ih =>
    have h1 : Differentiable ℂ (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : Differentiable ℂ (fun z => ∏ ξ ∈ s, f ξ z) :=
      ih (fun ξ hξ => hf ξ (Finset.mem_insert_of_mem hξ))
    have hmul : Differentiable ℂ (fun z => f a z * ∏ ξ ∈ s, f ξ z) := h1.mul h2
    have heq : (fun z : ℂ => ∏ ξ ∈ insert a s, f ξ z) = fun z => f a z * ∏ ξ ∈ s, f ξ z := by
      ext z; exact Finset.prod_insert ha
    rwa [heq]

private lemma differentiableAt_finset_prod {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (hf : ∀ ξ ∈ S, DifferentiableAt ℂ (f ξ) s) :
    DifferentiableAt ℂ (fun z : ℂ => ∏ ξ ∈ S, f ξ z) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using differentiableAt_const (1 : ℂ)
  | insert a u ha ih =>
    have h1 : DifferentiableAt ℂ (f a) s := hf a (Finset.mem_insert_self a u)
    have h2 : DifferentiableAt ℂ (fun z => ∏ ξ ∈ u, f ξ z) s :=
      ih (fun ξ hξ => hf ξ (Finset.mem_insert_of_mem hξ))
    have hmul : DifferentiableAt ℂ (fun z => f a z * ∏ ξ ∈ u, f ξ z) s := h1.mul h2
    have heq : (fun z : ℂ => ∏ ξ ∈ insert a u, f ξ z) = fun z => f a z * ∏ ξ ∈ u, f ξ z := by
      ext z; exact Finset.prod_insert ha
    rwa [heq]

private lemma deriv_finset_prod_div {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (hf : ∀ ξ ∈ S, DifferentiableAt ℂ (f ξ) s)
    (hne : ∀ ξ ∈ S, f ξ s ≠ 0) :
    deriv (fun z : ℂ => ∏ ξ ∈ S, f ξ z) s / (∏ ξ ∈ S, f ξ s) =
      ∑ ξ ∈ S, deriv (f ξ) s / f ξ s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    have hfa_diff : DifferentiableAt ℂ (f a) s := hf a (Finset.mem_insert_self a u)
    have hprod_diff : DifferentiableAt ℂ (fun z => ∏ ξ ∈ u, f ξ z) s :=
      differentiableAt_finset_prod u f s (fun ξ hξ => hf ξ (Finset.mem_insert_of_mem hξ))
    have hfa_ne : f a s ≠ 0 := hne a (Finset.mem_insert_self a u)
    have hprod_ne : (∏ ξ ∈ u, f ξ s) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ξ hξ => hne ξ (Finset.mem_insert_of_mem hξ)
    have hfn_eq : (fun z : ℂ => ∏ ξ ∈ insert a u, f ξ z) =
        fun z => f a z * ∏ ξ ∈ u, f ξ z := by
      ext z; exact Finset.prod_insert ha
    rw [hfn_eq, deriv_fun_mul hfa_diff hprod_diff, Finset.prod_insert ha, Finset.sum_insert ha,
      ← ih (fun ξ hξ => hf ξ (Finset.mem_insert_of_mem hξ))
          (fun ξ hξ => hne ξ (Finset.mem_insert_of_mem hξ))]
    field_simp [hfa_ne, hprod_ne]

/-- Desingularized family product `P(s) = ((s - 1) ζ(s))^R * ∏_{ξ ∈ S} L(s, ψ_ξ)`. -/
noncomputable def familyEntireProduct {ι : Type} (S : Finset ι) (ψ : ι → PrimitiveChar) (R : ℕ)
    (s : ℂ) : ℂ :=
  zetaDesing s ^ R * ∏ ξ ∈ S, DirichletCharacter.LFunction (ψ ξ).char s

/-- `familyEntireProduct` is entire when every `ψ ξ` is non-principal. -/
theorem differentiable_familyEntireProduct {ι : Type} (S : Finset ι) (ψ : ι → PrimitiveChar) (R : ℕ)
    (hnonprin : ∀ ξ ∈ S, (ψ ξ).char ≠ 1) :
    Differentiable ℂ (familyEntireProduct S ψ R) := by
  unfold familyEntireProduct
  exact (differentiable_zetaDesing.pow R).mul
    (differentiable_finset_prod S _ fun ξ hξ => DirichletCharacter.differentiable_LFunction (hnonprin ξ hξ))

/-- `familyEntireProduct` is non-vanishing on `Re(s) ≥ 1`. -/
theorem familyEntireProduct_ne_zero_of_one_le_re {ι : Type} (S : Finset ι) (ψ : ι → PrimitiveChar)
    (R : ℕ) (hnonprin : ∀ ξ ∈ S, (ψ ξ).char ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    familyEntireProduct S ψ R s ≠ 0 := by
  unfold familyEntireProduct
  refine mul_ne_zero (pow_ne_zero R (zetaDesing_ne_zero_of_one_le_re hs)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro ξ hξ
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (ψ ξ).char (Or.inl (hnonprin ξ hξ)) hs

/-- Logarithmic derivative of `familyEntireProduct` for `1 < s.re`. -/
theorem logDeriv_familyEntireProduct_of_one_lt_re
    {ι : Type} (S : Finset ι) (ψ : ι → PrimitiveChar) (R : ℕ)
    (hnonprin : ∀ ξ ∈ S, (ψ ξ).char ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    deriv (familyEntireProduct S ψ R) s / familyEntireProduct S ψ R s =
      (R : ℂ) * ((1 : ℂ) / (s - 1) + deriv riemannZeta s / riemannZeta s) +
        ∑ ξ ∈ S, deriv (DirichletCharacter.LFunction (ψ ξ).char) s /
          DirichletCharacter.LFunction (ψ ξ).char s := by
  have hs1 : s ≠ 1 := by
    intro h1; rw [h1, one_re] at hs; exact lt_irrefl 1 hs
  have hs_sub1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hzeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hzd_ne : zetaDesing s ≠ 0 := zetaDesing_ne_zero_of_one_le_re hs.le
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hzd_eq : EqOn zetaDesing (fun z : ℂ => (z - 1) * riemannZeta z) {z : ℂ | z ≠ 1} :=
    fun z hz => zetaDesing_eq_of_ne_one hz
  have hzd_deriv : deriv zetaDesing s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [Filter.EventuallyEq.deriv_eq (hzd_eq.eventuallyEq_of_mem (hopen.mem_nhds hs1))]
    have hd : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs1).hasDerivAt
    simpa [one_mul] using hd.deriv
  have hzd_logDeriv : deriv zetaDesing s / zetaDesing s =
      (1 : ℂ) / (s - 1) + deriv riemannZeta s / riemannZeta s := by
    rw [hzd_deriv, zetaDesing_eq_of_ne_one hs1]
    field_simp [hs_sub1, hzeta_ne]
  let F_pow : ℂ → ℂ := fun z => zetaDesing z ^ R
  let F_prod : ℂ → ℂ := fun z => ∏ ξ ∈ S, DirichletCharacter.LFunction (ψ ξ).char z
  have hF_pow_diff : DifferentiableAt ℂ F_pow s := (differentiable_zetaDesing.pow R) s
  have hF_prod_diff : DifferentiableAt ℂ F_prod s :=
    differentiableAt_finset_prod S _ s fun ξ hξ => DirichletCharacter.differentiable_LFunction (hnonprin ξ hξ) s
  have hF_pow_ne : F_pow s ≠ 0 := pow_ne_zero R hzd_ne
  have hF_prod_ne : F_prod s ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ξ hξ
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (ψ ξ).char (Or.inl (hnonprin ξ hξ)) hs.le
  have hd_prod_rule : deriv (familyEntireProduct S ψ R) s =
      deriv F_pow s * F_prod s + F_pow s * deriv F_prod s := by
    change deriv (fun z => F_pow z * F_prod z) s = deriv F_pow s * F_prod s + F_pow s * deriv F_prod s
    exact deriv_fun_mul hF_pow_diff hF_prod_diff
  have hd_pow_rule : deriv F_pow s = (R : ℂ) * zetaDesing s ^ (R - 1) * deriv zetaDesing s := by
    have hd : HasDerivAt (fun z => zetaDesing z ^ R)
        ((R : ℂ) * zetaDesing s ^ (R - 1) * deriv zetaDesing s) s :=
      (differentiable_zetaDesing s).hasDerivAt.pow R
    exact hd.deriv
  have hd_finset_rule : deriv F_prod s / F_prod s =
      ∑ ξ ∈ S, deriv (DirichletCharacter.LFunction (ψ ξ).char) s /
        DirichletCharacter.LFunction (ψ ξ).char s :=
    deriv_finset_prod_div S _ s
      (fun ξ hξ => DirichletCharacter.differentiable_LFunction (hnonprin ξ hξ) s)
      (fun ξ hξ => DirichletCharacter.LFunction_ne_zero_of_one_le_re (ψ ξ).char (Or.inl (hnonprin ξ hξ)) hs.le)
  have h_split_logDeriv : deriv (familyEntireProduct S ψ R) s / familyEntireProduct S ψ R s =
      deriv F_pow s / F_pow s + deriv F_prod s / F_prod s := by
    change deriv (familyEntireProduct S ψ R) s / (F_pow s * F_prod s) = _
    rw [hd_prod_rule]
    field_simp [hF_pow_ne, hF_prod_ne]
  rw [h_split_logDeriv, hd_finset_rule]
  congr 1
  rw [hd_pow_rule]
  dsimp [F_pow]
  by_cases hR0 : R = 0
  · subst hR0; simp
  · have hR_split : zetaDesing s ^ R = zetaDesing s * zetaDesing s ^ (R - 1) := by
      cases R with
      | zero => contradiction
      | succ k => simp [pow_succ']
    rw [hR_split]
    have hzd_pow_ne : zetaDesing s ^ (R - 1) ≠ 0 := pow_ne_zero (R - 1) hzd_ne
    calc
      (R : ℂ) * zetaDesing s ^ (R - 1) * deriv zetaDesing s / (zetaDesing s * zetaDesing s ^ (R - 1))
          = (R : ℂ) * (deriv zetaDesing s / zetaDesing s) := by
            field_simp [hzd_ne, hzd_pow_ne]
      _ = (R : ℂ) * ((1 : ℂ) / (s - 1) + deriv riemannZeta s / riemannZeta s) := by
            rw [hzd_logDeriv]

/-! ## Part 2A: Smoothed Kernel Mellin Identities & Dirichlet Series Interchange -/

/-- Helper to rewrite `IntegrableOn` along `EqOn` on a measurable set. -/
private lemma integrableOn_congr_eqOn {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : IntegrableOn f s) (hfg : EqOn f g s) :
    IntegrableOn g s :=
  hf.congr ((ae_restrict_iff' hs).mpr (Eventually.of_forall hfg))

/-- Improper integral of `x ^ w` on `Ioi c` for `c > 0` and `w.re < -1`. -/
lemma integral_Ioi_ofReal_cpow {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w.re < -1) :
    ∫ x in Ioi c, (x : ℂ) ^ w = -(c : ℂ) ^ (w + 1) / (w + 1) :=
  integral_Ioi_cpow_of_lt hw hc

/-- Elementary Mellin transform of the tent kernel `max (x / n - 1) 0` on `Ioi 1` for `n ≥ 1`
and `1 < s.re`: `∫_{x > 1} max (x / n - 1) 0 * x ^ (-s - 1) dx = n ^ (-s) / (s * (s - 1))`. -/
lemma integral_smoothed_tent_kernel {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0, zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h1; have := congrArg Complex.re (sub_eq_zero.mp h1); rw [one_re] at this; linarith
  have hw1_re : (-s).re < -1 := by rw [neg_re]; linarith
  have hw2_re : (-s - 1).re < -1 := by rw [sub_re, neg_re, one_re]; linarith
  have hint1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi (n : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hw1_re hn_pos
  have hint2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hw2_re hn_pos
  have hsplit_union : Ioi (1 : ℝ) = Ioc (1 : ℝ) (n : ℝ) ∪ Ioi (n : ℝ) :=
    (Ioc_union_Ioi_eq_Ioi hn_ge1).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) (n : ℝ)) (Ioi (n : ℝ)) := Ioc_disjoint_Ioi_same
  have hint_Ioi_n : IntegrableOn
      (fun x : ℝ => ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := by
    refine integrableOn_congr_eqOn measurableSet_Ioi ((hint1.const_mul ((n : ℂ)⁻¹)).sub hint2) ?_
    intro x hx
    dsimp only [Pi.sub_apply]
    have hx_gt_n : (n : ℝ) < x := hx
    have hx_pos : 0 < x := lt_trans hn_pos hx_gt_n
    have hmax : max (x / (n : ℝ) - 1) 0 = x / (n : ℝ) - 1 := by
      refine max_eq_left ?_
      rw [sub_nonneg, le_div_iff₀ hn_pos]
      linarith
    rw [hmax]
    push_cast
    have hcpow : (x : ℂ) ^ (-s) = (x : ℂ) * (x : ℂ) ^ (-s - 1) := by
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
      have hexp : (-s) = 1 + (-s - 1) := by ring
      conv_lhs => rw [hexp, Complex.cpow_add _ _ hx_ne, Complex.cpow_one]
    rw [hcpow]
    ring
  have hint_Ioc : IntegrableOn
      (fun x : ℝ => ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioc (1 : ℝ) (n : ℝ)) := by
    refine integrableOn_congr_eqOn measurableSet_Ioc
      (integrableOn_zero (μ := volume) (s := Ioc (1 : ℝ) (n : ℝ))) ?_
    intro x hx
    dsimp only
    have hmax : max (x / (n : ℝ) - 1) 0 = 0 := by
      refine max_eq_right ?_
      rw [sub_nonpos, div_le_one hn_pos]
      exact hx.2
    rw [hmax, Complex.ofReal_zero, zero_mul]
  rw [hsplit_union, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_Ioi_n]
  have hIoc_zero :
      ∫ x in Ioc (1 : ℝ) (n : ℝ), ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 0 := by
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hmax : max (x / (n : ℝ) - 1) 0 = 0 := by
      refine max_eq_right ?_
      rw [sub_nonpos, div_le_one hn_pos]
      exact hx.2
    rw [hmax, Complex.ofReal_zero, zero_mul]
  rw [hIoc_zero, zero_add]
  have heq_Ioi_n : EqOn
      (fun x : ℝ => ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => ((n : ℂ)⁻¹) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := by
    intro x hx
    dsimp only
    have hx_pos : 0 < x := lt_trans hn_pos hx
    have hmax : max (x / (n : ℝ) - 1) 0 = x / (n : ℝ) - 1 := by
      refine max_eq_left ?_
      rw [sub_nonneg, le_div_iff₀ hn_pos]
      linarith [show (n : ℝ) < x from hx]
    rw [hmax]
    push_cast
    have hcpow : (x : ℂ) ^ (-s) = (x : ℂ) * (x : ℂ) ^ (-s - 1) := by
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
      have hexp : (-s) = 1 + (-s - 1) := by ring
      conv_lhs => rw [hexp, Complex.cpow_add _ _ hx_ne, Complex.cpow_one]
    rw [hcpow]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq_Ioi_n,
    MeasureTheory.integral_sub (hint1.const_mul ((n : ℂ)⁻¹)) hint2,
    MeasureTheory.integral_const_mul,
    integral_Ioi_ofReal_cpow hn_pos hw1_re,
    integral_Ioi_ofReal_cpow hn_pos hw2_re,
    Complex.ofReal_natCast]
  have hpow_split : (n : ℂ) ^ (-s + 1) = (n : ℂ) * (n : ℂ) ^ (-s) := by
    have hexp : (-s + 1) = 1 + (-s) := by ring
    rw [hexp, Complex.cpow_add _ _ hn_ne, Complex.cpow_one]
  have hpow_split' : (n : ℂ) ^ (-s - 1 + 1) = (n : ℂ) ^ (-s) := by
    congr 1; ring
  rw [hpow_split, hpow_split']
  have hden1 : -s + 1 = -(s - 1) := by ring
  have hden2 : -s - 1 + 1 = -s := by ring
  rw [hden1, hden2]
  field_simp [hn_ne, hs0, hs1]
  ring

private lemma real_integral_smoothed_tent_kernel {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    ∫ x in Ioi (1 : ℝ), max (x / (n : ℝ) - 1) 0 * x ^ (-σ - 1) =
      (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hc := integral_smoothed_tent_kernel hn (show 1 < (σ : ℂ).re by simpa using hσ)
  have hcongr : ∫ x in Ioi (1 : ℝ),
      ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ x in Ioi (1 : ℝ), max (x / (n : ℝ) - 1) 0 * x ^ (-σ - 1) : ℝ) : ℂ) := by
    have heq : EqOn
        (fun x : ℝ => ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1))
        (fun x : ℝ => ((max (x / (n : ℝ) - 1) 0 * x ^ (-σ - 1) : ℝ) : ℂ))
        (Ioi (1 : ℝ)) := by
      intro x hx
      dsimp only
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hcpow : (x : ℂ) ^ (-(σ : ℂ) - 1) = ((x ^ (-σ - 1) : ℝ) : ℂ) := by
        have hexp : (-(σ : ℂ) - 1) = (((-σ - 1 : ℝ)) : ℂ) := by push_cast; ring
        rw [hexp, Complex.ofReal_cpow hx_pos.le]
      rw [hcpow, ← Complex.ofReal_mul]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq]
    exact integral_ofReal (𝕜 := ℂ)
  have hncpow : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Complex.ofReal_cpow hn_pos.le]
  rw [hcongr, hncpow] at hc
  have hdiv_r : (((n : ℝ) ^ (-σ) : ℝ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) - 1)) =
      (((n : ℝ) ^ (-σ) / (σ * (σ - 1)) : ℝ) : ℂ) := by push_cast; ring
  rw [hdiv_r] at hc
  exact Complex.ofReal_injective hc

/-- Rewriting the finite sum `∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * max (x / n - 1) 0` as a
series `∑' n : ℕ, if 1 ≤ n then a n * max (x / n - 1) 0 else 0` for `x ≥ 1`. -/
lemma sum_Icc_tent_eq_tsum (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) =
      ∑' n : ℕ, if 1 ≤ n then a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) else 0 := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rw [tsum_eq_sum (s := Finset.Icc 1 (Nat.floor x))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [ite_eq_left_iff.mpr (fun hnot => False.elim (hnot (Finset.mem_Icc.mp hn).1))]
  · intro n hn
    split_ifs with hn1
    · have hgt : Nat.floor x < n := by
        rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
        rcases hn with h0 | hgt
        · omega
        · exact hgt
      have hx_lt_n : x < (n : ℝ) := (Nat.floor_lt hx0).mp hgt
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hmax : max (x / (n : ℝ) - 1) 0 = 0 := by
        refine max_eq_right ?_
        rw [sub_nonpos, div_le_one hn_pos]
        exact hx_lt_n.le
      rw [hmax, Complex.ofReal_zero, mul_zero]
    · rfl

private lemma lintegral_enorm_tsum_ne_top_of_summable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℂ)
    (hf_int : ∀ n : ℕ, Integrable (f n) μ)
    (hsum : Summable (fun n : ℕ => ∫ x, ‖f n x‖ ∂μ)) :
    (∑' n : ℕ, ∫⁻ x, ‖f n x‖ₑ ∂μ) ≠ ⊤ := by
  have hterm : ∀ n : ℕ, ∫⁻ x, ‖f n x‖ₑ ∂μ = ENNReal.ofReal (∫ x, ‖f n x‖ ∂μ) := by
    intro n
    rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hf_int n)]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => MeasureTheory.integral_nonneg fun _ => norm_nonneg _) hsum]
  exact ENNReal.ofReal_ne_top

/-- Integrability and Mellin transform of `∑_{1 ≤ n ≤ x} a(n) max(x/n - 1, 0) * x ^ (-s - 1)` on
`Ioi 1` for `|a(n)| ≤ Λ(n)` and `1 < s.re`. -/
theorem integrableOn_and_integral_smoothed_vonMangoldt_series
    (a : ℕ → ℂ) (ha_le : ∀ n : ℕ, ‖a n‖ ≤ Λ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
        (x : ℂ) ^ (-s - 1))
      (Ioi (1 : ℝ)) ∧
    ∫ x in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
        (x : ℂ) ^ (-s - 1) =
      (∑' n : ℕ, if 1 ≤ n then a n * (n : ℂ) ^ (-s) else 0) / (s * (s - 1)) := by
  let f : ℕ → ℝ → ℂ := fun n x =>
    if 1 ≤ n then a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) else 0
  have hf_int : ∀ n : ℕ, Integrable (f n) (volume.restrict (Ioi (1 : ℝ))) := by
    intro n
    by_cases hn : 1 ≤ n
    · have hfn : f n = fun x => a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
        ext x; exact ite_eq_left_iff.mpr fun h => False.elim (h hn)
      rw [hfn]
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      have hw1_re : (-s).re < -1 := by rw [neg_re]; linarith
      have hw2_re : (-s - 1).re < -1 := by rw [sub_re, neg_re, one_re]; linarith
      have hint1 := integrableOn_Ioi_cpow_of_lt hw1_re hn_pos
      have hint2 := integrableOn_Ioi_cpow_of_lt hw2_re hn_pos
      have hsplit : Ioi (1 : ℝ) = Ioc (1 : ℝ) (n : ℝ) ∪ Ioi (n : ℝ) :=
        (Ioc_union_Ioi_eq_Ioi hn_ge1).symm
      change IntegrableOn _ (Ioi (1 : ℝ))
      rw [hsplit]
      refine IntegrableOn.union ?_ ?_
      · refine integrableOn_congr_eqOn measurableSet_Ioc
          (integrableOn_zero (μ := volume) (s := Ioc (1 : ℝ) (n : ℝ))) ?_
        intro x hx
        dsimp only
        have hmax : max (x / (n : ℝ) - 1) 0 = 0 := max_eq_right (by rw [sub_nonpos, div_le_one hn_pos]; exact hx.2)
        simp [hmax]
      · refine integrableOn_congr_eqOn measurableSet_Ioi
          (((hint1.const_mul ((n : ℂ)⁻¹)).sub hint2).const_mul (a n)) ?_
        intro x hx
        dsimp only [Pi.sub_apply]
        have hx_pos : 0 < x := lt_trans hn_pos hx
        have hmax : max (x / (n : ℝ) - 1) 0 = x / (n : ℝ) - 1 :=
          max_eq_left (by rw [sub_nonneg, le_div_iff₀ hn_pos]; linarith [show (n : ℝ) < x from hx])
        rw [hmax]; push_cast
        have hcpow : (x : ℂ) ^ (-s) = (x : ℂ) * (x : ℂ) ^ (-s - 1) := by
          have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
          have hexp : (-s) = 1 + (-s - 1) := by ring
          conv_lhs => rw [hexp, Complex.cpow_add _ _ hx_ne, Complex.cpow_one]
        rw [hcpow]; ring
    · have hfn : f n = fun _ => 0 := by
        ext x; exact ite_eq_right_iff.mpr fun h => False.elim (hn h)
      rw [hfn]
      exact integrable_zero _ _ _
  have hnorm_sum : Summable (fun n : ℕ => ∫ x in Ioi (1 : ℝ), ‖f n x‖) := by
    have hL_summ : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-s.re)) := by
      have h0 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
      refine h0.congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rw [LSeries.term_of_ne_zero hn0, norm_div, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0),
          div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
    refine (hL_summ.mul_right (1 / (s.re * (s.re - 1)))).of_nonneg_of_le
      (fun n => MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _)
      (fun n => ?_)
    by_cases hn : 1 ≤ n
    · have hfn : f n = fun x => a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
        ext x; exact ite_eq_left_iff.mpr fun h => False.elim (h hn)
      rw [hfn]
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      have hker_int : IntegrableOn (fun x : ℝ => max (x / (n : ℝ) - 1) 0 * x ^ (-s.re - 1)) (Ioi 1) := by
        have h1 := integrableOn_Ioi_rpow_of_lt (show -s.re < -1 by linarith) hn_pos
        have h2 := integrableOn_Ioi_rpow_of_lt (show -s.re - 1 < -1 by linarith) hn_pos
        rw [IntegrableOn, (Ioc_union_Ioi_eq_Ioi hn_ge1).symm]
        refine IntegrableOn.union ?_ ?_
        · refine integrableOn_congr_eqOn measurableSet_Ioc
            (integrableOn_zero (μ := volume) (s := Ioc (1 : ℝ) (n : ℝ))) ?_
          intro x hx
          dsimp only
          have hmax : max (x / (n : ℝ) - 1) 0 = 0 :=
            max_eq_right (sub_nonpos.mpr ((div_le_one hn_pos).mpr hx.2))
          rw [hmax, zero_mul]
        · refine integrableOn_congr_eqOn measurableSet_Ioi ((h1.const_mul (n : ℝ)⁻¹).sub h2) ?_
          intro x hx
          dsimp only [Pi.sub_apply]
          have hx_pos : 0 < x := lt_trans hn_pos hx
          have hx_gt_n : (n : ℝ) < x := hx
          have hmax : max (x / (n : ℝ) - 1) 0 = x / (n : ℝ) - 1 :=
            max_eq_left (by rw [sub_nonneg, le_div_iff₀ hn_pos]; linarith)
          rw [hmax]
          have hrpow : x ^ (-s.re) = x * x ^ (-s.re - 1) := by
            conv_lhs => rw [show (-s.re) = 1 + (-s.re - 1) by ring, Real.rpow_add hx_pos, Real.rpow_one]
          rw [hrpow]; ring
      have hfn_norm : IntegrableOn (fun x : ℝ => ‖a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖) (Ioi 1) := by
        have h1 := (hf_int n).norm
        rwa [hfn] at h1
      have hbound_int : ∫ x in Ioi (1 : ℝ),
          ‖a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖ ≤
          ∫ x in Ioi (1 : ℝ), Λ n * (max (x / (n : ℝ) - 1) 0 * x ^ (-s.re - 1)) := by
        refine MeasureTheory.setIntegral_mono_on hfn_norm (hker_int.const_mul (Λ n)) measurableSet_Ioi fun x hx => ?_
        have hx_pos : 0 < x := lt_trans zero_lt_one hx
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (le_max_right _ _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ha_le n) (le_max_right _ _))
          (Real.rpow_nonneg hx_pos.le _)
      rw [MeasureTheory.integral_const_mul, real_integral_smoothed_tent_kernel hn hs] at hbound_int
      calc
        ∫ x in Ioi (1 : ℝ), ‖a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)‖
            ≤ Λ n * ((n : ℝ) ^ (-s.re) / (s.re * (s.re - 1))) := hbound_int
        _ = Λ n * (n : ℝ) ^ (-s.re) * (1 / (s.re * (s.re - 1))) := by ring
    · have hfn : f n = fun _ => 0 := by
        ext x; exact ite_eq_right_iff.mpr fun h => False.elim (hn h)
      rw [hfn]
      simp only [norm_zero, MeasureTheory.integral_zero]
      exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
        (by positivity)
  have htsum_eq : EqOn
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
        (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => ∑' n : ℕ, f n x)
      (Ioi (1 : ℝ)) := by
    intro x hx
    dsimp only [f]
    rw [sum_Icc_tent_eq_tsum a (le_of_lt hx), ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    split_ifs <;> ring
  have hne_top := lintegral_enorm_tsum_ne_top_of_summable _ f hf_int hnorm_sum
  have hint_tsum : Integrable (fun x : ℝ => ∑' n : ℕ, f n x) (volume.restrict (Ioi (1 : ℝ))) := by
    have hmeas_tsum : AEStronglyMeasurable (fun x : ℝ => ∑' n : ℕ, f n x)
        (volume.restrict (Ioi (1 : ℝ))) := by
      have hm_seq : ∀ N : ℕ, AEStronglyMeasurable (fun x : ℝ => ∑ n ∈ Finset.range N, f n x)
          (volume.restrict (Ioi (1 : ℝ))) := fun N =>
        Finset.aestronglyMeasurable_fun_sum (Finset.range N) (fun n _ => (hf_int n).aestronglyMeasurable)
      exact aestronglyMeasurable_of_tendsto_ae
        (f := fun N x => ∑ n ∈ Finset.range N, f n x)
        atTop hm_seq (by
          filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))] with x hx
          have hx0 : 0 ≤ x := zero_le_one.trans (le_of_lt hx)
          have hhasSum : HasSum (fun n : ℕ => f n x) (∑ n ∈ Finset.Icc 1 (Nat.floor x), f n x) := by
            refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
            dsimp only [f]
            split_ifs with hn1
            · have hgt : Nat.floor x < n := by
                rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
                rcases hn with h0 | hgt
                · omega
                · exact hgt
              have hx_lt_n : x < (n : ℝ) := (Nat.floor_lt hx0).mp hgt
              have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
              have hmax : max (x / (n : ℝ) - 1) 0 = 0 :=
                max_eq_right (sub_nonpos.mpr ((div_le_one hn_pos).mpr hx_lt_n.le))
              rw [hmax, Complex.ofReal_zero, mul_zero, zero_mul]
            · rfl
          rw [hhasSum.tsum_eq]
          exact hhasSum.tendsto_sum_nat)
    refine ⟨hmeas_tsum, ?_⟩
    rw [HasFiniteIntegral]
    have hle : ∫⁻ x in Ioi (1 : ℝ), ‖∑' n : ℕ, f n x‖ₑ ≤ ∑' n : ℕ, ∫⁻ x in Ioi (1 : ℝ), ‖f n x‖ₑ := by
      calc
        ∫⁻ x in Ioi (1 : ℝ), ‖∑' n : ℕ, f n x‖ₑ
            ≤ ∫⁻ x in Ioi (1 : ℝ), ∑' n : ℕ, ‖f n x‖ₑ :=
              MeasureTheory.lintegral_mono fun x => enorm_tsum_le_tsum_enorm
        _ = ∑' n : ℕ, ∫⁻ x in Ioi (1 : ℝ), ‖f n x‖ₑ :=
              MeasureTheory.lintegral_tsum (fun n => (hf_int n).aestronglyMeasurable.enorm)
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hne_top)
  refine ⟨integrableOn_congr_eqOn measurableSet_Ioi hint_tsum htsum_eq.symm, ?_⟩
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi htsum_eq,
    MeasureTheory.integral_tsum (fun n => (hf_int n).aestronglyMeasurable) hne_top]
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  by_cases hn : 1 ≤ n
  · have hfn : f n = fun x => a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
      ext x; exact ite_eq_left_iff.mpr fun h => False.elim (h hn)
    rw [hfn]
    have hcm : (fun x : ℝ => a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) =
        fun x : ℝ => a n * (((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      ext x; ring
    rw [hcm, MeasureTheory.integral_const_mul, integral_smoothed_tent_kernel hn hs,
      ite_eq_left_iff.mpr (fun h => False.elim (h hn))]
    ring
  · have hfn : f n = fun _ => 0 := by
      ext x; exact ite_eq_right_iff.mpr fun h => False.elim (hn h)
    rw [hfn, MeasureTheory.integral_zero, ite_eq_right_iff.mpr (fun h => False.elim (hn h)), zero_div]

theorem integral_smoothed_vonMangoldt_series
    (a : ℕ → ℂ) (ha_le : ∀ n : ℕ, ‖a n‖ ≤ Λ n) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 (Nat.floor x), a n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
        (x : ℂ) ^ (-s - 1) =
      (∑' n : ℕ, if 1 ≤ n then a n * (n : ℂ) ^ (-s) else 0) / (s * (s - 1)) :=
  (integrableOn_and_integral_smoothed_vonMangoldt_series a ha_le hs).2

/-- Integrability and Mellin transform of `twistedVonMangoldtSum χ` on `Ioi 1` for `1 < s.re`. -/
theorem integrableOn_and_integral_twistedVonMangoldtSum
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => twistedVonMangoldtSum χ x * (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) ∧
    ∫ x in Ioi (1 : ℝ), twistedVonMangoldtSum χ x * (x : ℂ) ^ (-s - 1) =
      (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) / (s * (s - 1)) := by
  have hident := integrableOn_and_integral_smoothed_vonMangoldt_series
    (fun n : ℕ => (Λ n : ℂ) * χ n)
    (fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right (a := Λ n) ArithmeticFunction.vonMangoldt_nonneg
        (DirichletCharacter.norm_le_one χ n))
    hs
  refine ⟨hident.1, ?_⟩
  have hL : (∑' n : ℕ, if 1 ≤ n then ((Λ n : ℂ) * χ n) * (n : ℂ) ^ (-s) else 0) =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
    have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
    have hL_eq : LSeries ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) s =
        ∑' n : ℕ, if 1 ≤ n then ((Λ n : ℂ) * χ n) * (n : ℂ) ^ (-s) else 0 := by
      unfold LSeries
      refine tsum_congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        rw [LSeries.term_of_ne_zero hn0, ite_eq_left_iff.mpr (fun h => False.elim (h hn1))]
        simp [Pi.mul_apply, div_eq_mul_inv, ← Complex.cpow_neg, mul_comm]
    rw [← hL_eq]
    exact htw
  rw [hL] at hident
  exact hident.2

/-- Integrability and Mellin transform of `smoothedPrincipalG γ_em` on `Ioi 1` for `1 < s.re`. -/
theorem integrableOn_and_integral_smoothedPrincipalG (γ_em : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) ∧
    ∫ x in Ioi (1 : ℝ), ((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) =
      (-deriv riemannZeta s / riemannZeta s - (1 : ℂ) / (s - 1) - 1 + (1 + (γ_em : ℂ)) * s) /
        (s * (s - 1)) := by
  have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_re] at hs; linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h1; have := congrArg Complex.re (sub_eq_zero.mp h1); rw [one_re] at this; linarith
  have hvm_pair := integrableOn_and_integral_smoothed_vonMangoldt_series
    (fun n : ℕ => (Λ n : ℂ))
    (fun n => by rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg])
    hs
  have hint_vm := hvm_pair.1
  have hvm := hvm_pair.2
  have hzeta : (∑' n : ℕ, if 1 ≤ n then (Λ n : ℂ) * (n : ℂ) ^ (-s) else 0) =
      -deriv riemannZeta s / riemannZeta s := by
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    rw [← hL]
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rw [LSeries.term_of_ne_zero hn0, ite_eq_left_iff.mpr (fun h => False.elim (h hn1))]
      simp [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [hzeta] at hvm
  have hw1_re : (-s).re < -1 := by rw [neg_re]; linarith
  have hint_pow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hw1_re zero_lt_one
  have hpow_val : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s) = (1 : ℂ) / (s - 1) := by
    rw [integral_Ioi_ofReal_cpow zero_lt_one hw1_re, Complex.ofReal_one, Complex.one_cpow]
    have : -s + 1 = -(s - 1) := by ring
    rw [this]; field_simp [hs1]
  have hint_log : IntegrableOn (fun x : ℝ => Complex.log (x : ℂ) * (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := by
    let ε : ℝ := (s.re - 1) / 2
    have hε_pos : 0 < ε := by dsimp [ε]; linarith
    have hint_dom := (integrableOn_Ioi_rpow_of_lt (show (-s.re + ε) < -1 by dsimp [ε]; linarith) zero_lt_one).const_mul (1 / ε)
    refine hint_dom.mono'
      (((Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable).mul
        ((ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const
          (fun x hx => Or.inl (by rw [Complex.ofReal_re]; exact lt_trans zero_lt_one hx))).aestronglyMeasurable measurableSet_Ioi)) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, ← Complex.ofReal_log hx_pos.le, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (le_of_lt hx)),
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, neg_re]
    have hlog_le : Real.log x ≤ (1 / ε) * x ^ ε := by
      have h1 : ε * Real.log x = Real.log (x ^ ε) := (Real.log_rpow hx_pos ε).symm
      have h2 : Real.log (x ^ ε) ≤ x ^ ε - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos ε)
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hε_pos]
      linarith
    calc
      Real.log x * x ^ (-s.re) ≤ ((1 / ε) * x ^ ε) * x ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg hx_pos.le _)
      _ = (1 / ε) * (x ^ ε * x ^ (-s.re)) := by ring
      _ = (1 / ε) * x ^ (-s.re + ε) := by rw [← Real.rpow_add hx_pos, add_comm]
  have hlog_val : ∫ x in Ioi (1 : ℝ), Complex.log (x : ℂ) * (x : ℂ) ^ (-s) = (1 : ℂ) / (s - 1) ^ 2 := by
    have hd_s : HasDerivAt (fun w : ℂ => ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-w))
        (- ∫ x in Ioi (1 : ℝ), Complex.log (x : ℂ) * (x : ℂ) ^ (-s)) s := by
      let σ₀ : ℝ := (1 + s.re) / 2
      let r_ball : ℝ := (s.re - σ₀) / 2
      let ε : ℝ := (σ₀ - 1) / 2
      have hσ₀_gt1 : 1 < σ₀ := by dsimp [σ₀]; linarith
      have hr_pos : 0 < r_ball := by dsimp [r_ball, σ₀]; linarith
      have hε_pos : 0 < ε := by dsimp [ε, σ₀]; linarith
      have hball_re : ∀ w ∈ Metric.ball s r_ball, σ₀ ≤ w.re := by
        intro w hw
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        have hre_le : |w.re - s.re| ≤ ‖w - s‖ := by
          simpa [sub_re] using Complex.abs_re_le_norm (w - s)
        have h1 := (abs_le.mp (hre_le.trans hw.le)).1
        dsimp [r_ball, σ₀] at h1 ⊢
        linarith
      have hint_dom_r : Integrable (fun x : ℝ => (1 / ε) * x ^ (-σ₀ + ε))
          (volume.restrict (Ioi (1 : ℝ))) :=
        (integrableOn_Ioi_rpow_of_lt (show (-σ₀ + ε) < -1 by dsimp [ε, σ₀]; linarith) zero_lt_one).const_mul (1 / ε)
      have hF_meas : ∀ᶠ w in 𝓝 s, AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-w))
          (volume.restrict (Ioi (1 : ℝ))) := by
        filter_upwards [Metric.ball_mem_nhds s hr_pos] with w hw
        have hw_gt1 : 1 < w.re := lt_of_lt_of_le hσ₀_gt1 (hball_re w hw)
        exact (integrableOn_Ioi_cpow_of_lt (show (-w).re < -1 by rw [neg_re]; linarith) zero_lt_one).aestronglyMeasurable
      have hF'_meas : AEStronglyMeasurable
          (fun x : ℝ => (x : ℂ) ^ (-s) * Complex.log (x : ℂ) * (-1))
          (volume.restrict (Ioi (1 : ℝ))) := by
        have hlogC : AEStronglyMeasurable (fun x : ℝ => Complex.log (x : ℂ)) (volume.restrict (Ioi (1 : ℝ))) :=
          (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable
        exact ((hint_pow.aestronglyMeasurable).mul hlogC).mul aestronglyMeasurable_const
      have hbound : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioi (1 : ℝ)), ∀ w ∈ Metric.ball s r_ball,
          ‖(x : ℂ) ^ (-w) * Complex.log (x : ℂ) * (-1)‖ ≤ (1 / ε) * x ^ (-σ₀ + ε) := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))] with x hx w hw
        have hx_pos : 0 < x := lt_trans zero_lt_one hx
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos,
          ← Complex.ofReal_log hx_pos.le, Complex.norm_real,
          Real.norm_of_nonneg (Real.log_nonneg (le_of_lt hx)), norm_neg, norm_one, mul_one, neg_re]
        have hlog_le : Real.log x ≤ (1 / ε) * x ^ ε := by
          have h1 : ε * Real.log x = Real.log (x ^ ε) := (Real.log_rpow hx_pos ε).symm
          have h2 : Real.log (x ^ ε) ≤ x ^ ε - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos ε)
          rw [one_div, inv_mul_eq_div, le_div_iff₀ hε_pos]; linarith
        calc
          x ^ (-w.re) * Real.log x ≤ x ^ (-σ₀) * ((1 / ε) * x ^ ε) :=
            mul_le_mul (Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) (by linarith [hball_re w hw]))
              hlog_le (Real.log_nonneg (le_of_lt hx)) (Real.rpow_nonneg hx_pos.le _)
          _ = (1 / ε) * (x ^ ε * x ^ (-σ₀)) := by ring
          _ = (1 / ε) * x ^ (-σ₀ + ε) := by rw [← Real.rpow_add hx_pos, add_comm]
      have hderiv : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioi (1 : ℝ)), ∀ w ∈ Metric.ball s r_ball,
          HasDerivAt (fun z : ℂ => (x : ℂ) ^ (-z)) ((x : ℂ) ^ (-w) * Complex.log (x : ℂ) * (-1)) w := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))] with x hx w _
        have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hx).ne'
        simpa using (hasDerivAt_id w).neg.const_cpow (Or.inl hx_ne)
      have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume.restrict (Ioi (1 : ℝ)))
        (F := fun w x => (x : ℂ) ^ (-w))
        (F' := fun w x => (x : ℂ) ^ (-w) * Complex.log (x : ℂ) * (-1))
        (bound := fun x => (1 / ε) * x ^ (-σ₀ + ε))
        (Metric.ball_mem_nhds s hr_pos) hF_meas hint_pow hF'_meas hbound hint_dom_r hderiv
      have heq_neg : (- ∫ x in Ioi (1 : ℝ), Complex.log (x : ℂ) * (x : ℂ) ^ (-s)) =
          ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s) * Complex.log (x : ℂ) * (-1) := by
        rw [← MeasureTheory.integral_neg]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
      rw [heq_neg]; exact hd.2
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq_on : EqOn (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-z))
        (fun z : ℂ => (1 : ℂ) / (z - 1)) {z : ℂ | 1 < z.re} := by
      intro z hz
      dsimp only
      have hz_gt1 : (1 : ℝ) < z.re := hz
      have hz1 : z - 1 ≠ 0 := by
        intro h; have hre := congrArg Complex.re (sub_eq_zero.mp h); rw [one_re] at hre; linarith
      have hre_lt : (-z).re < -1 := by rw [neg_re]; linarith
      rw [integral_Ioi_ofReal_cpow zero_lt_one hre_lt, Complex.ofReal_one, Complex.one_cpow]
      have : -z + 1 = -(z - 1) := by ring
      rw [this]; field_simp [hz1]
    have hd_rhs : HasDerivAt (fun z : ℂ => (1 : ℂ) / (z - 1)) (-(1 : ℂ) / (s - 1) ^ 2) s := by
      have hd1 : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
      simpa [neg_div] using hd1.fun_inv hs1
    have hd_eq := hd_s.congr_of_eventuallyEq (heq_on.eventuallyEq_of_mem (hopen1.mem_nhds hs)).symm
    have hderiv_uniq := hd_eq.unique hd_rhs
    exact neg_inj.mp (by simpa [neg_div] using hderiv_uniq)
  have hsplit_int : EqOn
      (fun x : ℝ => ((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n : ℂ) * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
          (x : ℂ) ^ (-s - 1) -
        (Complex.log (x : ℂ) * (x : ℂ) ^ (-s) - (1 + (γ_em : ℂ)) * (x : ℂ) ^ (-s)))
      (Ioi (1 : ℝ)) := by
    intro x hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    dsimp only [smoothedPrincipalG]
    push_cast
    rw [Complex.ofReal_log hx_pos.le]
    have hcpow : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
      conv_rhs => rw [show (-s) = 1 + (-s - 1) by ring, Complex.cpow_add _ _ hx_ne, Complex.cpow_one]
    calc
      ((∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n : ℂ) * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) -
          (x : ℂ) * (Complex.log (x : ℂ) - 1 - (γ_em : ℂ))) * (x : ℂ) ^ (-s - 1)
          = (∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n : ℂ) * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
              (x : ℂ) ^ (-s - 1) -
            (Complex.log (x : ℂ) - 1 - (γ_em : ℂ)) * ((x : ℂ) * (x : ℂ) ^ (-s - 1)) := by ring
      _ = (∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n : ℂ) * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)) *
              (x : ℂ) ^ (-s - 1) -
            (Complex.log (x : ℂ) * (x : ℂ) ^ (-s) - (1 + (γ_em : ℂ)) * (x : ℂ) ^ (-s)) := by
            rw [hcpow]; ring
  have hint_diff := hint_vm.sub (hint_log.sub (hint_pow.const_mul (1 + (γ_em : ℂ))))
  refine ⟨integrableOn_congr_eqOn measurableSet_Ioi hint_diff hsplit_int.symm, ?_⟩
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsplit_int]
  have hsub1 := MeasureTheory.integral_sub hint_vm
    (hint_log.sub (hint_pow.const_mul (1 + (γ_em : ℂ))))
  have hsub2 := MeasureTheory.integral_sub hint_log (hint_pow.const_mul (1 + (γ_em : ℂ)))
  dsimp only [Pi.sub_apply] at hsub1 hsub2
  rw [hsub1, hsub2, MeasureTheory.integral_const_mul, hvm, hlog_val, hpow_val]
  field_simp [hs0, hs1]
  ring

/-! ## Part 2B: Involution Pairing & Proposition 3.3 -/

/-- Involution pairing on `S`: `∑ ξ ∈ S, realCharG (ψ ξ).char γ_em (logDerivMap (ψ ξ)) y`
equals the real part of `∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y + y * logDerivMap (ψ ξ)`. -/
lemma sum_realCharG_eq_re_sum
    {ι : Type}
    (S : Finset ι) (ψ : ι → PrimitiveChar)
    (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ) (y : ℝ)
    (hnonprin : ∀ ξ ∈ S, (ψ ξ).char ≠ 1) :
    (∑ ξ ∈ S, realCharG (ψ ξ).char γ_em (logDerivMap (ψ ξ)) y) =
      (∑ ξ ∈ S, (twistedVonMangoldtSum (ψ ξ).char y + (y : ℂ) * logDerivMap (ψ ξ))).re := by
  classical
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  unfold realCharG normalizedCharG
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hnonprin ξ hξ h))]

/-- Involution pairing identity on `twistedVonMangoldtSum`: using `τ` with `ψ (τ ξ) = (ψ ξ).inv`
and Lemma 3.1, `((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y).re : ℂ) = ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y`. -/
lemma sum_twistedVonMangoldtSum_real
    {ι : Type}
    (S : Finset ι) (τ : ι → ι) (ψ : ι → PrimitiveChar) (y : ℝ)
    (hτ_inv : ∀ ξ ∈ S, τ ξ ∈ S ∧ τ (τ ξ) = ξ)
    (hψ_inv : ∀ ξ ∈ S, ψ (τ ξ) = (ψ ξ).inv) :
    (((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y).re : ℝ) : ℂ) =
      ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y := by
  have hpair : (∑ ξ ∈ S, twistedVonMangoldtSum (ψ (τ ξ)).char y) =
      ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y := by
    refine Finset.sum_bij (fun ξ _ => τ ξ) (fun ξ hξ => (hτ_inv ξ hξ).1)
      (fun a ha b hb hab => ?_) (fun ξ hξ => ⟨τ ξ, (hτ_inv ξ hξ).1, (hτ_inv ξ hξ).2⟩)
      (fun _ _ => rfl)
    calc
      a = τ (τ a) := ((hτ_inv a ha).2).symm
      _ = τ (τ b) := by rw [hab]
      _ = b := (hτ_inv b hb).2
  have hhalf : (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y) =
      (1 / 2 : ℂ) * ∑ ξ ∈ S,
        (twistedVonMangoldtSum (ψ ξ).char y + twistedVonMangoldtSum (ψ ξ).inv.char y) := by
    have h2 : (2 : ℂ) * ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y =
        ∑ ξ ∈ S, (twistedVonMangoldtSum (ψ ξ).char y + twistedVonMangoldtSum (ψ ξ).inv.char y) := by
      calc
        (2 : ℂ) * ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y
            = (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y) +
                ∑ ξ ∈ S, twistedVonMangoldtSum (ψ (τ ξ)).char y := by
                  rw [hpair]; ring
        _ = ∑ ξ ∈ S, (twistedVonMangoldtSum (ψ ξ).char y + twistedVonMangoldtSum (ψ (τ ξ)).char y) := by
              rw [← Finset.sum_add_distrib]
        _ = ∑ ξ ∈ S, (twistedVonMangoldtSum (ψ ξ).char y + twistedVonMangoldtSum (ψ ξ).inv.char y) := by
              refine Finset.sum_congr rfl fun ξ hξ => by rw [hψ_inv ξ hξ]
    calc
      (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y)
          = (1 / 2 : ℂ) * ((2 : ℂ) * ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char y) := by ring
      _ = (1 / 2 : ℂ) * ∑ ξ ∈ S,
            (twistedVonMangoldtSum (ψ ξ).char y + twistedVonMangoldtSum (ψ ξ).inv.char y) := by
            rw [h2]
  have hreal_rhs : ∑ ξ ∈ S,
      (1 / 2 : ℂ) * (twistedVonMangoldtSum (ψ ξ).char y + twistedVonMangoldtSum (ψ ξ).inv.char y) =
      ∑ ξ ∈ S, (((twistedVonMangoldtSum (ψ ξ).char y).re : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun ξ _ => ?_
    unfold twistedVonMangoldtSum PrimitiveChar.inv
    rw [Complex.re_sum, Complex.ofReal_sum, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hre_scale : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).re = r * z.re := by
      intro r z; rw [mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have hmul_re : ((Λ n : ℂ) * (ψ ξ).char n * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ)).re =
        (Λ n * ((ψ ξ).char n).re) * max (y / (n : ℝ) - 1) 0 := by
      rw [mul_assoc, hre_scale, mul_comm ((ψ ξ).char n), hre_scale]
      ring
    rw [hmul_re, Complex.ofReal_mul, lemma_3_1_real_part_character_identity]
    push_cast
    ring
  rw [Complex.re_sum, Complex.ofReal_sum, ← hreal_rhs, ← Finset.mul_sum, ← hhalf]

private lemma integrableOn_and_integral_finset_sum_twisted
    {ι : Type} (S : Finset ι) (ψ : ι → PrimitiveChar) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x * (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) ∧
    ∫ x in Ioi (1 : ℝ), ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x * (x : ℂ) ^ (-s - 1) =
      ∑ ξ ∈ S, (-deriv (DirichletCharacter.LFunction (ψ ξ).char) s / DirichletCharacter.LFunction (ψ ξ).char s) / (s * (s - 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨integrableOn_zero (μ := volume) (s := Ioi (1 : ℝ)), MeasureTheory.integral_zero _ _⟩
  | insert a u ha ih =>
    have h1 := integrableOn_and_integral_twistedVonMangoldtSum (ψ a).char hs
    have heq : (fun x : ℝ => ∑ ξ ∈ insert a u, twistedVonMangoldtSum (ψ ξ).char x * (x : ℂ) ^ (-s - 1)) =
        fun x => twistedVonMangoldtSum (ψ a).char x * (x : ℂ) ^ (-s - 1) +
          ∑ ξ ∈ u, twistedVonMangoldtSum (ψ ξ).char x * (x : ℂ) ^ (-s - 1) := by
      ext x; exact Finset.sum_insert ha
    refine ⟨?_, ?_⟩
    · rw [heq]; exact h1.1.add ih.1
    · rw [heq, MeasureTheory.integral_add h1.1 ih.1, Finset.sum_insert ha, h1.2, ih.2]

/-- **Proposition 3.3 (Landau Positivity for Inversion-Closed Families)**:
If `S` is a finite set equipped with an involution `τ` pairing non-principal primitive characters
`ψ (τ ξ) = (ψ ξ).inv`, `1 ≤ R`, `0 < θ < 1`, the weighted family Chebyshev error satisfies
`R * G(y) + ∑_{ξ ∈ S} G_{ψ_ξ}(y) ≤ C₀ y^θ` for all `y ≥ y₀`, and the linear residue at `s = 1`
matches `P'(1) = (γ_em R + ∑ Re logDerivMap) P(1)`, then `ζ(s) ≠ 0` (for `s ≠ 1`) and
`L(s, ψ_ξ) ≠ 0` for all `ξ ∈ S` and `Re(s) > θ`. -/
theorem prop_3_3_inversion_closed_landau
    {ι : Type}
    (S : Finset ι) (τ : ι → ι) (ψ : ι → PrimitiveChar)
    (R : ℕ) (θ C₀ y₀ : ℝ) (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ)
    (hτ_inv : ∀ ξ ∈ S, τ ξ ∈ S ∧ τ (τ ξ) = ξ)
    (hψ_pair : ∀ ξ ∈ S, (ψ ξ).char ≠ 1 ∧ ψ (τ ξ) = (ψ ξ).inv)
    (hR : 1 ≤ R) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hres1 : deriv (familyEntireProduct S ψ R) 1 =
      (((R : ℂ) * (γ_em : ℂ) + ((∑ ξ ∈ S, (logDerivMap (ψ ξ)).re : ℝ) : ℂ))) *
        familyEntireProduct S ψ R 1)
    (hgrowth : ∀ y : ℝ, y₀ ≤ y →
      (R : ℝ) * smoothedPrincipalG γ_em y +
        ∑ ξ ∈ S, realCharG (ψ ξ).char γ_em (logDerivMap (ψ ξ)) y ≤ C₀ * y ^ θ) :
    ∀ s : ℂ, θ < s.re →
      (s ≠ 1 → riemannZeta s ≠ 0) ∧ (∀ ξ ∈ S, dirichletL (ψ ξ).char s ≠ 0) := by
  classical
  have hnonprin : ∀ ξ ∈ S, (ψ ξ).char ≠ 1 := fun ξ hξ => (hψ_pair ξ hξ).1
  let P : ℂ → ℂ := familyEntireProduct S ψ R
  have hP_diff : Differentiable ℂ P := differentiable_familyEntireProduct S ψ R hnonprin
  have hP_ge1 : ∀ s : ℂ, 1 ≤ s.re → P s ≠ 0 :=
    fun s hs => familyEntireProduct_ne_zero_of_one_le_re S ψ R hnonprin hs
  let C_log : ℝ := ∑ ξ ∈ S, (logDerivMap (ψ ξ)).re
  let C_pole : ℝ := max C₀ 0
  have hC_pole_nn : 0 ≤ C_pole := le_max_right C₀ 0
  let y₁ : ℝ := max y₀ 1
  have hy₁_ge1 : 1 ≤ y₁ := le_max_right y₀ 1
  have hy₁_pos : 0 < y₁ := zero_lt_one.trans_le hy₁_ge1
  let G_fam : ℝ → ℝ := fun y =>
    (R : ℝ) * smoothedPrincipalG γ_em y +
      ∑ ξ ∈ S, realCharG (ψ ξ).char γ_em (logDerivMap (ψ ξ)) y
  have hG_bdd_Icc : ∃ M_y₁ : ℝ, ∀ x ∈ Icc (1 : ℝ) y₁, G_fam x ≤ M_y₁ := by
    let B_vm : ℝ := ∑ n ∈ Finset.Icc 1 (Nat.floor y₁), Λ n * (y₁ / (n : ℝ))
    let B_lin : ℝ := y₁ * (|Real.log y₁| + 1 + |γ_em|)
    let B_char : ℝ := ∑ ξ ∈ S, (B_vm + y₁ * ‖logDerivMap (ψ ξ)‖)
    refine ⟨(R : ℝ) * (B_vm + B_lin) + B_char, fun x hx => ?_⟩
    have hx_ge1 : 1 ≤ x := hx.1
    have hx_le : x ≤ y₁ := hx.2
    have hx_pos : 0 < x := zero_lt_one.trans_le hx_ge1
    have hfl_sub : Finset.Icc 1 (Nat.floor x) ⊆ Finset.Icc 1 (Nat.floor y₁) :=
      Finset.Icc_subset_Icc_right (Nat.floor_mono hx_le)
    have hvm_le : ∑ n ∈ Finset.Icc 1 (Nat.floor x), Λ n * max (x / (n : ℝ) - 1) 0 ≤ B_vm := by
      calc
        ∑ n ∈ Finset.Icc 1 (Nat.floor x), Λ n * max (x / (n : ℝ) - 1) 0
            ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), Λ n * (y₁ / (n : ℝ)) := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
              have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
              have hn_le_x : (n : ℝ) ≤ x := (Nat.le_floor_iff hx_pos.le).mp (Finset.mem_Icc.mp hn).2
              refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
              rw [max_eq_left (by rw [sub_nonneg, le_div_iff₀ hn_pos]; linarith)]
              have : x / (n : ℝ) ≤ y₁ / (n : ℝ) := div_le_div_of_nonneg_right hx_le hn_pos.le
              linarith
        _ ≤ B_vm := Finset.sum_le_sum_of_subset_of_nonneg hfl_sub
              (fun n _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (div_nonneg hy₁_pos.le (Nat.cast_nonneg n)))
    have hG0_le : smoothedPrincipalG γ_em x ≤ B_vm + B_lin := by
      dsimp [smoothedPrincipalG]
      have hlog_x : |Real.log x| ≤ |Real.log y₁| := by
        rw [abs_of_nonneg (Real.log_nonneg hx_ge1), abs_of_nonneg (Real.log_nonneg hy₁_ge1)]
        exact Real.log_le_log hx_pos hx_le
      have hlin : -(x * (Real.log x - 1 - γ_em)) ≤ B_lin := by
        calc
          -(x * (Real.log x - 1 - γ_em)) ≤ |x * (Real.log x - 1 - γ_em)| := neg_le_abs _
          _ = x * |Real.log x - 1 - γ_em| := by rw [abs_mul, abs_of_pos hx_pos]
          _ ≤ y₁ * (|Real.log x| + 1 + |γ_em|) := by
                refine mul_le_mul hx_le ?_ (abs_nonneg _) hy₁_pos.le
                have h1 : |Real.log x - 1| ≤ |Real.log x| + |(1 : ℝ)| := abs_sub _ _
                rw [abs_one] at h1
                linarith [abs_sub (Real.log x - 1) γ_em]
          _ ≤ B_lin := by dsimp [B_lin]; gcongr
      linarith
    have hsum_char_le : ∑ ξ ∈ S, realCharG (ψ ξ).char γ_em (logDerivMap (ψ ξ)) x ≤ B_char := by
      refine Finset.sum_le_sum fun ξ hξ => ?_
      unfold realCharG normalizedCharG
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnonprin ξ hξ h))]
      refine (Complex.re_le_norm _).trans ?_
      calc
        ‖twistedVonMangoldtSum (ψ ξ).char x + (x : ℂ) * logDerivMap (ψ ξ)‖
            ≤ ‖twistedVonMangoldtSum (ψ ξ).char x‖ + ‖(x : ℂ) * logDerivMap (ψ ξ)‖ := norm_add_le _ _
        _ ≤ B_vm + y₁ * ‖logDerivMap (ψ ξ)‖ := by
              refine add_le_add ?_ ?_
              · unfold twistedVonMangoldtSum
                calc
                  ‖∑ n ∈ Finset.Icc 1 (Nat.floor x), (Λ n : ℂ) * (ψ ξ).char n * ((max (x / (n : ℝ) - 1) 0 : ℝ) : ℂ)‖
                      ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor x), Λ n * max (x / (n : ℝ) - 1) 0 := by
                        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
                        rw [norm_mul, norm_mul, Complex.norm_real,
                          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
                          Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _)]
                        have hle1 := mul_le_of_le_one_right (a := Λ n) ArithmeticFunction.vonMangoldt_nonneg
                          (DirichletCharacter.norm_le_one (ψ ξ).char n)
                        exact mul_le_mul_of_nonneg_right hle1 (le_max_right _ _)
                  _ ≤ B_vm := hvm_le
              · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
                exact mul_le_mul_of_nonneg_right hx_le (norm_nonneg _)
    dsimp [G_fam]
    have hR_nn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    nlinarith
  obtain ⟨M_y₁, hM_y₁⟩ := hG_bdd_Icc
  let C : ℝ := max C_pole M_y₁
  have hC_nn : 0 ≤ C := hC_pole_nn.trans (le_max_left C_pole M_y₁)
  let H : ℝ → ℝ := fun x => C * x ^ θ - G_fam x
  have hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x := by
    intro x hx
    have hx_pos : 0 < x := zero_lt_one.trans_le hx
    dsimp [H]
    by_cases hxy₁ : y₁ ≤ x
    · have hg := hgrowth x ((le_max_left y₀ 1).trans hxy₁)
      have hc_le : C₀ * x ^ θ ≤ C * x ^ θ :=
        mul_le_mul_of_nonneg_right ((le_max_left C₀ 0).trans (le_max_left C_pole M_y₁))
          (Real.rpow_nonneg hx_pos.le θ)
      dsimp [G_fam] at hg ⊢
      linarith
    · push Not at hxy₁
      have hg := hM_y₁ x ⟨hx, hxy₁.le⟩
      have hxθ_ge1 : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ0.le
      have hc_ge : M_y₁ ≤ C * x ^ θ := by
        have hM_le_C : M_y₁ ≤ C := le_max_right C_pole M_y₁
        nlinarith
      linarith
  let a : ℂ := -(R : ℂ)
  let b : ℂ := (R : ℂ) * (1 + (γ_em : ℂ)) + (C_log : ℂ)
  have hP_one : deriv P 1 - (a + b) * P 1 = 0 := by
    have hab : a + b = (R : ℂ) * (γ_em : ℂ) + (C_log : ℂ) := by dsimp [a, b]; ring
    rw [hab]
    exact sub_eq_zero.mpr hres1
  have hH_int_and_eq : ∀ σ_or_s : ℂ, 1 < σ_or_s.re →
      IntegrableOn (fun x : ℝ => ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-σ_or_s - 1)) (Ioi (1 : ℝ)) ∧
      ∫ x in Ioi (1 : ℝ), ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-σ_or_s - 1) =
        (deriv P σ_or_s / P σ_or_s - (a + b * σ_or_s)) / (σ_or_s * (σ_or_s - 1)) +
          (C : ℂ) / (σ_or_s - (θ : ℂ)) := by
    intro s hs
    have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := by
      intro h1; have := congrArg Complex.re (sub_eq_zero.mp h1); rw [one_re] at this; linarith
    have hsθ : s - (θ : ℂ) ≠ 0 := by
      intro hθ; have := congrArg Complex.re (sub_eq_zero.mp hθ); rw [Complex.ofReal_re] at this; linarith
    have hw_θ : ((θ : ℂ) - s - 1).re < -1 := by
      rw [sub_re, sub_re, Complex.ofReal_re, one_re]; linarith
    have hint_θ : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((θ : ℂ) - s - 1)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_cpow_of_lt hw_θ zero_lt_one
    have hval_θ : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((θ : ℂ) - s - 1) = (1 : ℂ) / (s - (θ : ℂ)) := by
      rw [integral_Ioi_ofReal_cpow zero_lt_one hw_θ, Complex.ofReal_one, Complex.one_cpow]
      have : (θ : ℂ) - s - 1 + 1 = -(s - (θ : ℂ)) := by ring
      rw [this]; field_simp [hsθ]
    have hw_x : (-s).re < -1 := by rw [neg_re]; linarith
    have hint_x : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_cpow_of_lt hw_x zero_lt_one
    have hval_x : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s) = (1 : ℂ) / (s - 1) := by
      rw [integral_Ioi_ofReal_cpow zero_lt_one hw_x, Complex.ofReal_one, Complex.one_cpow]
      have : -s + 1 = -(s - 1) := by ring
      rw [this]; field_simp [hs1]
    have hG0 := integrableOn_and_integral_smoothedPrincipalG γ_em hs
    have htw_sum := integrableOn_and_integral_finset_sum_twisted S ψ hs
    have hint_sum_tw : IntegrableOn
        (fun x : ℝ => (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
      refine integrableOn_congr_eqOn measurableSet_Ioi htw_sum.1 ?_
      intro x _; exact (Finset.sum_mul _ _ _).symm
    have hval_sum_tw : ∫ x in Ioi (1 : ℝ),
        (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1) =
        (∑ ξ ∈ S, -deriv (DirichletCharacter.LFunction (ψ ξ).char) s / DirichletCharacter.LFunction (ψ ξ).char s) / (s * (s - 1)) := by
      have heq : EqOn
          (fun x : ℝ => (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1))
          (fun x : ℝ => ∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x * (x : ℂ) ^ (-s - 1))
          (Ioi (1 : ℝ)) := fun x _ => Finset.sum_mul _ _ _
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq, htw_sum.2, ← Finset.sum_div]
    have hH_decomp : EqOn
        (fun x : ℝ => ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        (fun x : ℝ =>
          (C : ℂ) * (x : ℂ) ^ ((θ : ℂ) - s - 1) -
            ((R : ℂ) * (((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
              ((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1) +
                (C_log : ℂ) * (x : ℂ) ^ (-s))))
        (Ioi (1 : ℝ)) := by
      intro x hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
      have hcpow1 : ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ ((θ : ℂ) - s - 1) := by
        rw [Complex.ofReal_cpow hx_pos.le, ← Complex.cpow_add _ _ hx_ne]
        congr 1; ring
      have hcpow2 : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
        conv_rhs => rw [show (-s) = 1 + (-s - 1) by ring, Complex.cpow_add _ _ hx_ne, Complex.cpow_one]
      have hchar_x : (∑ i ∈ S, ((realCharG (ψ i).char γ_em (logDerivMap (ψ i)) x : ℝ) : ℂ)) =
          (∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) + (C_log : ℂ) * (x : ℂ) := by
        rw [← Complex.ofReal_sum, sum_realCharG_eq_re_sum S ψ γ_em logDerivMap x hnonprin,
          Complex.re_sum, Complex.ofReal_sum]
        have hsplit_s : ∑ ξ ∈ S, (((twistedVonMangoldtSum (ψ ξ).char x + (x : ℂ) * logDerivMap (ψ ξ)).re : ℝ) : ℂ) =
            (∑ ξ ∈ S, (((twistedVonMangoldtSum (ψ ξ).char x).re : ℝ) : ℂ)) +
              (∑ ξ ∈ S, (((((x : ℂ) * logDerivMap (ψ ξ)).re : ℝ) : ℂ))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [add_re, Complex.ofReal_add]
        rw [hsplit_s, ← Complex.ofReal_sum, ← Complex.re_sum,
          sum_twistedVonMangoldtSum_real S τ ψ x hτ_inv (fun ξ hξ => (hψ_pair ξ hξ).2)]
        congr 1
        dsimp [C_log]
        rw [Complex.ofReal_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        have hre_m : ((x : ℂ) * logDerivMap (ψ ξ)).re = x * (logDerivMap (ψ ξ)).re := by
          rw [mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
        rw [hre_m, Complex.ofReal_mul, mul_comm]
      dsimp only [H, G_fam]
      push_cast
      rw [hchar_x]
      calc
        ((C : ℂ) * ((x ^ θ : ℝ) : ℂ) -
            ((R : ℂ) * ((smoothedPrincipalG γ_em x : ℝ) : ℂ) +
              ((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) + (C_log : ℂ) * (x : ℂ)))) *
          (x : ℂ) ^ (-s - 1)
            = (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) -
              ((R : ℂ) * (((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
                ((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1) +
                  (C_log : ℂ) * ((x : ℂ) * (x : ℂ) ^ (-s - 1)))) := by ring
        _ = (C : ℂ) * (x : ℂ) ^ ((θ : ℂ) - s - 1) -
              ((R : ℂ) * (((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
                ((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1) +
                  (C_log : ℂ) * (x : ℂ) ^ (-s))) := by
              rw [hcpow1, hcpow2]
    have hint_rhs : IntegrableOn
        (fun x : ℝ =>
          (C : ℂ) * (x : ℂ) ^ ((θ : ℂ) - s - 1) -
            ((R : ℂ) * (((smoothedPrincipalG γ_em x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) +
              ((∑ ξ ∈ S, twistedVonMangoldtSum (ψ ξ).char x) * (x : ℂ) ^ (-s - 1) +
                (C_log : ℂ) * (x : ℂ) ^ (-s))))
        (Ioi (1 : ℝ)) :=
      (hint_θ.const_mul (C : ℂ)).sub
        ((hG0.1.const_mul (R : ℂ)).add (hint_sum_tw.add (hint_x.const_mul (C_log : ℂ))))
    refine ⟨integrableOn_congr_eqOn measurableSet_Ioi hint_rhs hH_decomp.symm, ?_⟩
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hH_decomp]
    have hsub_all := MeasureTheory.integral_sub
      (hint_θ.const_mul (C : ℂ))
      ((hG0.1.const_mul (R : ℂ)).add (hint_sum_tw.add (hint_x.const_mul (C_log : ℂ))))
    have hadd2 := MeasureTheory.integral_add (hG0.1.const_mul (R : ℂ))
      (hint_sum_tw.add (hint_x.const_mul (C_log : ℂ)))
    have hadd3 := MeasureTheory.integral_add hint_sum_tw (hint_x.const_mul (C_log : ℂ))
    dsimp only [Pi.sub_apply, Pi.add_apply] at hsub_all hadd2 hadd3
    rw [hsub_all, hadd2, hadd3,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      hval_θ, hG0.2, hval_sum_tw, hval_x,
      logDeriv_familyEntireProduct_of_one_lt_re S ψ R hnonprin hs]
    dsimp [a, b]
    simp only [Finset.sum_neg_distrib, neg_div]
    field_simp [hs0, hs1, hsθ]
    ring
  have hH_int_real : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    have hc := (hH_int_and_eq (σ : ℂ) (by simpa using hσ)).1.norm
    refine integrableOn_congr_eqOn measurableSet_Ioi hc ?_
    intro x hx
    dsimp only
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hH_nonneg x (le_of_lt hx)),
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hre : (-(σ : ℂ) - 1).re = -σ - 1 := by simp
    rw [hre]
  have hP_nz_θ := thm_3_2_landau_positivity P a b H C θ hP_diff hP_ge1 hP_one
    hH_nonneg hH_int_real hθ0 hθ1 (fun s hs => (hH_int_and_eq s hs).2)
  intro s hs
  have hPs : P s ≠ 0 := hP_nz_θ s hs
  dsimp [P, familyEntireProduct] at hPs
  obtain ⟨hzd_pow_ne, hprod_ne⟩ := mul_ne_zero_iff.mp hPs
  refine ⟨?_, ?_⟩
  · intro hs1
    have hzd_ne : zetaDesing s ≠ 0 := fun h0 => hzd_pow_ne (by rw [h0, zero_pow (by omega)])
    rw [zetaDesing_eq_of_ne_one hs1] at hzd_ne
    exact (mul_ne_zero_iff.mp hzd_ne).2
  · intro ξ hξ
    rw [Finset.prod_ne_zero_iff] at hprod_ne
    exact hprod_ne ξ hξ

/-- Expanded product set `S(Λ) := {(ψ, j) : ψ ∈ X°, 0 ≤ j < k(ψ)}` used in Theorem 3.4. -/
noncomputable def expandedSet (L : CharacterLevel) : Finset (PrimitiveChar × ℕ) := by
  classical
  exact L.nonPrincipal.biUnion
    (fun ψ => (Finset.range (L.multiplicity ψ)).image (fun j => (ψ, j)))

/-- **Theorem 3.4 (Chebyshev Growth Implies Zero-Freeness — Unconditional)**:
If `G_m(Λ; y) ≤ y^θ` for all `y ≥ y₀` with `θ ∈ (0, 1)`, then `Λ` is zero-free above `θ`
without any external `LandauAnalyticBackend` hypothesis. -/
theorem thm_3_4_chebyshev_growth_zero_free_unconditional
    (L : CharacterLevel) (θ y₀ : ℝ) (γ_em : ℝ) (logDerivMap : PrimitiveChar → ℂ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hres1 : deriv (familyEntireProduct (expandedSet L) (fun p : PrimitiveChar × ℕ => p.1) (3 * L.orderParam + 1)) 1 =
      ((((3 * L.orderParam + 1 : ℕ) : ℂ) * (γ_em : ℂ) +
          ((∑ p ∈ expandedSet L, (logDerivMap p.1).re : ℝ) : ℂ))) *
        familyEntireProduct (expandedSet L) (fun p : PrimitiveChar × ℕ => p.1) (3 * L.orderParam + 1) 1)
    (hgrowth : ∀ y : ℝ, y₀ ≤ y → L.weightedSum γ_em logDerivMap y ≤ y ^ θ) :
    L.IsZeroFreeAbove θ := by
  classical
  let R : ℕ := 3 * L.orderParam + 1
  have hR_pos : (0 : ℝ) < (R : ℝ) := by dsimp [R]; positivity
  let S : Finset (PrimitiveChar × ℕ) := expandedSet L
  let τ : PrimitiveChar × ℕ → PrimitiveChar × ℕ := fun p => (p.1.inv, p.2)
  have hτ_mem : ∀ p ∈ S, τ p ∈ S ∧ τ (τ p) = p := by
    intro p hp
    rcases p with ⟨ψ, j⟩
    simp only [S, expandedSet, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq] at hp
    obtain ⟨ψ', hψ'_mem, j', hj'_lt, rfl, rfl⟩ := hp
    refine ⟨?_, ?_⟩
    · simp only [S, expandedSet, τ, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_range, Prod.mk.injEq]
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
    simp only [S, expandedSet, Finset.mem_biUnion, Finset.mem_image,
      Prod.mk.injEq] at hp
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
      dsimp [S, expandedSet]
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
  have hPT := prop_3_3_inversion_closed_landau S τ (fun p => p.1)
    R θ (R : ℝ) y₀ γ_em logDerivMap hτ_mem hψ_spec (by dsimp [R]; omega) hθ0 hθ1 hres1 hsum_bound
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
      simp only [S, expandedSet, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_range, Prod.mk.injEq]
      exact ⟨ψ, hmem_np, 0, hm_pos, rfl, rfl⟩
    exact (hPT s hs_re).2 (ψ, 0) hp_mem

/-- Canonical logarithmic derivative of `L(s, ψ)` at `s = 1`. -/
noncomputable def canonicalLogDerivMap (ψ : PrimitiveChar) : ℂ :=
  deriv (DirichletCharacter.LFunction ψ.char) 1 / DirichletCharacter.LFunction ψ.char 1

/-- Conjugate symmetry `L(z, χ⁻¹) = conj (L(conj z, χ))` for non-principal `χ`, proved on
`Re(z) > 1` from the Dirichlet series and extended to all `z ∈ ℂ` by analytic continuation. -/
lemma LFunction_inv_eq_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ⁻¹ =
      fun z : ℂ => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) := by
  have hχ_inv : χ⁻¹ ≠ 1 := by
    intro h1
    apply hχ
    have := congrArg Inv.inv h1
    simpa using this
  let F₁ : ℂ → ℂ := DirichletCharacter.LFunction χ⁻¹
  let F₂ : ℂ → ℂ := fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))
  have hF₁_diff : Differentiable ℂ F₁ := DirichletCharacter.differentiable_LFunction hχ_inv
  have hF₂_diff : Differentiable ℂ F₂ := fun z => by
    have h := ((DirichletCharacter.differentiable_LFunction hχ
      (starRingEnd ℂ z)).hasDerivAt.conj_conj).differentiableAt
    rw [starRingEnd_self_apply] at h
    exact h
  have heq_gt1 : ∀ z : ℂ, 1 < z.re → F₁ z = F₂ z := by
    intro z hz
    have hconj_re : 1 < (starRingEnd ℂ z).re := by simpa using hz
    dsimp [F₁, F₂]
    rw [DirichletCharacter.LFunction_eq_LSeries χ⁻¹ hz,
      DirichletCharacter.LFunction_eq_LSeries χ hconj_re]
    unfold LSeries
    rw [Complex.conj_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0, map_div₀]
      congr 1
      · by_cases hu : IsUnit (n : ZMod N)
        · have hmul_arg : (n : ZMod N) * Ring.inverse (n : ZMod N) = 1 :=
            Ring.mul_inverse_cancel (n : ZMod N) hu
          have hprod : χ n * χ⁻¹ n = 1 := by
            rw [MulChar.inv_apply, ← map_mul, hmul_arg, map_one]
          have hle1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
          have hle2 : ‖χ⁻¹ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ⁻¹ n
          have hprod_norm : ‖χ n‖ * ‖χ⁻¹ n‖ = 1 := by rw [← norm_mul, hprod, norm_one]
          have hun : ‖χ n‖ = 1 := by nlinarith [norm_nonneg (χ n), norm_nonneg (χ⁻¹ n)]
          have hconj : χ n * starRingEnd ℂ (χ n) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hun]; norm_num
          have hne0 : χ n ≠ 0 := by
            intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
          exact mul_left_cancel₀ hne0 (hprod.trans hconj.symm)
        · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, map_zero]
      · rw [Complex.cpow_conj, Complex.conj_natCast, starRingEnd_self_apply]
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm
  have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2_mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ, F₁ z = F₂ z := by
    have hev : ∀ᶠ z in nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ, z ∈ {w : ℂ | 1 < w.re} :=
      nhdsWithin_le_nhds (hopen1.mem_nhds h2_mem)
    exact hev.frequently.mono fun z hz => heq_gt1 z hz
  ext z
  exact (hF₁_diff.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hF₂_diff.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ (2 : ℂ)) hfreq (mem_univ z)

/-- Conjugate symmetry `canonicalLogDerivMap ψ.inv = starRingEnd ℂ (canonicalLogDerivMap ψ)`. -/
lemma canonicalLogDerivMap_inv (ψ : PrimitiveChar) (hψ : ψ.char ≠ 1) :
    canonicalLogDerivMap ψ.inv = starRingEnd ℂ (canonicalLogDerivMap ψ) := by
  unfold canonicalLogDerivMap PrimitiveChar.inv
  have hconj_fn := LFunction_inv_eq_conj ψ.char hψ
  have hval1 : DirichletCharacter.LFunction ψ.char⁻¹ 1 =
      starRingEnd ℂ (DirichletCharacter.LFunction ψ.char 1) := by
    rw [hconj_fn]
    simp only [map_one]
  have hderiv1 : deriv (DirichletCharacter.LFunction ψ.char⁻¹) 1 =
      starRingEnd ℂ (deriv (DirichletCharacter.LFunction ψ.char) 1) := by
    rw [hconj_fn]
    have hd := ((DirichletCharacter.differentiable_LFunction hψ (1 : ℂ)).hasDerivAt).conj_conj
    have h2 := hd.deriv
    simp only [map_one] at h2
    exact h2
  rw [hderiv1, hval1, map_div₀]

/-- For every `CharacterLevel L`, the sum of `canonicalLogDerivMap p.1` over `expandedSet L`
is purely real, hence equals `((∑ p ∈ expandedSet L, (canonicalLogDerivMap p.1).re : ℝ) : ℂ)`. -/
lemma sum_canonicalLogDerivMap_expandedSet_real (L : CharacterLevel) :
    (∑ p ∈ expandedSet L, canonicalLogDerivMap p.1) =
      ((∑ p ∈ expandedSet L, (canonicalLogDerivMap p.1).re : ℝ) : ℂ) := by
  classical
  let S := expandedSet L
  let τ : PrimitiveChar × ℕ → PrimitiveChar × ℕ := fun p => (p.1.inv, p.2)
  have hτ_mem : ∀ p ∈ S, τ p ∈ S ∧ τ (τ p) = p := by
    intro p hp
    rcases p with ⟨ψ, j⟩
    simp only [S, expandedSet, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq] at hp
    obtain ⟨ψ', hψ'_mem, j', hj'_lt, rfl, rfl⟩ := hp
    refine ⟨?_, ?_⟩
    · simp only [S, expandedSet, τ, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_range, Prod.mk.injEq]
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
  have hnp : ∀ p ∈ S, p.1.char ≠ 1 := by
    intro p hp
    rcases p with ⟨ψ, j⟩
    simp only [S, expandedSet, Finset.mem_biUnion, Finset.mem_image,
      Prod.mk.injEq] at hp
    obtain ⟨ψ', hψ'_mem, _, _, rfl, _⟩ := hp
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
  have hpair : ∑ p ∈ S, canonicalLogDerivMap (τ p).1 = ∑ p ∈ S, canonicalLogDerivMap p.1 := by
    refine Finset.sum_bij (fun p _ => τ p) (fun p hp => (hτ_mem p hp).1)
      (fun a ha b hb hab => ?_) (fun p hp => ⟨τ p, (hτ_mem p hp).1, (hτ_mem p hp).2⟩)
      (fun _ _ => rfl)
    calc
      a = τ (τ a) := ((hτ_mem a ha).2).symm
      _ = τ (τ b) := by rw [hab]
      _ = b := (hτ_mem b hb).2
  have h2 : (2 : ℂ) * ∑ p ∈ S, canonicalLogDerivMap p.1 =
      (2 : ℂ) * ((∑ p ∈ S, (canonicalLogDerivMap p.1).re : ℝ) : ℂ) := by
    calc
      (2 : ℂ) * ∑ p ∈ S, canonicalLogDerivMap p.1
          = (∑ p ∈ S, canonicalLogDerivMap p.1) + ∑ p ∈ S, canonicalLogDerivMap (τ p).1 := by
              rw [hpair]; ring
      _ = ∑ p ∈ S, (canonicalLogDerivMap p.1 + canonicalLogDerivMap p.1.inv) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ p ∈ S, (canonicalLogDerivMap p.1 + starRingEnd ℂ (canonicalLogDerivMap p.1)) := by
            refine Finset.sum_congr rfl fun p hp => by rw [canonicalLogDerivMap_inv p.1 (hnp p hp)]
      _ = ∑ p ∈ S, (2 : ℂ) * ((canonicalLogDerivMap p.1).re : ℂ) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Complex.add_conj]
            push_cast
            ring
      _ = (2 : ℂ) * ((∑ p ∈ S, (canonicalLogDerivMap p.1).re : ℝ) : ℂ) := by
            rw [← Finset.mul_sum, Complex.ofReal_sum]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2

/-- Unconditional derivative of `zetaDesing` at `s = 1`
equals `Real.eulerMascheroniConstant`, proved from Mathlib's Laurent constant
`riemannZeta_sub_one_inv_tendsto`. -/
theorem hasDerivAt_zetaDesing_one :
    HasDerivAt zetaDesing (Real.eulerMascheroniConstant : ℂ) 1 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun s : ℂ => riemannZeta s - (s - 1)⁻¹)
      (nhdsWithin 1 {1}ᶜ) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    simpa only [one_div] using tendsto_riemannZeta_sub_one_div
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs_ne : s ≠ 1 := hs
  have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne
  rw [slope_def_field, zetaDesing_eq_of_ne_one hs_ne, zetaDesing_one]
  field_simp [hs_sub]

theorem deriv_zetaDesing_one :
    deriv zetaDesing 1 = (Real.eulerMascheroniConstant : ℂ) :=
  hasDerivAt_zetaDesing_one.deriv

/-- **Unconditional Residue Identity at `s = 1` (`hres1`)**:
Proves `deriv P 1 = ((3o + 1) γ_EM + ∑ Re(L'(1, ψ)/L(1, ψ))) * P(1)` directly from
`HasDerivAt zetaDesing Real.eulerMascheroniConstant 1` and Mathlib's `LFunction` properties. -/
theorem familyEntireProduct_deriv_one_unconditional
    (L : CharacterLevel)
    (hzd_deriv1 : deriv zetaDesing 1 = (Real.eulerMascheroniConstant : ℂ)) :
    deriv (familyEntireProduct (expandedSet L) (fun p => p.1) (3 * L.orderParam + 1)) 1 =
      ((((3 * L.orderParam + 1 : ℕ) : ℂ) * (Real.eulerMascheroniConstant : ℂ) +
          ((∑ p ∈ expandedSet L, (canonicalLogDerivMap p.1).re : ℝ) : ℂ))) *
        familyEntireProduct (expandedSet L) (fun p => p.1) (3 * L.orderParam + 1) 1 := by
  classical
  let R : ℕ := 3 * L.orderParam + 1
  let S := expandedSet L
  have hnonprin : ∀ p ∈ S, p.1.char ≠ 1 := by
    intro p hp
    rcases p with ⟨ψ, j⟩
    simp only [S, expandedSet, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq] at hp
    obtain ⟨ψ', hψ'_mem, _, _, rfl, _⟩ := hp
    unfold CharacterLevel.nonPrincipal at hψ'_mem
    rw [Finset.mem_erase] at hψ'_mem
    intro hchar1
    apply hψ'_mem.1
    cases ψ' with
    | mk m nz c hp =>
      simp only at hchar1
      have hcond1 : c.conductor = 1 := by rw [hchar1]; exact DirichletCharacter.conductor_one
      have hm1 : m = 1 := by rw [DirichletCharacter.isPrimitive_def] at hp; rw [← hp, hcond1]
      subst hm1
      unfold PrimitiveChar.one
      congr 1
  let F_pow : ℂ → ℂ := fun z => zetaDesing z ^ R
  let F_prod : ℂ → ℂ := fun z => ∏ p ∈ S, DirichletCharacter.LFunction p.1.char z
  have hF_pow_diff : DifferentiableAt ℂ F_pow 1 := (differentiable_zetaDesing.pow R) 1
  have hF_prod_diff : DifferentiableAt ℂ F_prod 1 :=
    differentiableAt_finset_prod S _ 1 fun p hp =>
      DirichletCharacter.differentiable_LFunction (hnonprin p hp) 1
  have hF_pow_one : F_pow 1 = 1 := by dsimp [F_pow]; rw [zetaDesing_one, one_pow]
  have hF_prod_ne : F_prod 1 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      DirichletCharacter.LFunction_ne_zero_of_one_le_re p.1.char (Or.inl (hnonprin p hp)) (by norm_num)
  have hd_pow : deriv F_pow 1 = (R : ℂ) * (Real.eulerMascheroniConstant : ℂ) := by
    have hd : HasDerivAt (fun z => zetaDesing z ^ R)
        ((R : ℂ) * zetaDesing 1 ^ (R - 1) * deriv zetaDesing 1) 1 :=
      (differentiable_zetaDesing 1).hasDerivAt.pow R
    rw [hd.deriv, zetaDesing_one, one_pow, mul_one, hzd_deriv1]
  have hd_prod : deriv F_prod 1 =
      (∑ p ∈ S, canonicalLogDerivMap p.1) * F_prod 1 := by
    have hdiv := deriv_finset_prod_div S _ 1
      (fun p hp => DirichletCharacter.differentiable_LFunction (hnonprin p hp) 1)
      (fun p hp => DirichletCharacter.LFunction_ne_zero_of_one_le_re p.1.char (Or.inl (hnonprin p hp)) (by norm_num))
    exact (div_eq_iff hF_prod_ne).mp hdiv
  change deriv (fun z => F_pow z * F_prod z) 1 = _
  rw [deriv_fun_mul hF_pow_diff hF_prod_diff, hd_pow, hd_prod, hF_pow_one, one_mul,
    sum_canonicalLogDerivMap_expandedSet_real L]
  change ((R : ℂ) * (Real.eulerMascheroniConstant : ℂ)) * F_prod 1 +
      ((∑ p ∈ S, (canonicalLogDerivMap p.1).re : ℝ) : ℂ) * F_prod 1 =
    ((R : ℂ) * (Real.eulerMascheroniConstant : ℂ) +
      ((∑ p ∈ S, (canonicalLogDerivMap p.1).re : ℝ) : ℂ)) * (F_pow 1 * F_prod 1)
  rw [hF_pow_one, one_mul]
  ring

theorem familyEntireProduct_deriv_one_unconditional_final (L : CharacterLevel) :
    deriv (familyEntireProduct (expandedSet L) (fun p => p.1) (3 * L.orderParam + 1)) 1 =
      ((((3 * L.orderParam + 1 : ℕ) : ℂ) * (Real.eulerMascheroniConstant : ℂ) +
          ((∑ p ∈ expandedSet L, (canonicalLogDerivMap p.1).re : ℝ) : ℂ))) *
        familyEntireProduct (expandedSet L) (fun p => p.1) (3 * L.orderParam + 1) 1 :=
  familyEntireProduct_deriv_one_unconditional L deriv_zetaDesing_one

end GRHIteratedThetaLifts.Section3B
