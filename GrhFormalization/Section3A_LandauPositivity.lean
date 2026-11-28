/-
Copyright (c) 2026 Nillohit Roy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nillohit Roy
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open Complex Real Filter Topology MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace GRHIteratedThetaLifts.Section3A

noncomputable def logDeriv (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  deriv P s / P s

def halfPlane (σ₀ : ℝ) : Set ℂ :=
  {s : ℂ | σ₀ < s.re}

noncomputable def landauRHS (P : ℂ → ℂ) (a b : ℂ) (C θ : ℝ) : ℂ → ℂ :=
  Function.update
    (fun s => (logDeriv P s - (a + b * s)) / (s * (s - 1)) + (C : ℂ) / (s - (θ : ℂ)))
    1
    ((deriv (logDeriv P) 1 - b) + (C : ℂ) / (1 - (θ : ℂ)))

lemma landauRHS_eq_of_ne_one (P : ℂ → ℂ) (a b : ℂ) (C θ : ℝ) {s : ℂ} (hs : s ≠ 1) :
    landauRHS P a b C θ s =
      (logDeriv P s - (a + b * s)) / (s * (s - 1)) + (C : ℂ) / (s - (θ : ℂ)) :=
  Function.update_of_ne hs _ _

private lemma re_gt_ne_zero {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {s : ℂ} (hs : s ∈ halfPlane σ₀) : s ≠ 0 := by
  intro h0
  have hgt : σ₀ < (0 : ℂ).re := h0 ▸ hs
  rw [zero_re] at hgt
  exact lt_irrefl 0 (lt_trans hσ₀ hgt)

private lemma differentiableOn_logDeriv (P : ℂ → ℂ) (σ₀ : ℝ)
    (hP_diff : Differentiable ℂ P)
    (hP_nz : ∀ s : ℂ, σ₀ < s.re → P s ≠ 0) :
    DifferentiableOn ℂ (logDeriv P) (halfPlane σ₀) := by
  have hderivP : Differentiable ℂ (deriv P) :=
    fun s => (hP_diff.analyticAt s).deriv.differentiableAt
  intro s hs
  exact (hderivP s).differentiableWithinAt.div (hP_diff s).differentiableWithinAt (hP_nz s hs)

private lemma differentiableOn_pole (C θ σ₀ : ℝ) (hθ_le : θ ≤ σ₀) :
    DifferentiableOn ℂ (fun s : ℂ => (C : ℂ) / (s - (θ : ℂ))) (halfPlane σ₀) := by
  have hnum : Differentiable ℂ (fun _ : ℂ => (C : ℂ)) := differentiable_const _
  have hden : Differentiable ℂ (fun s : ℂ => s - (θ : ℂ)) :=
    differentiable_id.sub (differentiable_const _)
  intro s hs
  refine (hnum s).differentiableWithinAt.div (hden s).differentiableWithinAt ?_
  intro hsub
  rw [sub_eq_zero] at hsub
  have hre : s.re = θ := by rw [hsub, Complex.ofReal_re]
  have hgt : σ₀ < θ := hre ▸ hs
  exact not_le_of_gt hgt hθ_le

theorem differentiableOn_landauRHS
    (P : ℂ → ℂ) (a b : ℂ) (C θ σ₀ : ℝ)
    (hP_diff : Differentiable ℂ P)
    (hP_nz : ∀ s : ℂ, σ₀ < s.re → P s ≠ 0)
    (hP_one : deriv P 1 - (a + b) * P 1 = 0)
    (hθ0 : 0 < θ) (hθ_le : θ ≤ σ₀) :
    DifferentiableOn ℂ (landauRHS P a b C θ) (halfPlane σ₀) := by
  have hσ₀_pos : 0 < σ₀ := lt_of_lt_of_le hθ0 hθ_le
  have hU_open : IsOpen (halfPlane σ₀) := isOpen_lt continuous_const Complex.continuous_re
  have hL_diffOn := differentiableOn_logDeriv P σ₀ hP_diff hP_nz
  have hPole_diffOn := differentiableOn_pole C θ σ₀ hθ_le
  have haff_diff : Differentiable ℂ (fun s : ℂ => a + b * s) :=
    (differentiable_const a).add ((differentiable_const b).mul differentiable_id)
  have hquad_diff : Differentiable ℂ (fun s : ℂ => s * (s - 1)) :=
    differentiable_id.mul (differentiable_id.sub (differentiable_const 1))
  by_cases h1U : (1 : ℂ) ∈ halfPlane σ₀
  · have hL1 : logDeriv P 1 = a + b := by
      dsimp [logDeriv]
      rw [div_eq_iff (hP_nz 1 h1U)]
      exact sub_eq_zero.mp hP_one
    let num : ℂ → ℂ := fun s => logDeriv P s - (a + b * s)
    have hnum_diffOn : DifferentiableOn ℂ num (halfPlane σ₀) :=
      hL_diffOn.sub haff_diff.differentiableOn
    have hnum1 : num 1 = 0 := by
      dsimp [num]
      rw [hL1]
      ring
    have hderiv_num1 : deriv num 1 = deriv (logDeriv P) 1 - b := by
      have hd1 : HasDerivAt (logDeriv P) (deriv (logDeriv P) 1) 1 :=
        (hL_diffOn.differentiableAt (hU_open.mem_nhds h1U)).hasDerivAt
      have hd2 : HasDerivAt (fun s => a + b * s) b 1 := by
        simpa using ((hasDerivAt_id (1 : ℂ)).const_mul b).const_add a
      exact (hd1.sub hd2).deriv
    have hdslope_diffOn : DifferentiableOn ℂ (dslope num 1) (halfPlane σ₀) :=
      (Complex.differentiableOn_dslope (hU_open.mem_nhds h1U)).mpr hnum_diffOn
    have hg_ext_diffOn : DifferentiableOn ℂ (fun s => dslope num 1 s / s) (halfPlane σ₀) :=
      fun s hs => (hdslope_diffOn s hs).div
        (differentiable_id s).differentiableWithinAt (re_gt_ne_zero hσ₀_pos hs)
    have heq_U : EqOn (landauRHS P a b C θ)
        (fun s => dslope num 1 s / s + (C : ℂ) / (s - (θ : ℂ))) (halfPlane σ₀) := by
      intro s hs
      by_cases hs1 : s = 1
      · subst hs1
        dsimp [landauRHS]
        rw [Function.update_self, dslope_same, hderiv_num1, div_one]
      · have hs0 : s ≠ 0 := re_gt_ne_zero hσ₀_pos hs
        have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
        rw [landauRHS_eq_of_ne_one P a b C θ hs1]
        dsimp only
        rw [dslope_of_ne num hs1, slope_def_field, hnum1, sub_zero]
        congr 1
        dsimp [num]
        field_simp [hs0, hs1']
    exact DifferentiableOn.congr (hg_ext_diffOn.add hPole_diffOn) heq_U
  · have heq : EqOn (landauRHS P a b C θ)
        (fun z => (logDeriv P z - (a + b * z)) / (z * (z - 1)) + (C : ℂ) / (z - (θ : ℂ)))
        (halfPlane σ₀) :=
      fun z hz => landauRHS_eq_of_ne_one P a b C θ (fun h1 => h1U (h1 ▸ hz))
    have hmain : DifferentiableOn ℂ
        (fun z => (logDeriv P z - (a + b * z)) / (z * (z - 1)) + (C : ℂ) / (z - (θ : ℂ)))
        (halfPlane σ₀) := by
      intro s hs
      have hs1 : s ≠ 1 := fun h1 => h1U (h1 ▸ hs)
      have hs0 : s ≠ 0 := re_gt_ne_zero hσ₀_pos hs
      refine (((hL_diffOn s hs).sub (haff_diff s).differentiableWithinAt).div
        (hquad_diff s).differentiableWithinAt
        (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).add (hPole_diffOn s hs)
    exact DifferentiableOn.congr hmain heq

/-- 1-D complex Taylor series on `Metric.eball c R` from `DifferentiableOn ℂ F (Metric.closedBall c R)`. -/
theorem taylor_hasSum_of_differentiableOn_closedBall
    {F : ℂ → ℂ} {c w : ℂ} {R : ℝ≥0}
    (hF : DifferentiableOn ℂ F (Metric.closedBall c (R : ℝ)))
    (hR : 0 < R) (hw : ‖w‖ < (R : ℝ)) :
    HasSum (fun n : ℕ => iteratedDeriv n F c / (n.factorial : ℂ) * w ^ n) (F (c + w)) := by
  have hfps : HasFPowerSeriesOnBall F (cauchyPowerSeries F c (R : ℝ)) c (R : ℝ≥0∞) :=
    hF.hasFPowerSeriesOnBall hR
  have hw_eball : w ∈ Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (NNReal.coe_pos.mpr hR)).mpr hw
  have hsum := hfps.hasSum hw_eball
  convert hsum using 1
  ext n
  have hfact := hfps.factorial_smul w n
  have hmap : (iteratedFDeriv ℂ n F c fun _ => w) =
      w ^ n * (iteratedFDeriv ℂ n F c fun _ => (1 : ℂ)) := by
    have hsmul := (iteratedFDeriv ℂ n F c).map_smul_univ (fun _ : Fin n => w) (fun _ : Fin n => (1 : ℂ))
    simpa [smul_eq_mul, Finset.prod_const, Fintype.card_fin] using hsmul
  rw [hmap, ← iteratedDeriv_eq_iteratedFDeriv] at hfact
  simp only [nsmul_eq_mul] at hfact
  have hfn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply mul_left_cancel₀ hfn
  calc
    (n.factorial : ℂ) * (iteratedDeriv n F c / (n.factorial : ℂ) * w ^ n)
        = iteratedDeriv n F c * w ^ n := by field_simp [hfn]
    _ = w ^ n * iteratedDeriv n F c := mul_comm _ _
    _ = (n.factorial : ℂ) * ((cauchyPowerSeries F c (R : ℝ) n) fun _ => w) := hfact.symm

private lemma abs_log_pow_le_rpow {k : ℕ} {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    |Real.log x| ^ k ≤ max 1 ((k : ℝ) / ε) ^ k * x ^ ε := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases hk0 : k = 0
  · subst hk0
    simp only [pow_zero]
    have hC1 : (1 : ℝ) ≤ max 1 ((0 : ℝ) / ε) ^ 0 := by simp
    have hx1 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
    nlinarith
  · have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
    have hε' : 0 < ε / (k : ℝ) := div_pos hε hk_pos
    have h1 : (ε / (k : ℝ)) * Real.log x = Real.log (x ^ (ε / (k : ℝ))) := by
      rw [Real.log_rpow hx_pos]
    have h2 : Real.log (x ^ (ε / (k : ℝ))) ≤ x ^ (ε / (k : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx_pos _)
    have hlog_le' : Real.log x ≤ x ^ (ε / (k : ℝ)) / (ε / (k : ℝ)) := by
      rw [le_div_iff₀ hε']
      linarith
    have hlog_le : Real.log x ≤ ((k : ℝ) / ε) * x ^ (ε / (k : ℝ)) := by
      convert hlog_le' using 1
      field_simp [ne_of_gt hε]
    have hbase : |Real.log x| ≤ max 1 ((k : ℝ) / ε) * x ^ (ε / (k : ℝ)) := by
      rw [abs_of_nonneg hlog_nonneg]
      exact hlog_le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hx_pos.le _))
    calc
      |Real.log x| ^ k
          ≤ (max 1 ((k : ℝ) / ε) * x ^ (ε / (k : ℝ))) ^ k :=
            pow_le_pow_left₀ (abs_nonneg _) hbase k
      _ = max 1 ((k : ℝ) / ε) ^ k * (x ^ (ε / (k : ℝ))) ^ k := mul_pow _ _ k
      _ = max 1 ((k : ℝ) / ε) ^ k * (x ^ (ε / (k : ℝ))) ^ (k : ℝ) := by
            rw [← Real.rpow_natCast (x ^ (ε / (k : ℝ))) k]
      _ = max 1 ((k : ℝ) / ε) ^ k * x ^ ε := by
            rw [← Real.rpow_mul hx_pos.le]
            congr 2
            field_simp

private lemma aestronglyMeasurable_ofReal_cpow_Ioi (w : ℂ) :
    AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ w) (volume.restrict (Ioi (1 : ℝ))) := by
  have hcontOn : ContinuousOn (fun x : ℝ => (x : ℂ) ^ w) (Ioi (1 : ℝ)) := by
    refine ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const ?_
    intro x hx
    left
    rw [Complex.ofReal_re]
    exact lt_trans zero_lt_one hx
  exact hcontOn.aestronglyMeasurable measurableSet_Ioi

private lemma integrableOn_mellin_log_pow_of_gt
    (H : ℝ → ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_meas : AEStronglyMeasurable H (volume.restrict (Ioi (1 : ℝ))))
    {σ_dom : ℝ} (hH_dom : IntegrableOn (fun x : ℝ => H x * x ^ (-σ_dom - 1)) (Ioi 1))
    (k : ℕ) {σ₀ : ℝ} (hσ_lt : σ_dom < σ₀) {z : ℂ} (hz : σ₀ ≤ z.re) :
    IntegrableOn (fun x : ℝ => (H x : ℂ) * ((Real.log x : ℂ) ^ k) * (x : ℂ) ^ (-z - 1)) (Ioi 1) := by
  let ε : ℝ := σ₀ - σ_dom
  have hε_pos : 0 < ε := sub_pos.mpr hσ_lt
  let C_log : ℝ := max 1 ((k : ℝ) / ε) ^ k
  have hlog_meas : Measurable (fun x : ℝ => (Real.log x : ℂ)) :=
    Complex.measurable_ofReal.comp Real.measurable_log
  refine (hH_dom.const_mul C_log).mono' ?_ ?_
  · exact ((Complex.measurable_ofReal.comp_aemeasurable hH_meas.aemeasurable).mul
      (hlog_meas.pow_const k).aemeasurable).aestronglyMeasurable.mul
      (aestronglyMeasurable_ofReal_cpow_Ioi (-z - 1))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx_ge1 : 1 ≤ x := le_of_lt hx
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hH0 : 0 ≤ H x := hH_nonneg x hx_ge1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hH0,
      norm_pow, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hlog_pow : |Real.log x| ^ k ≤ C_log * x ^ ε := abs_log_pow_le_rpow hε_pos hx_ge1
    have hre : (-z - 1).re ≤ -σ₀ - 1 := by
      rw [sub_re, neg_re, one_re]
      exact sub_le_sub_right (neg_le_neg hz) 1
    calc
      H x * |Real.log x| ^ k * x ^ (-z - 1).re
          ≤ H x * (C_log * x ^ ε) * x ^ (-σ₀ - 1) := by
            refine mul_le_mul ?_ (Real.rpow_le_rpow_of_exponent_le hx_ge1 hre)
              (Real.rpow_nonneg hx_pos.le _) (mul_nonneg hH0 (by positivity))
            exact mul_le_mul_of_nonneg_left hlog_pow hH0
      _ = C_log * (H x * (x ^ ε * x ^ (-σ₀ - 1))) := by ring
      _ = C_log * (H x * x ^ (-σ_dom - 1)) := by
            have hexp : ε + (-σ₀ - 1) = -σ_dom - 1 := by dsimp [ε]; ring
            rw [← Real.rpow_add hx_pos, hexp]

private lemma integrableOn_mellin_log_pow
    (H : ℝ → ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_meas : AEStronglyMeasurable H (volume.restrict (Ioi (1 : ℝ))))
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (k : ℕ) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {z : ℂ} (hz : σ₀ ≤ z.re) :
    IntegrableOn (fun x : ℝ => (H x : ℂ) * ((Real.log x : ℂ) ^ k) * (x : ℂ) ^ (-z - 1)) (Ioi 1) :=
  integrableOn_mellin_log_pow_of_gt H hH_nonneg hH_meas
    (hH_int ((1 + σ₀) / 2) (by linarith)) k (by linarith) hz

private lemma aestronglyMeasurable_of_mellin_int
    (H : ℝ → ℝ)
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) :
    AEStronglyMeasurable H (volume.restrict (Ioi (1 : ℝ))) := by
  have hint2 := (hH_int 2 (by norm_num)).aestronglyMeasurable
  have hpow_cont : Continuous (fun x : ℝ => x ^ (3 : ℝ)) :=
    Continuous.rpow_const continuous_id (fun _ => Or.inr (by norm_num))
  have hmul : AEStronglyMeasurable
      (fun x : ℝ => (H x * x ^ (-(2 : ℝ) - 1)) * x ^ (3 : ℝ))
      (volume.restrict (Ioi (1 : ℝ))) :=
    hint2.mul hpow_cont.aestronglyMeasurable
  refine hmul.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  rw [mul_assoc, ← Real.rpow_add hx_pos]
  norm_num

private lemma hasDerivAt_mellin_integrand (c : ℂ) {x : ℝ} (hx : 1 < x) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => c * (x : ℂ) ^ (-w - 1))
      (c * ((x : ℂ) ^ (-z - 1) * Complex.log (x : ℂ) * (-1))) z := by
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hx))
  have hd1 : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
    simpa using (hasDerivAt_id z).neg.sub_const (1 : ℂ)
  exact (hd1.const_cpow (Or.inl hx_ne)).const_mul c

private lemma norm_mellin_integrand_deriv (h : ℝ) (k : ℕ) {x : ℝ} (hx : 1 < x) (z : ℂ) :
    ‖(h : ℂ) * ((Real.log x : ℂ) ^ k) *
        ((x : ℂ) ^ (-z - 1) * Complex.log (x : ℂ) * (-1))‖ =
      |h| * |Real.log x| ^ (k + 1) * x ^ (-z - 1).re := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos,
    ← Complex.ofReal_log hx_pos.le, Complex.norm_real, Real.norm_eq_abs, norm_neg, norm_one,
    mul_one, pow_succ]
  ring

private lemma norm_mellin_deriv_le
    {H : ℝ → ℝ} {k : ℕ} {σ₀ ε C_log : ℝ} {x : ℝ} {z : ℂ}
    (hx : 1 < x) (hH0 : 0 ≤ H x) (hz_re : σ₀ ≤ z.re)
    (hCnn : 0 ≤ C_log)
    (hlog_pow : |Real.log x| ^ (k + 1) ≤ C_log * x ^ ε) :
    ‖(H x : ℂ) * ((Real.log x : ℂ) ^ k) *
        ((x : ℂ) ^ (-z - 1) * Complex.log (x : ℂ) * (-1))‖ ≤
      C_log * (H x * x ^ (-(σ₀ - ε) - 1)) := by
  have hx_ge1 : 1 ≤ x := le_of_lt hx
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  rw [norm_mellin_integrand_deriv (H x) k hx z, abs_of_nonneg hH0]
  have hxε : 0 ≤ x ^ ε := Real.rpow_nonneg hx_pos.le _
  have hre : (-z - 1).re ≤ -σ₀ - 1 := by
    rw [sub_re, neg_re, one_re]
    exact sub_le_sub_right (neg_le_neg hz_re) 1
  have h1 : H x * |Real.log x| ^ (k + 1) ≤ H x * (C_log * x ^ ε) :=
    mul_le_mul_of_nonneg_left hlog_pow hH0
  have h2 : x ^ (-z - 1).re ≤ x ^ (-σ₀ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx_ge1 hre
  have h3 : x ^ ε * x ^ (-σ₀ - 1) = x ^ (-(σ₀ - ε) - 1) := by
    rw [← Real.rpow_add hx_pos]; congr 1; ring
  calc H x * |Real.log x| ^ (k + 1) * x ^ (-z - 1).re
      ≤ (H x * (C_log * x ^ ε)) * x ^ (-σ₀ - 1) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hx_pos.le _)
          (mul_nonneg hH0 (mul_nonneg hCnn hxε))
    _ = C_log * (H x * (x ^ ε * x ^ (-σ₀ - 1))) := by ring
    _ = C_log * (H x * x ^ (-(σ₀ - ε) - 1)) := by rw [h3]

private lemma hasDerivAt_mellin_log_pow_aux_of_gt
    (H : ℝ → ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_meas : AEStronglyMeasurable H (volume.restrict (Ioi (1 : ℝ))))
    {σ_min : ℝ} (hH_int : ∀ σ : ℝ, σ_min < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (k : ℕ) (s : ℂ) (σ₀ δ ε C_log : ℝ)
    (_hσ₀_gt : σ_min < σ₀) (hσ₀_lt : σ₀ < s.re) (hδ_pos : 0 < δ) (hε_pos : 0 < ε)
    (hσ_dom_gt : σ_min < σ₀ - ε) (hδ_le : δ ≤ s.re - σ₀)
    (hC : C_log = max 1 ((k + 1 : ℝ) / ε) ^ (k + 1)) :
    HasDerivAt
      (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ k) * (x : ℂ) ^ (-z - 1))
      (- ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ (k + 1)) * (x : ℂ) ^ (-s - 1)) s := by
  let coeff : ℝ → ℂ := fun x => (H x : ℂ) * ((Real.log x : ℂ) ^ k)
  let F : ℂ → ℝ → ℂ := fun z x => coeff x * (x : ℂ) ^ (-z - 1)
  let F' : ℂ → ℝ → ℂ := fun z x => coeff x * ((x : ℂ) ^ (-z - 1) * Complex.log (x : ℂ) * (-1))
  let bound : ℝ → ℝ := fun x => C_log * (H x * x ^ (-(σ₀ - ε) - 1))
  have hlog_meas : Measurable (fun x : ℝ => (Real.log x : ℂ)) :=
    Complex.measurable_ofReal.comp Real.measurable_log
  have hcoeff_meas : AEStronglyMeasurable coeff (volume.restrict (Ioi (1 : ℝ))) :=
    ((Complex.measurable_ofReal.comp_aemeasurable hH_meas.aemeasurable).mul
      (hlog_meas.pow_const k).aemeasurable).aestronglyMeasurable
  have hint_dom : Integrable bound (volume.restrict (Ioi (1 : ℝ))) :=
    (hH_int (σ₀ - ε) hσ_dom_gt).const_mul C_log
  have hball_re : ∀ z ∈ Metric.ball s δ, σ₀ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs : |z.re - s.re| ≤ ‖z - s‖ := by
      simpa [sub_re] using Complex.abs_re_le_norm (z - s)
    have hlow : s.re - δ ≤ z.re := by linarith [(abs_le.mp (habs.trans hz.le)).1]
    linarith
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds s hδ_pos)
    ?_ ?_ ?_ ?_ hint_dom ?_
  · have heq : (- ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ (k + 1)) * (x : ℂ) ^ (-s - 1))
        = ∫ x in Ioi (1 : ℝ), F' s x := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun (s := Ioi (1 : ℝ)) measurableSet_Ioi fun x hx => ?_
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      dsimp [F', coeff]
      rw [Complex.ofReal_log hx_pos.le, pow_succ]
      ring
    rw [heq]
    have hd2 := hd.2
    dsimp only [F, coeff] at hd2
    exact hd2
  · filter_upwards [Metric.ball_mem_nhds s hδ_pos] with z hz
    exact (integrableOn_mellin_log_pow_of_gt H hH_nonneg hH_meas
      (hH_int ((σ_min + σ₀) / 2) (by linarith)) k (by linarith) (hball_re z hz)).aestronglyMeasurable
  · exact integrableOn_mellin_log_pow_of_gt H hH_nonneg hH_meas
      (hH_int ((σ_min + σ₀) / 2) (by linarith)) k (by linarith) hσ₀_lt.le
  · have hlogC : AEStronglyMeasurable (fun x : ℝ => Complex.log (x : ℂ))
        (volume.restrict (Ioi (1 : ℝ))) :=
      (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable
    have hinner : AEStronglyMeasurable
        (fun x : ℝ => (x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * (-1 : ℂ))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((aestronglyMeasurable_ofReal_cpow_Ioi (-s - 1)).mul hlogC).mul
        aestronglyMeasurable_const
    exact hcoeff_meas.mul hinner
  · rw [ae_restrict_iff' measurableSet_Ioi]
    have hCnn : 0 ≤ C_log := by
      rw [hC]; exact pow_nonneg (zero_le_one.trans (le_max_left 1 _)) (k + 1)
    refine Eventually.of_forall fun x hx z hz => ?_
    have hlog_pow : |Real.log x| ^ (k + 1) ≤ C_log * x ^ ε := by
      rw [hC]
      simpa [Nat.cast_add_one] using abs_log_pow_le_rpow (k := k + 1) hε_pos (le_of_lt hx)
    exact norm_mellin_deriv_le hx (hH_nonneg x (le_of_lt hx)) (hball_re z hz) hCnn hlog_pow
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun x hx z _ =>
      hasDerivAt_mellin_integrand (coeff x) hx z

private theorem iteratedDeriv_mellin_integral_of_gt
    (H : ℝ → ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_meas : AEStronglyMeasurable H (volume.restrict (Ioi (1 : ℝ))))
    {σ_min : ℝ} (hH_int : ∀ σ : ℝ, σ_min < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (k : ℕ) {s : ℂ} (hs : σ_min < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)) s =
      (-1 : ℂ) ^ k *
        ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ k) * (x : ℂ) ^ (-s - 1) := by
  induction k generalizing s with
  | zero =>
    simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {z : ℂ | σ_min < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have heqOn : EqOn
        (iteratedDeriv k (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)))
        (fun z : ℂ => (-1 : ℂ) ^ k *
          ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ k) * (x : ℂ) ^ (-z - 1))
        {z : ℂ | σ_min < z.re} := fun z hz => ih hz
    rw [Filter.EventuallyEq.deriv_eq (heqOn.eventuallyEq_of_mem (hopen.mem_nhds hs))]
    have hd := (hasDerivAt_mellin_log_pow_aux_of_gt H hH_nonneg hH_meas hH_int k s
      ((σ_min + s.re) / 2) ((s.re - (σ_min + s.re) / 2) / 2)
      (((σ_min + s.re) / 2 - σ_min) / 2)
      (max 1 ((k + 1 : ℝ) / (((σ_min + s.re) / 2 - σ_min) / 2)) ^ (k + 1))
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) rfl).const_mul ((-1 : ℂ) ^ k)
    rw [hd.deriv, pow_succ]
    ring

theorem iteratedDeriv_mellin_integral
    (H : ℝ → ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)) s =
      (-1 : ℂ) ^ k *
        ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ k) * (x : ℂ) ^ (-s - 1) :=
  iteratedDeriv_mellin_integral_of_gt H hH_nonneg (aestronglyMeasurable_of_mellin_int H hH_int) hH_int k hs

private lemma integrableOn_mellin_real_term
    (H : ℝ → ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_meas : AEStronglyMeasurable H (volume.restrict (Ioi (1 : ℝ))))
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    IntegrableOn
      (fun x : ℝ => H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ))
      (Ioi 1) := by
  have hk := (integrableOn_mellin_log_pow H hH_nonneg hH_meas hH_int n
    (show (1 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≤ (2 : ℂ).re by norm_num)).norm.const_mul (r ^ n)
  have hmid_meas : Measurable (fun x : ℝ => (r * Real.log x) ^ n / (n.factorial : ℝ)) :=
    ((measurable_const.mul Real.measurable_log).pow_const n).div_const (n.factorial : ℝ)
  have hpow_meas : Measurable (fun x : ℝ => x ^ (-3 : ℝ)) :=
    Measurable.pow_const measurable_id (-3 : ℝ)
  refine hk.mono' ?_ ?_
  · exact (hH_meas.mul hmid_meas.aemeasurable.aestronglyMeasurable).mul
      hpow_meas.aemeasurable.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hfact_ge1 : (1 : ℝ) ≤ (n.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos n)
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hH0, norm_pow, Complex.norm_real, Real.norm_of_nonneg hlog0,
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hre2 : (-(2 : ℂ) - 1).re = -3 := by norm_num
    rw [hre2, mul_pow]
    have hdiv_le : r ^ n * Real.log x ^ n / (n.factorial : ℝ) ≤ r ^ n * Real.log x ^ n :=
      div_le_self (by positivity) hfact_ge1
    calc
      H x * (r ^ n * Real.log x ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ)
          ≤ H x * (r ^ n * Real.log x ^ n) * x ^ (-3 : ℝ) := by gcongr
      _ = r ^ n * (H x * Real.log x ^ n * x ^ (-3 : ℝ)) := by ring

private lemma integral_mellin_real_eq
    (H : ℝ → ℝ)
    {σ : ℝ} :
    ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ x in Ioi (1 : ℝ), H x * x ^ (-σ - 1) : ℝ) : ℂ) := by
  have heq : EqOn (fun x : ℝ => (H x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1))
      (fun x : ℝ => ((H x * x ^ (-σ - 1) : ℝ) : ℂ)) (Ioi (1 : ℝ)) := by
    intro x hx
    dsimp only
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hcpow : (x : ℂ) ^ (-(σ : ℂ) - 1) = ((x ^ (-σ - 1) : ℝ) : ℂ) := by
      have hexp : (-(σ : ℂ) - 1) = (((-σ - 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [hexp, Complex.ofReal_cpow hx_pos.le]
    rw [hcpow, Complex.ofReal_mul]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi heq]
  exact integral_ofReal (𝕜 := ℂ)

private lemma tendsto_ennreal_mellin_partial_sums
    {H : ℝ → ℝ} {x r : ℝ} (hx : 1 < x) (hH0 : 0 ≤ H x) (hr : 0 ≤ r) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ENNReal.ofReal (H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ)))
      atTop
      (𝓝 (ENNReal.ofReal (H x * x ^ (-(2 - r) - 1)))) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
  have hexp_hasSum : HasSum (fun n : ℕ => (r * Real.log x) ^ n / (n.factorial : ℝ))
      (Real.exp (r * Real.log x)) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (NormedSpace.expSeries_div_summable (r * Real.log x)).hasSum
  have hmul_hasSum : HasSum
      (fun n : ℕ => H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ))
      (H x * x ^ (-(2 - r) - 1)) := by
    have h1 := (hexp_hasSum.mul_left (H x)).mul_right (x ^ (-3 : ℝ))
    have hval : H x * Real.exp (r * Real.log x) * x ^ (-3 : ℝ) = H x * x ^ (-(2 - r) - 1) := by
      rw [mul_comm r (Real.log x), Real.exp_mul, Real.exp_log hx_pos, mul_assoc, ← Real.rpow_add hx_pos]
      congr 2
      ring
    rw [hval] at h1
    simpa [mul_assoc] using h1
  have ht := hmul_hasSum.tendsto_sum_nat
  have heq : (fun N : ℕ => ∑ n ∈ Finset.range N,
      ENNReal.ofReal (H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ))) =
      (fun N : ℕ => ENNReal.ofReal (∑ n ∈ Finset.range N,
        H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ))) := by
    ext N
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  rw [heq]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht

private lemma lintegral_finset_sum_aemeas
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ℕ)
    (f : ℕ → α → ℝ≥0∞) (hf : ∀ n : ℕ, AEMeasurable (f n) μ) :
    ∫⁻ x, (∑ n ∈ s, f n x) ∂μ = ∑ n ∈ s, ∫⁻ x, f n x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [MeasureTheory.lintegral_add_left' (hf a), ih]

/-- Landau's Tonelli continuation: if `landauRHS P a b C θ` is holomorphic on `halfPlane σ₁`
(`σ₁ ≤ 1`) and agrees with the Mellin integral of `H ≥ 0` on `halfPlane 1`, then
`H x * x ^ (-σ - 1)` is integrable on `Ioi 1` for every `σ > σ₁`. -/
theorem integrableOn_mellin_of_differentiableOn
    (P : ℂ → ℂ) (a b : ℂ) (H : ℝ → ℝ) (C θ σ₁ : ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (_hσ₁_le1 : σ₁ ≤ 1)
    (hRHS_diffOn : DifferentiableOn ℂ (landauRHS P a b C θ) (halfPlane σ₁))
    (hMellin_gt1 : ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) = landauRHS P a b C θ s) :
    ∀ σ : ℝ, σ₁ < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) := by
  have hH_meas := aestronglyMeasurable_of_mellin_int H hH_int
  intro σ hσ
  by_cases hσ1 : 1 < σ
  · exact hH_int σ hσ1
  · push Not at hσ1
    let r : ℝ := 2 - σ
    have hr_pos : 0 < r := by dsimp [r]; linarith
    let R_val : ℝ := (r + (2 - σ₁)) / 2
    have hR_pos : 0 < R_val := by dsimp [R_val]; linarith
    let R : ℝ≥0 := ⟨R_val, hR_pos.le⟩
    have hR_gt0 : 0 < R := Subtype.mk_lt_mk.mpr hR_pos
    have hball_sub : Metric.closedBall (2 : ℂ) (R : ℝ) ⊆ halfPlane σ₁ := by
      intro z hz
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz
      have hz_le : ‖z - 2‖ ≤ (R : ℝ) := hz
      have habs : |(2 : ℂ).re - z.re| ≤ ‖(2 : ℂ) - z‖ := by
        simpa [sub_re] using Complex.abs_re_le_norm ((2 : ℂ) - z)
      rw [norm_sub_rev] at habs
      have hlow : (2 : ℝ) - (R : ℝ) ≤ z.re := by
        have h2re : (2 : ℂ).re = 2 := by norm_num
        have hdiff := (abs_le.mp (habs.trans hz_le)).2
        rw [h2re] at hdiff
        linarith
      change σ₁ < z.re
      have hR_eq : (R : ℝ) = R_val := rfl
      rw [hR_eq] at hlow
      dsimp [R_val, r] at hlow
      linarith
    have hw_lt : ‖(-(r : ℂ))‖ < (R : ℝ) := by
      rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
      change r < R_val
      dsimp [R_val, r]
      linarith
    have htaylor := taylor_hasSum_of_differentiableOn_closedBall
      (hRHS_diffOn.mono hball_sub) hR_gt0 hw_lt
    have h2r : (2 : ℂ) + (-(r : ℂ)) = (σ : ℂ) := by
      dsimp [r]; push_cast; ring
    rw [h2r] at htaylor
    have hopen1 : IsOpen (halfPlane 1) := isOpen_lt continuous_const Complex.continuous_re
    have h2_mem1 : (2 : ℂ) ∈ halfPlane 1 := by change (1 : ℝ) < (2 : ℂ).re; norm_num
    have hderiv_eq : ∀ n : ℕ,
        iteratedDeriv n (landauRHS P a b C θ) 2 =
          iteratedDeriv n (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)) 2 := by
      intro n
      refine Filter.EventuallyEq.iteratedDeriv_eq (n := n) ?_
      filter_upwards [hopen1.mem_nhds h2_mem1] with z hz
      exact (hMellin_gt1 z hz).symm
    have hterm_re : ∀ n : ℕ,
        ((iteratedDeriv n (landauRHS P a b C θ) 2 / (n.factorial : ℂ) * (-(r : ℂ)) ^ n)).re =
          ∫ x in Ioi (1 : ℝ), H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ) := by
      intro n
      rw [hderiv_eq n, iteratedDeriv_mellin_integral H hH_nonneg hH_int n (by norm_num)]
      have hsign : (-1 : ℂ) ^ n * (-(r : ℂ)) ^ n = ((r ^ n : ℝ) : ℂ) := by
        rw [← mul_pow]
        have : (-1 : ℂ) * (-(r : ℂ)) = (r : ℂ) := by ring
        rw [this, Complex.ofReal_pow]
      have hcomm :
          (-1 : ℂ) ^ n * (∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-(2 : ℂ) - 1)) /
            (n.factorial : ℂ) * (-(r : ℂ)) ^ n =
          (((r ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
            ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-(2 : ℂ) - 1) := by
        calc
          (-1 : ℂ) ^ n * (∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-(2 : ℂ) - 1)) /
              (n.factorial : ℂ) * (-(r : ℂ)) ^ n
              = ((-1 : ℂ) ^ n * (-(r : ℂ)) ^ n / (n.factorial : ℂ)) *
                  ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-(2 : ℂ) - 1) := by ring
          _ = (((r ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
                ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-(2 : ℂ) - 1) := by
                rw [hsign]; push_cast; ring
      rw [hcomm, ← MeasureTheory.integral_const_mul]
      have hint_eq : EqOn
          (fun x : ℝ => (((r ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
            ((H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-(2 : ℂ) - 1)))
          (fun x : ℝ => ((H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ) : ℝ) : ℂ))
          (Ioi (1 : ℝ)) := by
        intro x hx
        dsimp only
        have hx_pos : 0 < x := lt_trans zero_lt_one hx
        have hcpow : (x : ℂ) ^ (-(2 : ℂ) - 1) = ((x ^ (-3 : ℝ) : ℝ) : ℂ) := by
          have hexp : (-(2 : ℂ) - 1) = (((-3 : ℝ)) : ℂ) := by norm_num
          rw [hexp, Complex.ofReal_cpow hx_pos.le]
        rw [hcpow]
        push_cast
        rw [mul_pow]
        ring
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hint_eq]
      exact (congrArg Complex.re
        (integral_ofReal (𝕜 := ℂ)
          (f := fun x : ℝ => H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ)))).trans
        (Complex.ofReal_re _)
    have hre_sum : HasSum
        (fun n : ℕ => ∫ x in Ioi (1 : ℝ), H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ))
        ((landauRHS P a b C θ (σ : ℂ)).re) := by
      have hre := Complex.reCLM.hasSum htaylor
      change HasSum (fun n : ℕ =>
        (iteratedDeriv n (landauRHS P a b C θ) 2 / (n.factorial : ℂ) * (-(r : ℂ)) ^ n).re)
        ((landauRHS P a b C θ (σ : ℂ)).re) at hre
      simp_rw [hterm_re] at hre
      exact hre
    let f : ℕ → ℝ → ℝ≥0∞ := fun n x =>
      ENNReal.ofReal (H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ))
    have hf_aemeas : ∀ n : ℕ, AEMeasurable (f n) (volume.restrict (Ioi (1 : ℝ))) := fun n =>
      (integrableOn_mellin_real_term H hH_nonneg hH_meas hH_int hr_pos.le n).aemeasurable.ennreal_ofReal
    have hpartial_le : ∀ N : ℕ,
        ∫⁻ x in Ioi (1 : ℝ), (∑ n ∈ Finset.range N, f n x) ≤
          ENNReal.ofReal ((landauRHS P a b C θ (σ : ℂ)).re) := by
      intro N
      rw [lintegral_finset_sum_aemeas _ (Finset.range N) f hf_aemeas]
      have hterm_lint : ∀ n : ℕ,
          ∫⁻ x in Ioi (1 : ℝ), f n x =
            ENNReal.ofReal (∫ x in Ioi (1 : ℝ),
              H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ)) := by
        intro n
        have hint_n := integrableOn_mellin_real_term H hH_nonneg hH_meas hH_int hr_pos.le n
        symm
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_n
          (by
            change ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
              0 ≤ H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ)
            rw [ae_restrict_iff' measurableSet_Ioi]
            refine Eventually.of_forall fun x hx => ?_
            have hx_pos : 0 < x := lt_trans zero_lt_one hx
            have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
            have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
            positivity)
      simp_rw [hterm_lint]
      have hsum_nonneg : ∀ n : ℕ,
          0 ≤ ∫ x in Ioi (1 : ℝ),
            H x * ((r * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-3 : ℝ) := by
        intro n
        refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
        have hx_pos : 0 < x := lt_trans zero_lt_one hx
        have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
        have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
        positivity
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hsum_nonneg n)]
      exact ENNReal.ofReal_le_ofReal (sum_le_hasSum (Finset.range N) (fun n _ => hsum_nonneg n) hre_sum)
    let S : ℕ → ℝ → ℝ≥0∞ := fun N x => ∑ n ∈ Finset.range N, f n x
    have hS_aemeas : ∀ N : ℕ, AEMeasurable (S N) (volume.restrict (Ioi (1 : ℝ))) := fun N =>
      Finset.aemeasurable_fun_sum (Finset.range N) (fun n _ => hf_aemeas n)
    have hS_mono : Monotone S := by
      intro m n hmn x
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hmn)
    have hsup_le : ∫⁻ x in Ioi (1 : ℝ), (⨆ N : ℕ, S N x) ≤
        ENNReal.ofReal ((landauRHS P a b C θ (σ : ℂ)).re) := by
      rw [MeasureTheory.lintegral_iSup' hS_aemeas (Eventually.of_forall fun x m n hmn => hS_mono hmn x)]
      exact iSup_le hpartial_le
    have hsup_ae : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
        ENNReal.ofReal (H x * x ^ (-σ - 1)) = ⨆ N : ℕ, S N x := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      have hs := tendsto_ennreal_mellin_partial_sums hx (hH_nonneg x (le_of_lt hx)) hr_pos.le
      have hexp : -(2 - r) - 1 = -σ - 1 := by dsimp [r]; ring
      rw [hexp] at hs
      exact tendsto_nhds_unique hs (tendsto_atTop_iSup (fun m n hmn => hS_mono hmn x))
    have hlint_fin : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (H x * x ^ (-σ - 1)) < ⊤ := by
      rw [lintegral_congr_ae hsup_ae]
      exact lt_of_le_of_lt hsup_le ENNReal.ofReal_lt_top
    have hmeas_target : AEStronglyMeasurable (fun x : ℝ => H x * x ^ (-σ - 1))
        (volume.restrict (Ioi (1 : ℝ))) :=
      hH_meas.mul (Measurable.pow_const measurable_id (-σ - 1)).aemeasurable.aestronglyMeasurable
    have hnonneg_target : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x : ℝ => H x * x ^ (-σ - 1) := by
      change ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), 0 ≤ H x * x ^ (-σ - 1)
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      exact mul_nonneg (hH_nonneg x (le_of_lt hx))
        (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)
    exact ⟨hmeas_target, (hasFiniteIntegral_iff_ofReal hnonneg_target).mpr hlint_fin⟩

/-- Analytic continuation of the Mellin integral `∫ x in Ioi 1, (H x : ℂ) * (x : ℂ) ^ (-s - 1)`
to `halfPlane σ₁` and equality with `landauRHS P a b C θ` via the identity theorem. -/
theorem mellin_eqOn_halfPlane
    (P : ℂ → ℂ) (a b : ℂ) (H : ℝ → ℝ) (C θ σ₁ : ℝ)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (_hσ₁_le1 : σ₁ ≤ 1)
    (hRHS_diffOn : DifferentiableOn ℂ (landauRHS P a b C θ) (halfPlane σ₁))
    (hMellin_gt1 : ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) = landauRHS P a b C θ s) :
    EqOn (fun s : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1))
      (landauRHS P a b C θ) (halfPlane σ₁) := by
  have hH_meas := aestronglyMeasurable_of_mellin_int H hH_int
  have hint_gt_σ₁ := integrableOn_mellin_of_differentiableOn
    P a b H C θ σ₁ hH_nonneg hH_int _hσ₁_le1 hRHS_diffOn hMellin_gt1
  let M : ℂ → ℂ := fun z => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)
  have hM_diffOn : DifferentiableOn ℂ M (halfPlane σ₁) := by
    intro s hs
    change σ₁ < s.re at hs
    let σ₀ : ℝ := (σ₁ + s.re) / 2
    have hσ₀_gt : σ₁ < σ₀ := by dsimp [σ₀]; linarith
    have hσ₀_lt : σ₀ < s.re := by dsimp [σ₀]; linarith
    let δ : ℝ := (s.re - σ₀) / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    let ε : ℝ := (σ₀ - σ₁) / 2
    have hε_pos : 0 < ε := by dsimp [ε]; linarith
    have hσ_dom_gt : σ₁ < σ₀ - ε := by dsimp [ε, σ₀]; linarith
    let C_log : ℝ := max 1 ((1 : ℝ) / ε) ^ 1
    let F : ℂ → ℝ → ℂ := fun z x => (H x : ℂ) * (x : ℂ) ^ (-z - 1)
    let F' : ℂ → ℝ → ℂ := fun z x => (H x : ℂ) * ((x : ℂ) ^ (-z - 1) * Complex.log (x : ℂ) * (-1))
    let bound : ℝ → ℝ := fun x => C_log * (H x * x ^ (-(σ₀ - ε) - 1))
    have hball_re : ∀ z ∈ Metric.ball s δ, σ₀ ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have habs : |z.re - s.re| ≤ ‖z - s‖ := by
        simpa [sub_re] using Complex.abs_re_le_norm (z - s)
      have hlow : s.re - δ ≤ z.re := by linarith [(abs_le.mp (habs.trans hz.le)).1]
      dsimp [δ] at hlow
      linarith
    have hint_k0 : ∀ z : ℂ, σ₀ ≤ z.re →
        IntegrableOn (fun x : ℝ => (H x : ℂ) * (x : ℂ) ^ (-z - 1)) (Ioi 1) := by
      intro z hz
      refine (hint_gt_σ₁ σ₀ hσ₀_gt).mono' ?_ ?_
      · exact (Complex.measurable_ofReal.comp_aemeasurable hH_meas.aemeasurable).aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow_Ioi (-z - 1))
      · rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun x hx => ?_
        have hx_ge1 : 1 ≤ x := le_of_lt hx
        have hx_pos : 0 < x := lt_trans zero_lt_one hx
        have hH0 : 0 ≤ H x := hH_nonneg x hx_ge1
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hH0,
          Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
        have hre : (-z - 1).re ≤ -σ₀ - 1 := by
          rw [sub_re, neg_re, one_re]
          exact sub_le_sub_right (neg_le_neg hz) 1
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx_ge1 hre) hH0
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      (Metric.ball_mem_nhds s hδ_pos)
      ?_ ?_ ?_ ?_ ((hint_gt_σ₁ (σ₀ - ε) hσ_dom_gt).const_mul C_log) ?_
    · exact hd.2.differentiableAt.differentiableWithinAt
    · filter_upwards [Metric.ball_mem_nhds s hδ_pos] with z hz
      exact (hint_k0 z (hball_re z hz)).aestronglyMeasurable
    · exact hint_k0 s hσ₀_lt.le
    · have hlogC : AEStronglyMeasurable (fun x : ℝ => Complex.log (x : ℂ))
          (volume.restrict (Ioi (1 : ℝ))) :=
        (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable
      have hinner : AEStronglyMeasurable
          (fun x : ℝ => (x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * (-1 : ℂ))
          (volume.restrict (Ioi (1 : ℝ))) :=
        ((aestronglyMeasurable_ofReal_cpow_Ioi (-s - 1)).mul hlogC).mul
          aestronglyMeasurable_const
      exact (Complex.measurable_ofReal.comp_aemeasurable hH_meas.aemeasurable).aestronglyMeasurable.mul hinner
    · rw [ae_restrict_iff' measurableSet_Ioi]
      have hCnn : 0 ≤ C_log := by
        dsimp [C_log]; exact pow_nonneg (zero_le_one.trans (le_max_left 1 _)) 1
      refine Eventually.of_forall fun x hx z hz => ?_
      have hlog_pow : |Real.log x| ^ 1 ≤ C_log * x ^ ε := by
        dsimp [C_log]
        simpa using abs_log_pow_le_rpow (k := 1) hε_pos (le_of_lt hx)
      have hnorm := norm_mellin_deriv_le (k := 0) hx (hH_nonneg x (le_of_lt hx)) (hball_re z hz) hCnn hlog_pow
      have hexp : -(σ₀ - ε) - 1 = ε - σ₀ - 1 := by ring
      dsimp only [F', bound]
      rw [hexp]
      simpa [pow_zero, mul_one, mul_assoc] using hnorm
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun x hx z _ =>
        hasDerivAt_mellin_integrand ((H x : ℂ)) hx z
  have hU_open : IsOpen (halfPlane σ₁) := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ (halfPlane σ₁) := by
    intro x hx y hy a b ha hb hab
    change σ₁ < x.re at hx
    change σ₁ < y.re at hy
    change σ₁ < (a • x + b • y).re
    simp only [add_re, real_smul, mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    by_cases ha0 : a = 0
    · subst ha0; simp at hab; subst hab; simpa using hy
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hx' : a * σ₁ < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
      have hy' : b * σ₁ ≤ b * y.re := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
      calc
        σ₁ = (a + b) * σ₁ := by rw [hab, one_mul]
        _ = a * σ₁ + b * σ₁ := add_mul a b σ₁
        _ < a * x.re + b * y.re := add_lt_add_of_lt_of_le hx' hy'
  have h2_mem : (2 : ℂ) ∈ halfPlane σ₁ := by
    change σ₁ < (2 : ℂ).re; norm_num; linarith
  have hopen1 : IsOpen (halfPlane 1) := isOpen_lt continuous_const Complex.continuous_re
  have h2_mem1 : (2 : ℂ) ∈ halfPlane 1 := by change (1 : ℝ) < (2 : ℂ).re; norm_num
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ, M z = landauRHS P a b C θ z := by
    have hev : ∀ᶠ z in nhdsWithin (2 : ℂ) {(2 : ℂ)}ᶜ, z ∈ halfPlane 1 :=
      nhdsWithin_le_nhds (hopen1.mem_nhds h2_mem1)
    exact hev.frequently.mono fun z hz => hMellin_gt1 z hz
  exact (hM_diffOn.analyticOnNhd hU_open).eqOn_of_preconnected_of_frequently_eq
    (hRHS_diffOn.analyticOnNhd hU_open) hU_conv.isPreconnected h2_mem hfreq

private lemma logDeriv_pole_tendsto_nhdsWithin
    {P : ℂ → ℂ} (hP_diff : Differentiable ℂ P) (hP_nzero : ∃ w : ℂ, P w ≠ 0)
    {z₁ : ℂ} (hz₁ : P z₁ = 0) :
    ∃ (m : ℕ) (g : ℂ → ℂ),
      1 ≤ m ∧ AnalyticAt ℂ g z₁ ∧ g z₁ ≠ 0 ∧
      ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ,
        logDeriv P z = (m : ℂ) / (z - z₁) + logDeriv g z := by
  have hP_ana : AnalyticAt ℂ P z₁ := hP_diff.analyticAt z₁
  have hnot_ev0 : ¬ ∀ᶠ z in 𝓝 z₁, P z = 0 := by
    intro hev
    have hev_w : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, P z = 0 := nhdsWithin_le_nhds hev
    have heq : EqOn P (fun _ => 0) univ :=
      (hP_diff.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
        analyticOnNhd_const isPreconnected_univ (mem_univ z₁) hev_w.frequently
    obtain ⟨w, hw⟩ := hP_nzero
    exact hw (heq (mem_univ w))
  obtain ⟨m, g, hg_ana, hg_ne, hfac⟩ :=
    (hP_ana.exists_eventuallyEq_pow_smul_ne_zero_iff).mpr hnot_ev0
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    push Not at hm0
    have hm_eq0 : m = 0 := by omega
    subst hm_eq0
    have h0 := hfac.self_of_nhds
    simp [hz₁] at h0
    exact hg_ne h0.symm
  refine ⟨m, g, hm_pos, hg_ana, hg_ne, ?_⟩
  have hsub_ne : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, z - z₁ ≠ 0 := by
    rw [eventually_nhdsWithin_iff]
    exact Eventually.of_forall fun z hz hsub => hz (sub_eq_zero.mp hsub)
  have hg_ev_ne : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, g z ≠ 0 :=
    nhdsWithin_le_nhds (hg_ana.continuousAt.eventually_ne hg_ne)
  have hg_ev_diff : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, DifferentiableAt ℂ g z :=
    nhdsWithin_le_nhds (hg_ana.eventually_analyticAt.mono fun _ h => h.differentiableAt)
  have hfac_nhds : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, P z = (z - z₁) ^ m * g z := by
    filter_upwards [nhdsWithin_le_nhds hfac] with z hz
    simpa [smul_eq_mul] using hz
  filter_upwards [hsub_ne, hg_ev_ne, hg_ev_diff, hfac_nhds,
    nhdsWithin_le_nhds (Filter.EventuallyEq.deriv hfac)] with z hz_ne hg_z hg_diff_z hPz hderivPz
  have hd_pow : HasDerivAt (fun w : ℂ => (w - z₁) ^ m) ((m : ℂ) * (z - z₁) ^ (m - 1)) z := by
    change HasDerivAt ((fun w : ℂ => w - z₁) ^ m) ((m : ℂ) * (z - z₁) ^ (m - 1)) z
    simpa using ((hasDerivAt_id z).sub_const z₁).pow m
  have hd_prod : HasDerivAt (fun w : ℂ => (w - z₁) ^ m • g w)
      ((m : ℂ) * (z - z₁) ^ (m - 1) * g z + (z - z₁) ^ m * deriv g z) z := by
    have hm1 := hd_pow.mul hg_diff_z.hasDerivAt
    change HasDerivAt (fun w : ℂ => (w - z₁) ^ m * g w) _ z at hm1
    simpa [smul_eq_mul] using hm1
  dsimp [logDeriv]
  rw [hderivPz, hd_prod.deriv, hPz]
  have hm_split : (z - z₁) ^ m = (z - z₁) * (z - z₁) ^ (m - 1) := by
    cases m with
    | zero => omega
    | succ k => simp [pow_succ']
  rw [hm_split]
  field_simp [hz_ne, pow_ne_zero (m - 1) hz_ne, hg_z]

private lemma not_cleared_denom_eq_at_zero
    {M P : ℂ → ℂ} {a b : ℂ} {C θ : ℝ} {z₁ : ℂ}
    (hM_diff : DifferentiableAt ℂ M z₁) (hP_diff : Differentiable ℂ P)
    (hP_nzero : ∃ w : ℂ, P w ≠ 0) (hz₁ : P z₁ = 0) (hz₁_θ : z₁ - (θ : ℂ) ≠ 0)
    (heq : ∀ᶠ z in 𝓝 z₁,
      M z * P z * (z * (z - 1)) * (z - (θ : ℂ)) =
        (deriv P z - (a + b * z) * P z) * (z - (θ : ℂ)) + (C : ℂ) * P z * (z * (z - 1))) :
    False := by
  have hP_ana : AnalyticAt ℂ P z₁ := hP_diff.analyticAt z₁
  have hnot_ev0 : ¬ ∀ᶠ z in 𝓝 z₁, P z = 0 := by
    intro hev
    have hev_w : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, P z = 0 := nhdsWithin_le_nhds hev
    have heq0 : EqOn P (fun _ => 0) univ :=
      (hP_diff.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
        analyticOnNhd_const isPreconnected_univ (mem_univ z₁) hev_w.frequently
    obtain ⟨w, hw⟩ := hP_nzero
    exact hw (heq0 (mem_univ w))
  obtain ⟨m, g, hg_ana, hg_ne, hfac⟩ :=
    (hP_ana.exists_eventuallyEq_pow_smul_ne_zero_iff).mpr hnot_ev0
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    push Not at hm0
    have hm_eq0 : m = 0 := by omega
    subst hm_eq0
    have h0 := hfac.self_of_nhds
    simp [hz₁] at h0
    exact hg_ne h0.symm
  have hlim_lhs : Tendsto
      (fun z : ℂ => M z * (z - z₁) * g z * (z * (z - 1)) * (z - (θ : ℂ)))
      (nhdsWithin z₁ {z₁}ᶜ)
      (𝓝 (0 : ℂ)) := by
    have ht0 : Tendsto
        (fun z : ℂ => M z * (z - z₁) * g z * (z * (z - 1)) * (z - (θ : ℂ)))
        (𝓝 z₁)
        (𝓝 (M z₁ * (z₁ - z₁) * g z₁ * (z₁ * (z₁ - 1)) * (z₁ - (θ : ℂ)))) :=
      ((((hM_diff.continuousAt.tendsto.mul
        ((continuous_id.sub continuous_const).continuousAt.tendsto)).mul
        hg_ana.continuousAt.tendsto).mul
        ((continuous_id.mul (continuous_id.sub continuous_const)).continuousAt.tendsto)).mul
        ((continuous_id.sub continuous_const).continuousAt.tendsto))
    simp only [sub_self, mul_zero, zero_mul] at ht0
    exact ht0.mono_left nhdsWithin_le_nhds
  have hg_deriv_cont : ContinuousAt (deriv g) z₁ := hg_ana.deriv.continuousAt
  have hlim_rhs : Tendsto
      (fun z : ℂ =>
        (((m : ℂ) * g z + (z - z₁) * deriv g z) - (a + b * z) * ((z - z₁) * g z)) * (z - (θ : ℂ)) +
          (C : ℂ) * ((z - z₁) * g z) * (z * (z - 1)))
      (nhdsWithin z₁ {z₁}ᶜ)
      (𝓝 (((m : ℂ) * g z₁) * (z₁ - (θ : ℂ)))) := by
    have ht1 : Tendsto
        (fun z : ℂ =>
          (((m : ℂ) * g z + (z - z₁) * deriv g z) - (a + b * z) * ((z - z₁) * g z)) * (z - (θ : ℂ)) +
            (C : ℂ) * ((z - z₁) * g z) * (z * (z - 1)))
        (𝓝 z₁)
        (𝓝 ((((m : ℂ) * g z₁ + (z₁ - z₁) * deriv g z₁) -
            (a + b * z₁) * ((z₁ - z₁) * g z₁)) * (z₁ - (θ : ℂ)) +
          (C : ℂ) * ((z₁ - z₁) * g z₁) * (z₁ * (z₁ - 1)))) :=
      (((((tendsto_const_nhds.mul hg_ana.continuousAt.tendsto).add
        ((continuous_id.sub continuous_const).continuousAt.tendsto.mul hg_deriv_cont.tendsto)).sub
        (((continuous_const.add (continuous_const.mul continuous_id)).continuousAt.tendsto).mul
          ((continuous_id.sub continuous_const).continuousAt.tendsto.mul hg_ana.continuousAt.tendsto))).mul
        ((continuous_id.sub continuous_const).continuousAt.tendsto)).add
        ((tendsto_const_nhds.mul
          ((continuous_id.sub continuous_const).continuousAt.tendsto.mul hg_ana.continuousAt.tendsto)).mul
          ((continuous_id.mul (continuous_id.sub continuous_const)).continuousAt.tendsto)))
    simp only [sub_self, zero_mul, mul_zero, sub_zero, add_zero] at ht1
    exact ht1.mono_left (nhdsWithin_le_nhds (s := {z₁}ᶜ))
  have hev_eq_div : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ,
      M z * (z - z₁) * g z * (z * (z - 1)) * (z - (θ : ℂ)) =
        (((m : ℂ) * g z + (z - z₁) * deriv g z) - (a + b * z) * ((z - z₁) * g z)) * (z - (θ : ℂ)) +
          (C : ℂ) * ((z - z₁) * g z) * (z * (z - 1)) := by
    have hsub_ne : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, z - z₁ ≠ 0 := by
      rw [eventually_nhdsWithin_iff]
      exact Eventually.of_forall fun z hz hsub => hz (sub_eq_zero.mp hsub)
    have hg_ev_diff : ∀ᶠ z in nhdsWithin z₁ {z₁}ᶜ, DifferentiableAt ℂ g z :=
      nhdsWithin_le_nhds (hg_ana.eventually_analyticAt.mono fun _ h => h.differentiableAt)
    filter_upwards [hsub_ne, hg_ev_diff, nhdsWithin_le_nhds heq,
      nhdsWithin_le_nhds hfac, nhdsWithin_le_nhds (Filter.EventuallyEq.deriv hfac)] with
      z hz_ne hg_diff_z hId hPz hderivPz
    have hd_pow : HasDerivAt (fun w : ℂ => (w - z₁) ^ m) ((m : ℂ) * (z - z₁) ^ (m - 1)) z := by
      change HasDerivAt ((fun w : ℂ => w - z₁) ^ m) ((m : ℂ) * (z - z₁) ^ (m - 1)) z
      simpa using ((hasDerivAt_id z).sub_const z₁).pow m
    have hd_prod : HasDerivAt (fun w : ℂ => (w - z₁) ^ m • g w)
        ((m : ℂ) * (z - z₁) ^ (m - 1) * g z + (z - z₁) ^ m * deriv g z) z := by
      have hm1 := hd_pow.mul hg_diff_z.hasDerivAt
      change HasDerivAt (fun w : ℂ => (w - z₁) ^ m * g w) _ z at hm1
      simpa [smul_eq_mul] using hm1
    have hPz' : P z = (z - z₁) ^ m * g z := by simpa [smul_eq_mul] using hPz
    have hderivPz' : deriv P z = (m : ℂ) * (z - z₁) ^ (m - 1) * g z + (z - z₁) ^ m * deriv g z := by
      rw [hderivPz, hd_prod.deriv]
    have hm_split : (z - z₁) ^ m = (z - z₁) * (z - z₁) ^ (m - 1) := by
      cases m with
      | zero => omega
      | succ k => simp [pow_succ']
    rw [hPz', hderivPz', hm_split] at hId
    have hpow_ne : (z - z₁) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hz_ne
    apply mul_left_cancel₀ hpow_ne
    calc
      (z - z₁) ^ (m - 1) * (M z * (z - z₁) * g z * (z * (z - 1)) * (z - (θ : ℂ)))
          = M z * ((z - z₁) * (z - z₁) ^ (m - 1) * g z) * (z * (z - 1)) * (z - (θ : ℂ)) := by ring
      _ = ((m : ℂ) * (z - z₁) ^ (m - 1) * g z + (z - z₁) * (z - z₁) ^ (m - 1) * deriv g z -
            (a + b * z) * ((z - z₁) * (z - z₁) ^ (m - 1) * g z)) * (z - (θ : ℂ)) +
          (C : ℂ) * ((z - z₁) * (z - z₁) ^ (m - 1) * g z) * (z * (z - 1)) := hId
      _ = (z - z₁) ^ (m - 1) *
            ((((m : ℂ) * g z + (z - z₁) * deriv g z) - (a + b * z) * ((z - z₁) * g z)) * (z - (θ : ℂ)) +
              (C : ℂ) * ((z - z₁) * g z) * (z * (z - 1))) := by ring
  have hlim_rhs' := hlim_rhs.congr' (hev_eq_div.mono fun _ h => h.symm)
  have hzero_prod : (0 : ℂ) = ((m : ℂ) * g z₁) * (z₁ - (θ : ℂ)) :=
    tendsto_nhds_unique hlim_lhs hlim_rhs'
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero hm_ne hg_ne) hz₁_θ hzero_prod.symm

private lemma differentiableOn_landauRHS_of_open
    (P : ℂ → ℂ) (a b : ℂ) (C θ : ℝ) (U : Set ℂ)
    (hU_open : IsOpen U)
    (hP_diff : Differentiable ℂ P)
    (hP_nz : ∀ s ∈ U, P s ≠ 0)
    (hP_one : deriv P 1 - (a + b) * P 1 = 0)
    (hθ_lt : ∀ s ∈ U, θ < s.re)
    (hθ0 : 0 < θ) :
    DifferentiableOn ℂ (landauRHS P a b C θ) U := by
  have hderivP : Differentiable ℂ (deriv P) :=
    fun s => (hP_diff.analyticAt s).deriv.differentiableAt
  have hL_diffOn : DifferentiableOn ℂ (logDeriv P) U :=
    fun s hs => (hderivP s).differentiableWithinAt.div (hP_diff s).differentiableWithinAt (hP_nz s hs)
  have hPole_diffOn : DifferentiableOn ℂ (fun s : ℂ => (C : ℂ) / (s - (θ : ℂ))) U := by
    intro s hs
    refine ((differentiable_const (C : ℂ)) s).differentiableWithinAt.div
      ((differentiable_id.sub (differentiable_const (θ : ℂ))) s).differentiableWithinAt ?_
    intro hsub
    rw [sub_eq_zero] at hsub
    have hre : s.re = θ := by rw [hsub, Complex.ofReal_re]
    linarith [hθ_lt s hs]
  have haff_diff : Differentiable ℂ (fun s : ℂ => a + b * s) :=
    (differentiable_const a).add ((differentiable_const b).mul differentiable_id)
  have hquad_diff : Differentiable ℂ (fun s : ℂ => s * (s - 1)) :=
    differentiable_id.mul (differentiable_id.sub (differentiable_const 1))
  have hU_ne0 : ∀ s ∈ U, s ≠ 0 := by
    intro s hs h0
    have hgt := hθ_lt s hs
    rw [h0, zero_re] at hgt
    linarith
  by_cases h1U : (1 : ℂ) ∈ U
  · have hL1 : logDeriv P 1 = a + b := by
      dsimp [logDeriv]
      rw [div_eq_iff (hP_nz 1 h1U)]
      exact sub_eq_zero.mp hP_one
    let num : ℂ → ℂ := fun s => logDeriv P s - (a + b * s)
    have hnum_diffOn : DifferentiableOn ℂ num U := hL_diffOn.sub haff_diff.differentiableOn
    have hnum1 : num 1 = 0 := by dsimp [num]; rw [hL1]; ring
    have hderiv_num1 : deriv num 1 = deriv (logDeriv P) 1 - b := by
      have hd1 : HasDerivAt (logDeriv P) (deriv (logDeriv P) 1) 1 :=
        (hL_diffOn.differentiableAt (hU_open.mem_nhds h1U)).hasDerivAt
      have hd2 : HasDerivAt (fun s => a + b * s) b 1 := by
        simpa using ((hasDerivAt_id (1 : ℂ)).const_mul b).const_add a
      exact (hd1.sub hd2).deriv
    have hdslope_diffOn : DifferentiableOn ℂ (dslope num 1) U :=
      (Complex.differentiableOn_dslope (hU_open.mem_nhds h1U)).mpr hnum_diffOn
    have hg_ext_diffOn : DifferentiableOn ℂ (fun s => dslope num 1 s / s) U :=
      fun s hs => (hdslope_diffOn s hs).div
        (differentiable_id s).differentiableWithinAt (hU_ne0 s hs)
    have heq_U : EqOn (landauRHS P a b C θ)
        (fun s => dslope num 1 s / s + (C : ℂ) / (s - (θ : ℂ))) U := by
      intro s hs
      by_cases hs1 : s = 1
      · subst hs1
        dsimp [landauRHS]
        rw [Function.update_self, dslope_same, hderiv_num1, div_one]
      · have hs0 : s ≠ 0 := hU_ne0 s hs
        have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
        rw [landauRHS_eq_of_ne_one P a b C θ hs1]
        dsimp only
        rw [dslope_of_ne num hs1, slope_def_field, hnum1, sub_zero]
        congr 1
        dsimp [num]
        field_simp [hs0, hs1']
    exact DifferentiableOn.congr (hg_ext_diffOn.add hPole_diffOn) heq_U
  · have heq : EqOn (landauRHS P a b C θ)
        (fun z => (logDeriv P z - (a + b * z)) / (z * (z - 1)) + (C : ℂ) / (z - (θ : ℂ))) U :=
      fun z hz => landauRHS_eq_of_ne_one P a b C θ (fun h1 => h1U (h1 ▸ hz))
    have hmain : DifferentiableOn ℂ
        (fun z => (logDeriv P z - (a + b * z)) / (z * (z - 1)) + (C : ℂ) / (z - (θ : ℂ))) U := by
      intro s hs
      have hs1 : s ≠ 1 := fun h1 => h1U (h1 ▸ hs)
      refine (((hL_diffOn s hs).sub (haff_diff s).differentiableWithinAt).div
        (hquad_diff s).differentiableWithinAt
        (mul_ne_zero (hU_ne0 s hs) (sub_ne_zero.mpr hs1))).add (hPole_diffOn s hs)
    exact DifferentiableOn.congr hmain heq

/-- **Theorem 3.2 (Landau Positivity for Entire Functions)**:
If `P : ℂ → ℂ` is entire, non-vanishing on `Re(s) ≥ 1`, satisfies `P'(1) = (a + b) P(1)`,
and `∫_1^∞ H(x) x^{-s-1} dx = landauRHS P a b C θ s` on `Re(s) > 1` with `H(x) ≥ 0` and
`0 < θ < 1`, then `P(s) ≠ 0` for all `Re(s) > θ`. -/
theorem thm_3_2_landau_positivity
    (P : ℂ → ℂ) (a b : ℂ) (H : ℝ → ℝ) (C θ : ℝ)
    (hP_diff : Differentiable ℂ P)
    (hP_ge1 : ∀ s : ℂ, 1 ≤ s.re → P s ≠ 0)
    (hP_one : deriv P 1 - (a + b) * P 1 = 0)
    (hH_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x)
    (hH_int : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1))
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMellin_gt1 : ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) =
        (deriv P s / P s - (a + b * s)) / (s * (s - 1)) + (C : ℂ) / (s - (θ : ℂ))) :
    ∀ s : ℂ, θ < s.re → P s ≠ 0 := by
  have hRHS_gt1 : ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1) = landauRHS P a b C θ s := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h1; rw [h1, one_re] at hs; exact lt_irrefl 1 hs
    rw [landauRHS_eq_of_ne_one P a b C θ hs1]
    exact hMellin_gt1 s hs
  by_contra hvan
  push Not at hvan
  obtain ⟨z₀, hz₀_gt, hPz₀⟩ := hvan
  let S_re : Set ℝ := {r : ℝ | ∃ z : ℂ, P z = 0 ∧ z.re = r}
  have hS_ne : S_re.Nonempty := ⟨z₀.re, z₀, hPz₀, rfl⟩
  have hS_bdd : BddAbove S_re := by
    refine ⟨1, ?_⟩
    rintro r ⟨z, hPz, rfl⟩
    by_contra hgt
    push Not at hgt
    exact hP_ge1 z hgt.le hPz
  let σ₀ : ℝ := sSup S_re
  have hσ₀_gt_θ : θ < σ₀ := lt_of_lt_of_le hz₀_gt (le_csSup hS_bdd ⟨z₀, hPz₀, rfl⟩)
  have hσ₀_le_1 : σ₀ ≤ 1 := csSup_le hS_ne (by
    rintro r ⟨z, hPz, rfl⟩
    by_contra hgt
    push Not at hgt
    exact hP_ge1 z hgt.le hPz)
  have hP_gt_σ₀ : ∀ z : ℂ, σ₀ < z.re → P z ≠ 0 := by
    intro z hz hPz
    exact not_lt_of_ge (le_csSup hS_bdd ⟨z, hPz, rfl⟩) hz
  have hRHS_diff_σ₀ : DifferentiableOn ℂ (landauRHS P a b C θ) (halfPlane σ₀) :=
    differentiableOn_landauRHS P a b C θ σ₀ hP_diff hP_gt_σ₀ hP_one hθ0 hσ₀_gt_θ.le
  have hMellin_σ₀ := mellin_eqOn_halfPlane P a b H C θ σ₀ hH_nonneg hH_int hσ₀_le_1 hRHS_diff_σ₀ hRHS_gt1
  have hP_nzero : ∃ w : ℂ, P w ≠ 0 := ⟨1, hP_ge1 1 (by norm_num)⟩
  -- Step 1: Rule out a real zero at `s = σ₀`
  have hP_σ₀_ne : P (σ₀ : ℂ) ≠ 0 := by
    intro hPσ₀
    obtain ⟨m, g, hm_pos, hg_ana, hg_ne, hpole⟩ :=
      logDeriv_pole_tendsto_nhdsWithin hP_diff hP_nzero hPσ₀
    have hσ₀_pos : 0 < σ₀ := lt_trans hθ0 hσ₀_gt_θ
    have hσ₀_lt1 : σ₀ < 1 := lt_of_le_of_ne hσ₀_le_1
      (fun h1 => hP_ge1 1 (by norm_num) (by simpa [h1] using hPσ₀))
    have hnonneg_M : ∀ t : ℝ, 0 < t → 0 ≤ (landauRHS P a b C θ ((σ₀ + t : ℝ) : ℂ)).re := by
      intro t ht
      have hmem : (((σ₀ + t : ℝ) : ℂ)) ∈ halfPlane σ₀ := by
        change σ₀ < (((σ₀ + t : ℝ) : ℂ)).re
        rw [Complex.ofReal_re]
        linarith
      have h1 := hMellin_σ₀ hmem
      dsimp only at h1
      rw [← h1, integral_mellin_real_eq H, Complex.ofReal_re]
      refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
      exact mul_nonneg (hH_nonneg x (le_of_lt hx))
        (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)
    have hcont_g : ContinuousAt (logDeriv g) (σ₀ : ℂ) :=
      hg_ana.deriv.continuousAt.div hg_ana.continuousAt hg_ne
    obtain ⟨δ₁, hδ₁_pos, hδ₁_ball⟩ := Metric.mem_nhds_iff.mp
      (hcont_g.norm.eventually_lt continuousAt_const (lt_add_one ‖logDeriv g (σ₀ : ℂ)‖))
    obtain ⟨δ₂, hδ₂_pos, hδ₂_pole⟩ := Metric.mem_nhdsWithin_iff.mp hpole
    let M_g : ℝ := ‖logDeriv g (σ₀ : ℂ)‖ + 1
    let M_aff : ℝ := ‖a‖ + ‖b‖ * 2
    let M_pole : ℝ := |C| / (σ₀ - θ)
    let K : ℝ := M_g + M_aff + M_pole + 1
    let t : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) (min ((1 - σ₀) / 2) ((m : ℝ) / (2 * K)))
    have hK_pos : 0 < K := by
      have : 0 ≤ M_g := add_nonneg (norm_nonneg _) zero_le_one
      have : 0 ≤ M_aff := by dsimp [M_aff]; positivity
      have : 0 ≤ M_pole := div_nonneg (abs_nonneg C) (sub_nonneg.mpr hσ₀_gt_θ.le)
      dsimp [K]; linarith
    have hm_real_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have ht_pos : 0 < t := by
      dsimp [t]
      refine lt_min (lt_min (half_pos hδ₁_pos) (half_pos hδ₂_pos))
        (lt_min (half_pos (sub_pos.mpr hσ₀_lt1)) (div_pos hm_real_pos (by linarith)))
    let zt : ℂ := ((σ₀ + t : ℝ) : ℂ)
    have hdist_zt : dist zt (σ₀ : ℂ) = t := by
      have : zt - (σ₀ : ℂ) = (t : ℂ) := by dsimp [zt]; push_cast; ring
      rw [Complex.dist_eq, this, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
    have hzt_ne : zt ≠ (σ₀ : ℂ) := by
      intro h; rw [h, dist_self] at hdist_zt; linarith
    have hzt_mem1 : zt ∈ Metric.ball (σ₀ : ℂ) δ₁ := by
      rw [Metric.mem_ball, hdist_zt]
      exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hδ₁_pos)
    have hzt_mem2 : zt ∈ Metric.ball (σ₀ : ℂ) δ₂ := by
      rw [Metric.mem_ball, hdist_zt]
      exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hδ₂_pos)
    have ht_le_half : t ≤ (1 - σ₀) / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have ht_le_K : t ≤ (m : ℝ) / (2 * K) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hzt_ne1 : zt ≠ 1 := by
      intro h1
      have hre := congrArg Complex.re h1
      dsimp [zt] at hre
      linarith
    have hpole_zt : logDeriv P zt = (m : ℂ) / (t : ℂ) + logDeriv g zt := by
      have hsub : zt - (σ₀ : ℂ) = (t : ℂ) := by dsimp [zt]; push_cast; ring
      have h := hδ₂_pole ⟨hzt_mem2, hzt_ne⟩
      change logDeriv P zt = (m : ℂ) / (zt - (σ₀ : ℂ)) + logDeriv g zt at h
      rwa [hsub] at h
    have hquad_neg : (σ₀ + t) * (σ₀ + t - 1) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have hquad_gt_neg1 : -1 < (σ₀ + t) * (σ₀ + t - 1) := by
      nlinarith
    have hg_bound : |(logDeriv g zt).re| ≤ M_g :=
      (Complex.abs_re_le_norm _).trans (hδ₁_ball hzt_mem1).le
    have haff_bound : |(a + b * zt).re| ≤ M_aff := by
      refine (Complex.abs_re_le_norm _).trans ?_
      have hnorm_zt : ‖zt‖ ≤ 2 := by
        dsimp [zt]
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
      calc
        ‖a + b * zt‖ ≤ ‖a‖ + ‖b * zt‖ := norm_add_le _ _
        _ = ‖a‖ + ‖b‖ * ‖zt‖ := by rw [norm_mul]
        _ ≤ ‖a‖ + ‖b‖ * 2 := by gcongr
    have hpoleC_bound : |((C : ℂ) / (zt - (θ : ℂ))).re| ≤ M_pole := by
      have hdiv_real : (C : ℂ) / (zt - (θ : ℂ)) = ((C / (σ₀ + t - θ) : ℝ) : ℂ) := by
        dsimp [zt]; push_cast; ring
      have hden_pos : 0 < σ₀ - θ := sub_pos.mpr hσ₀_gt_θ
      have hden_le : σ₀ - θ ≤ σ₀ + t - θ := by linarith
      rw [hdiv_real, Complex.ofReal_re, abs_div, abs_of_pos (lt_of_lt_of_le hden_pos hden_le)]
      exact div_le_div_of_nonneg_left (abs_nonneg C) hden_pos hden_le
    have hnum_re : (logDeriv P zt - (a + b * zt)).re ≥ (m : ℝ) / t - (M_g + M_aff) := by
      rw [hpole_zt, sub_re, add_re]
      have hm_div : ((m : ℂ) / (t : ℂ)).re = (m : ℝ) / t := by
        have : (m : ℂ) / (t : ℂ) = (((m : ℝ) / t : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [hm_div]
      linarith [(abs_le.mp hg_bound).1, (abs_le.mp haff_bound).2]
    have hnum_gt_K : K < (logDeriv P zt - (a + b * zt)).re := by
      have hdiv_ge : 2 * K ≤ (m : ℝ) / t := by
        rw [le_div_iff₀ ht_pos]
        have := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * K)).mp ht_le_K
        linarith
      have hK_def : K = M_g + M_aff + M_pole + 1 := rfl
      have hMpole_nn : 0 ≤ M_pole := div_nonneg (abs_nonneg C) (sub_nonneg.mpr hσ₀_gt_θ.le)
      linarith
    have hrhs_re : (landauRHS P a b C θ zt).re =
        (logDeriv P zt - (a + b * zt)).re / ((σ₀ + t) * (σ₀ + t - 1)) +
          ((C : ℂ) / (zt - (θ : ℂ))).re := by
      rw [landauRHS_eq_of_ne_one P a b C θ hzt_ne1, add_re]
      congr 1
      have hden : zt * (zt - 1) = (((σ₀ + t) * (σ₀ + t - 1) : ℝ) : ℂ) := by
        dsimp [zt]; push_cast; ring
      have hdiv_r : ∀ (w : ℂ) (x : ℝ), (w / (x : ℂ)).re = w.re / x := by
        intro w x
        rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hden, hdiv_r]
    have hfirst_lt : (logDeriv P zt - (a + b * zt)).re / ((σ₀ + t) * (σ₀ + t - 1)) < -K := by
      rw [div_lt_iff_of_neg hquad_neg]
      nlinarith
    have hneg_rhs : (landauRHS P a b C θ zt).re < 0 := by
      rw [hrhs_re]
      have hnum_re_parts : (logDeriv P zt - (a + b * zt)).re =
          (logDeriv P zt).re - (a.re + (b * zt).re) := by
        simp [sub_re, add_re]
      rw [hnum_re_parts]
      have hfirst_lt' := hfirst_lt
      dsimp [K] at hfirst_lt'
      have hMg_nn : 0 ≤ M_g := add_nonneg (norm_nonneg _) zero_le_one
      have hMaff_nn : 0 ≤ M_aff := by dsimp [M_aff]; positivity
      have hpoleC_upper : ((C : ℂ) / (zt - (θ : ℂ))).re ≤ M_pole :=
        (abs_le.mp hpoleC_bound).2
      have hsum_lt :
          ((logDeriv P zt).re - (a.re + (b * zt).re)) /
                ((σ₀ + t) * (σ₀ + t - 1)) + ((C : ℂ) / (zt - (θ : ℂ))).re <
              -(M_g + M_aff + M_pole + 1) + M_pole :=
        add_lt_add_of_lt_of_le hfirst_lt' hpoleC_upper
      have hsum_le : -(M_g + M_aff + M_pole + 1) + M_pole ≤ 0 := by
        calc
          -(M_g + M_aff + M_pole + 1) + M_pole = -(M_g + M_aff + 1) := by ring
          _ ≤ 0 := by linarith
      exact lt_of_lt_of_le hsum_lt hsum_le
    exact not_lt_of_ge (hnonneg_M t ht_pos) hneg_rhs
  -- Step 2: Obtain a zero `z₁` near `σ₀` and continue `M` across `σ₀ - r₀ / 2`
  obtain ⟨r₁, hr₁_pos, hr₁_ball⟩ := Metric.mem_nhds_iff.mp
    (hP_diff.continuous.continuousAt.eventually_ne hP_σ₀_ne)
  let r₀ : ℝ := min (r₁ / 8) ((σ₀ - θ) / 4)
  have hr₀_pos : 0 < r₀ := lt_min (by linarith) (by linarith)
  obtain ⟨r_z, ⟨z₁, hPz₁, rfl⟩, hz₁_gt⟩ := (lt_csSup_iff hS_bdd hS_ne).mp
    (show σ₀ - r₀ / 2 < σ₀ by linarith)
  let c₀ : ℂ := ((σ₀ + r₀ : ℝ) : ℂ)
  have hc₀_gt_σ₀ : σ₀ < c₀.re := by dsimp [c₀]; linarith
  have hP_udisk_ne : ∀ z ∈ Metric.ball c₀ ((2 : ℝ) * r₀), P z ≠ 0 := by
    intro z hz
    by_cases hre : σ₀ < z.re
    · exact hP_gt_σ₀ z hre
    · push Not at hre
      apply hr₁_ball
      rw [Metric.mem_ball, Complex.dist_eq] at hz ⊢
      have hre_diff : |(z - (σ₀ : ℂ)).re| ≤ (2 : ℝ) * r₀ := by
        have h1 : |z.re - (σ₀ + r₀)| ≤ ‖z - c₀‖ := by
          simpa [c₀, sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm (z - c₀)
        rw [sub_re, Complex.ofReal_re, abs_of_nonpos (sub_nonpos.mpr hre)]
        have := (abs_le.mp (h1.trans hz.le)).1
        linarith
      have him_diff : |(z - (σ₀ : ℂ)).im| ≤ (2 : ℝ) * r₀ := by
        have h1 : |z.im - 0| ≤ ‖z - c₀‖ := by
          simpa [c₀, sub_im, Complex.ofReal_im] using Complex.abs_im_le_norm (z - c₀)
        simpa [sub_im, Complex.ofReal_im] using h1.trans hz.le
      have hnorm_le : ‖z - (σ₀ : ℂ)‖ ≤ |(z - (σ₀ : ℂ)).re| + |(z - (σ₀ : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      have hr₀_le1 : r₀ ≤ r₁ / 8 := min_le_left _ _
      linarith
  have hθ_udisk : ∀ z ∈ Metric.ball c₀ ((2 : ℝ) * r₀), θ < z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |z.re - (σ₀ + r₀)| ≤ ‖z - c₀‖ := by
      simpa [c₀, sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm (z - c₀)
    have hlow := (abs_le.mp (h1.trans hz.le)).1
    have hr₀_le2 : r₀ ≤ (σ₀ - θ) / 4 := min_le_right _ _
    linarith
  have hRHS_diff_ball : DifferentiableOn ℂ (landauRHS P a b C θ)
      (Metric.closedBall c₀ ((7 / 4 : ℝ) * r₀)) :=
    (differentiableOn_landauRHS_of_open P a b C θ (Metric.ball c₀ ((2 : ℝ) * r₀))
      Metric.isOpen_ball hP_diff hP_udisk_ne hP_one hθ_udisk hθ0).mono
      (Metric.closedBall_subset_ball (by linarith))
  let r_step : ℝ := (3 / 2 : ℝ) * r₀
  have hr_step_pos : 0 < r_step := by dsimp [r_step]; linarith
  let R_c : ℝ≥0 := ⟨(7 / 4 : ℝ) * r₀, by positivity⟩
  have hR_c_pos : 0 < R_c := Subtype.mk_lt_mk.mpr (by positivity)
  have hw_c_lt : ‖(-(r_step : ℂ))‖ < (R_c : ℝ) := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hr_step_pos.le]
    change r_step < (7 / 4 : ℝ) * r₀
    dsimp [r_step]; linarith
  have htaylor_c := taylor_hasSum_of_differentiableOn_closedBall
    hRHS_diff_ball hR_c_pos hw_c_lt
  let σ_reach : ℝ := σ₀ - r₀ / 2
  have hc_plus_w : c₀ + (-(r_step : ℂ)) = (σ_reach : ℂ) := by
    dsimp [c₀, r_step, σ_reach]; push_cast; ring
  rw [hc_plus_w] at htaylor_c
  have hH_meas := aestronglyMeasurable_of_mellin_int H hH_int
  have hint_c₀ : ∀ σ' : ℝ, σ₀ < σ' → IntegrableOn (fun x : ℝ => H x * x ^ (-σ' - 1)) (Ioi 1) :=
    integrableOn_mellin_of_differentiableOn P a b H C θ σ₀ hH_nonneg hH_int hσ₀_le_1 hRHS_diff_σ₀ hRHS_gt1
  have hopen_σ₀ : IsOpen (halfPlane σ₀) := isOpen_lt continuous_const Complex.continuous_re
  have hderiv_c_eq : ∀ n : ℕ,
      iteratedDeriv n (landauRHS P a b C θ) c₀ =
        iteratedDeriv n (fun z : ℂ => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)) c₀ := by
    intro n
    refine Filter.EventuallyEq.iteratedDeriv_eq (n := n) ?_
    filter_upwards [hopen_σ₀.mem_nhds hc₀_gt_σ₀] with z hz
    exact (hMellin_σ₀ hz).symm
  have hterm_c_re : ∀ n : ℕ,
      ((iteratedDeriv n (landauRHS P a b C θ) c₀ / (n.factorial : ℂ) * (-(r_step : ℂ)) ^ n)).re =
        ∫ x in Ioi (1 : ℝ), H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1) := by
    intro n
    rw [hderiv_c_eq n, iteratedDeriv_mellin_integral_of_gt H hH_nonneg hH_meas hint_c₀ n
      (by show σ₀ < c₀.re; dsimp [c₀]; linarith)]
    have hsign : (-1 : ℂ) ^ n * (-(r_step : ℂ)) ^ n = ((r_step ^ n : ℝ) : ℂ) := by
      rw [← mul_pow]
      have : (-1 : ℂ) * (-(r_step : ℂ)) = (r_step : ℂ) := by ring
      rw [this, Complex.ofReal_pow]
    have hcomm :
        (-1 : ℂ) ^ n * (∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-c₀ - 1)) /
          (n.factorial : ℂ) * (-(r_step : ℂ)) ^ n =
        (((r_step ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
          ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-c₀ - 1) := by
      calc
        (-1 : ℂ) ^ n * (∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-c₀ - 1)) /
            (n.factorial : ℂ) * (-(r_step : ℂ)) ^ n
            = ((-1 : ℂ) ^ n * (-(r_step : ℂ)) ^ n / (n.factorial : ℂ)) *
                ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-c₀ - 1) := by ring
        _ = (((r_step ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
              ∫ x in Ioi (1 : ℝ), (H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-c₀ - 1) := by
              rw [hsign]; push_cast; ring
    rw [hcomm, ← MeasureTheory.integral_const_mul]
    have hint_eq : EqOn
        (fun x : ℝ => (((r_step ^ n / (n.factorial : ℝ) : ℝ) : ℂ)) *
          ((H x : ℂ) * ((Real.log x : ℂ) ^ n) * (x : ℂ) ^ (-c₀ - 1)))
        (fun x : ℝ => ((H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1) : ℝ) : ℂ))
        (Ioi (1 : ℝ)) := by
      intro x hx
      dsimp only
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hcpow : (x : ℂ) ^ (-c₀ - 1) = ((x ^ (-(σ₀ + r₀) - 1) : ℝ) : ℂ) := by
        have hexp : (-c₀ - 1) = (((-(σ₀ + r₀) - 1 : ℝ)) : ℂ) := by dsimp [c₀]; push_cast; ring
        rw [hexp, Complex.ofReal_cpow hx_pos.le]
      rw [hcpow]
      push_cast
      rw [mul_pow]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hint_eq]
    have hre_int :
        (∫ x in Ioi (1 : ℝ),
          ((H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1) : ℝ) : ℂ)).re =
        ∫ x in Ioi (1 : ℝ),
          (((H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1) : ℝ) : ℂ)).re := by
      exact (congrArg Complex.re
        (integral_ofReal (𝕜 := ℂ)
          (f := fun x : ℝ => (H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) *
              (x : ℝ) ^ (-(σ₀ + r₀) - 1) : ℝ)))).trans (Complex.ofReal_re _)
    simpa only [Complex.ofReal_re] using hre_int
  have hre_c_sum : HasSum
      (fun n : ℕ => ∫ x in Ioi (1 : ℝ), H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1))
      ((landauRHS P a b C θ (σ_reach : ℂ)).re) := by
    have hre := Complex.reCLM.hasSum htaylor_c
    change HasSum (fun n : ℕ =>
      (iteratedDeriv n (landauRHS P a b C θ) c₀ / (n.factorial : ℂ) * (-(r_step : ℂ)) ^ n).re)
      ((landauRHS P a b C θ (σ_reach : ℂ)).re) at hre
    simp_rw [hterm_c_re] at hre
    exact hre
  have hint_c_term : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1))
      (Ioi 1) := by
    intro n
    have hmid_meas : Measurable (fun x : ℝ => (r_step * Real.log x) ^ n / (n.factorial : ℝ)) :=
      ((measurable_const.mul Real.measurable_log).pow_const n).div_const (n.factorial : ℝ)
    have hpow_meas : Measurable (fun x : ℝ => x ^ (-(σ₀ + r₀) - 1)) :=
      Measurable.pow_const measurable_id (-(σ₀ + r₀) - 1)
    have hae_meas : AEStronglyMeasurable
        (fun x : ℝ => H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1))
        (volume.restrict (Ioi (1 : ℝ))) :=
      (hH_meas.mul hmid_meas.aemeasurable.aestronglyMeasurable).mul
        hpow_meas.aemeasurable.aestronglyMeasurable
    have hk := (integrableOn_mellin_log_pow_of_gt H hH_nonneg hH_meas
      (hint_c₀ (σ₀ + r₀ / 2) (by linarith)) n
      (by linarith) (show σ₀ + r₀ ≤ c₀.re by dsimp [c₀]; linarith)).norm.const_mul (r_step ^ n)
    refine hk.mono' hae_meas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx_pos : 0 < x := lt_trans zero_lt_one hx
    have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hfact_ge1 : (1 : ℝ) ≤ (n.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos n)
    have hterm_nn : 0 ≤ H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) *
        x ^ (-(σ₀ + r₀) - 1) :=
      mul_nonneg
        (mul_nonneg hH0
          (div_nonneg (pow_nonneg (mul_nonneg hr_step_pos.le hlog0) n) (Nat.cast_nonneg _)))
        (Real.rpow_nonneg hx_pos.le _)
    rw [Real.norm_of_nonneg hterm_nn, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hH0, norm_pow, Complex.norm_real, Real.norm_of_nonneg hlog0,
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hrec : (-c₀ - 1).re = -(σ₀ + r₀) - 1 := by simp [c₀]
    rw [hrec, mul_pow]
    have hdiv_le : r_step ^ n * Real.log x ^ n / (n.factorial : ℝ) ≤ r_step ^ n * Real.log x ^ n :=
      div_le_self (by positivity) hfact_ge1
    calc
      H x * (r_step ^ n * Real.log x ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1)
          ≤ H x * (r_step ^ n * Real.log x ^ n) * x ^ (-(σ₀ + r₀) - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv_le hH0) (Real.rpow_nonneg hx_pos.le _)
      _ = r_step ^ n * (H x * Real.log x ^ n * x ^ (-(σ₀ + r₀) - 1)) := by ring
  let fc : ℕ → ℝ → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1))
  have hfc_aemeas : ∀ n : ℕ, AEMeasurable (fc n) (volume.restrict (Ioi (1 : ℝ))) := fun n =>
    (hint_c_term n).aemeasurable.ennreal_ofReal
  let Sc : ℕ → ℝ → ℝ≥0∞ := fun N x => ∑ n ∈ Finset.range N, fc n x
  have hSc_mono : Monotone Sc := fun m n hmn x => Finset.sum_le_sum_of_subset (Finset.range_mono hmn)
  have hSc_sup_le : ∫⁻ x in Ioi (1 : ℝ), (⨆ N : ℕ, Sc N x) ≤
      ENNReal.ofReal ((landauRHS P a b C θ (σ_reach : ℂ)).re) := by
    rw [MeasureTheory.lintegral_iSup'
      (fun N => Finset.aemeasurable_fun_sum (Finset.range N) (fun n _ => hfc_aemeas n))
      (Eventually.of_forall fun x m n hmn => hSc_mono hmn x)]
    refine iSup_le fun N => ?_
    rw [lintegral_finset_sum_aemeas _ (Finset.range N) fc hfc_aemeas]
    have hterm_l : ∀ n : ℕ, ∫⁻ x in Ioi (1 : ℝ), fc n x =
        ENNReal.ofReal (∫ x in Ioi (1 : ℝ),
          H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1)) := by
      intro n
      symm
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint_c_term n)
        (by
          change ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
            0 ≤ H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1)
          rw [ae_restrict_iff' measurableSet_Ioi]
          refine Eventually.of_forall fun x hx => ?_
          have hx_pos : 0 < x := lt_trans zero_lt_one hx
          have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
          have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
          positivity)
    simp_rw [hterm_l]
    have hnn : ∀ n : ℕ, 0 ≤ ∫ x in Ioi (1 : ℝ),
        H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1) := by
      intro n
      refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      positivity
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hnn n)]
    exact ENNReal.ofReal_le_ofReal (sum_le_hasSum (Finset.range N) (fun n _ => hnn n) hre_c_sum)
  have hint_reach : IntegrableOn (fun x : ℝ => H x * x ^ (-σ_reach - 1)) (Ioi 1) := by
    have hsup_ae : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
        ENNReal.ofReal (H x * x ^ (-σ_reach - 1)) = ⨆ N : ℕ, Sc N x := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hH0 : 0 ≤ H x := hH_nonneg x (le_of_lt hx)
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      have hexp_hasSum : HasSum (fun n : ℕ => (r_step * Real.log x) ^ n / (n.factorial : ℝ))
          (Real.exp (r_step * Real.log x)) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
        exact (NormedSpace.expSeries_div_summable (r_step * Real.log x)).hasSum
      have hmul_hasSum : HasSum
          (fun n : ℕ => H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1))
          (H x * x ^ (-σ_reach - 1)) := by
        have h1 := (hexp_hasSum.mul_left (H x)).mul_right (x ^ (-(σ₀ + r₀) - 1))
        have hval : H x * Real.exp (r_step * Real.log x) * x ^ (-(σ₀ + r₀) - 1) =
            H x * x ^ (-σ_reach - 1) := by
          rw [mul_comm r_step (Real.log x), Real.exp_mul, Real.exp_log hx_pos, mul_assoc,
            ← Real.rpow_add hx_pos]
          congr 2
          dsimp [r_step, σ_reach]; ring
        rw [hval] at h1
        simpa [mul_assoc] using h1
      have ht := hmul_hasSum.tendsto_sum_nat
      have ht_sc : Tendsto (fun N : ℕ => Sc N x) atTop (𝓝 (ENNReal.ofReal (H x * x ^ (-σ_reach - 1)))) := by
        have heq : (fun N : ℕ => Sc N x) = (fun N : ℕ => ENNReal.ofReal (∑ n ∈ Finset.range N,
            H x * ((r_step * Real.log x) ^ n / (n.factorial : ℝ)) * x ^ (-(σ₀ + r₀) - 1))) := by
          ext N; dsimp [Sc, fc]; rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
        rw [heq]
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
      exact tendsto_nhds_unique ht_sc (tendsto_atTop_iSup (fun m n hmn => hSc_mono hmn x))
    have hlint_fin : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (H x * x ^ (-σ_reach - 1)) < ⊤ := by
      rw [lintegral_congr_ae hsup_ae]
      exact lt_of_le_of_lt hSc_sup_le ENNReal.ofReal_lt_top
    have hmeas_t : AEStronglyMeasurable (fun x : ℝ => H x * x ^ (-σ_reach - 1))
        (volume.restrict (Ioi (1 : ℝ))) :=
      hH_meas.mul (Measurable.pow_const measurable_id (-σ_reach - 1)).aemeasurable.aestronglyMeasurable
    have hnn_t : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun x : ℝ => H x * x ^ (-σ_reach - 1) := by
      change ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), 0 ≤ H x * x ^ (-σ_reach - 1)
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      exact mul_nonneg (hH_nonneg x (le_of_lt hx)) (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)
    exact ⟨hmeas_t, (hasFiniteIntegral_iff_ofReal hnn_t).mpr hlint_fin⟩
  let M : ℂ → ℂ := fun z => ∫ x in Ioi (1 : ℝ), (H x : ℂ) * (x : ℂ) ^ (-z - 1)
  have hM_diff_reach : DifferentiableOn ℂ M (halfPlane σ_reach) := by
    intro s hs
    change σ_reach < s.re at hs
    let σ' : ℝ := (σ_reach + s.re) / 2
    have hσ'_gt : σ_reach < σ' := by dsimp [σ']; linarith
    have hσ'_lt : σ' < s.re := by dsimp [σ']; linarith
    let δ' : ℝ := (s.re - σ') / 2
    have hδ'_pos : 0 < δ' := by dsimp [δ']; linarith
    let ε' : ℝ := (σ' - σ_reach) / 2
    have hε'_pos : 0 < ε' := by dsimp [ε']; linarith
    have hσ'_dom_gt : σ_reach < σ' - ε' := by dsimp [ε', σ']; linarith
    let C_log : ℝ := max 1 ((1 : ℝ) / ε') ^ 1
    let F : ℂ → ℝ → ℂ := fun z x => (H x : ℂ) * (x : ℂ) ^ (-z - 1)
    let F' : ℂ → ℝ → ℂ := fun z x => (H x : ℂ) * ((x : ℂ) ^ (-z - 1) * Complex.log (x : ℂ) * (-1))
    let bound : ℝ → ℝ := fun x => C_log * (H x * x ^ (-(σ' - ε') - 1))
    have hball_re : ∀ z ∈ Metric.ball s δ', σ' ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have habs : |z.re - s.re| ≤ ‖z - s‖ := by
        simpa [sub_re] using Complex.abs_re_le_norm (z - s)
      have hlow : s.re - δ' ≤ z.re := by linarith [(abs_le.mp (habs.trans hz.le)).1]
      dsimp [δ'] at hlow
      linarith
    have hint_dom' : IntegrableOn (fun x : ℝ => H x * x ^ (-(σ' - ε') - 1)) (Ioi 1) := by
      refine hint_reach.mono'
        (hH_meas.mul (Measurable.pow_const measurable_id (-(σ' - ε') - 1)).aemeasurable.aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      have hx_ge1 : 1 ≤ x := le_of_lt hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hH0 : 0 ≤ H x := hH_nonneg x hx_ge1
      rw [Real.norm_of_nonneg (mul_nonneg hH0 (Real.rpow_nonneg hx_pos.le _))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx_ge1 (by linarith)) hH0
    have hint_k0 : ∀ z : ℂ, σ' ≤ z.re →
        IntegrableOn (fun x : ℝ => (H x : ℂ) * (x : ℂ) ^ (-z - 1)) (Ioi 1) := by
      intro z hz
      refine hint_reach.mono'
        ((Complex.measurable_ofReal.comp_aemeasurable hH_meas.aemeasurable).aestronglyMeasurable.mul
          (aestronglyMeasurable_ofReal_cpow_Ioi (-z - 1))) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      have hx_ge1 : 1 ≤ x := le_of_lt hx
      have hx_pos : 0 < x := lt_trans zero_lt_one hx
      have hH0 : 0 ≤ H x := hH_nonneg x hx_ge1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hH0,
        Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
      have hre : (-z - 1).re ≤ -σ_reach - 1 := by
        rw [sub_re, neg_re, one_re]
        have : σ_reach ≤ z.re := le_trans hσ'_gt.le hz
        linarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx_ge1 hre) hH0
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      (Metric.ball_mem_nhds s hδ'_pos)
      ?_ ?_ ?_ ?_ (hint_dom'.const_mul C_log) ?_
    · exact hd.2.differentiableAt.differentiableWithinAt
    · filter_upwards [Metric.ball_mem_nhds s hδ'_pos] with z hz
      exact (hint_k0 z (hball_re z hz)).aestronglyMeasurable
    · exact hint_k0 s hσ'_lt.le
    · have hlogC : AEStronglyMeasurable (fun x : ℝ => Complex.log (x : ℂ))
          (volume.restrict (Ioi (1 : ℝ))) :=
        (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable
      have hinner : AEStronglyMeasurable
          (fun x : ℝ => (x : ℂ) ^ (-s - 1) * Complex.log (x : ℂ) * (-1 : ℂ))
          (volume.restrict (Ioi (1 : ℝ))) :=
        ((aestronglyMeasurable_ofReal_cpow_Ioi (-s - 1)).mul hlogC).mul
          aestronglyMeasurable_const
      exact (Complex.measurable_ofReal.comp_aemeasurable hH_meas.aemeasurable).aestronglyMeasurable.mul hinner
    · rw [ae_restrict_iff' measurableSet_Ioi]
      have hCnn : 0 ≤ C_log := by
        dsimp [C_log]; exact pow_nonneg (zero_le_one.trans (le_max_left 1 _)) 1
      refine Eventually.of_forall fun x hx z hz => ?_
      have hlog_pow : |Real.log x| ^ 1 ≤ C_log * x ^ ε' := by
        dsimp [C_log]
        simpa using abs_log_pow_le_rpow (k := 1) hε'_pos (le_of_lt hx)
      have hnorm := norm_mellin_deriv_le (k := 0) hx (hH_nonneg x (le_of_lt hx)) (hball_re z hz) hCnn hlog_pow
      have hexp : -(σ' - ε') - 1 = ε' - σ' - 1 := by ring
      dsimp only [F', bound]
      rw [hexp]
      simpa [pow_zero, mul_one, mul_assoc] using hnorm
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun x hx z _ =>
        hasDerivAt_mellin_integrand ((H x : ℂ)) hx z
  let LHS_cd : ℂ → ℂ := fun z => M z * P z * (z * (z - 1)) * (z - (θ : ℂ))
  let RHS_cd : ℂ → ℂ := fun z =>
    (deriv P z - (a + b * z) * P z) * (z - (θ : ℂ)) + (C : ℂ) * P z * (z * (z - 1))
  have hderivP : Differentiable ℂ (deriv P) :=
    fun z => (hP_diff.analyticAt z).deriv.differentiableAt
  have hRHS_cd_diff : Differentiable ℂ RHS_cd := by
    dsimp [RHS_cd]
    exact ((hderivP.sub (((differentiable_const a).add ((differentiable_const b).mul differentiable_id)).mul hP_diff)).mul
      (differentiable_id.sub (differentiable_const (θ : ℂ)))).add
      (((differentiable_const (C : ℂ)).mul hP_diff).mul
        (differentiable_id.mul (differentiable_id.sub (differentiable_const 1))))
  have hLHS_cd_diffOn : DifferentiableOn ℂ LHS_cd (halfPlane σ_reach) := by
    intro z hz
    exact (((hM_diff_reach z hz).mul (hP_diff z).differentiableWithinAt).mul
      ((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))) z).differentiableWithinAt).mul
      ((differentiable_id.sub (differentiable_const (θ : ℂ))) z).differentiableWithinAt
  have hU_reach_open : IsOpen (halfPlane σ_reach) := isOpen_lt continuous_const Complex.continuous_re
  have hU_reach_conv : Convex ℝ (halfPlane σ_reach) := by
    intro x hx y hy a' b' ha' hb' hab'
    change σ_reach < x.re at hx
    change σ_reach < y.re at hy
    change σ_reach < (a' • x + b' • y).re
    simp only [add_re, real_smul, mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    by_cases ha0 : a' = 0
    · subst ha0; simp at hab'; subst hab'; simpa using hy
    · have ha_pos : 0 < a' := lt_of_le_of_ne ha' (Ne.symm ha0)
      have hx' : a' * σ_reach < a' * x.re := mul_lt_mul_of_pos_left hx ha_pos
      have hy' : b' * σ_reach ≤ b' * y.re := mul_le_mul_of_nonneg_left (le_of_lt hy) hb'
      calc
        σ_reach = (a' + b') * σ_reach := by rw [hab', one_mul]
        _ = a' * σ_reach + b' * σ_reach := add_mul a' b' σ_reach
        _ < a' * x.re + b' * y.re := add_lt_add_of_lt_of_le hx' hy'
  have hc₀_mem_reach : c₀ ∈ halfPlane σ_reach := by
    change σ_reach < c₀.re; dsimp [c₀, σ_reach]; linarith
  have hfreq_cd : ∃ᶠ z in nhdsWithin c₀ {c₀}ᶜ, LHS_cd z = RHS_cd z := by
    have hev : ∀ᶠ z in nhdsWithin c₀ {c₀}ᶜ, z ∈ halfPlane σ₀ :=
      nhdsWithin_le_nhds (hopen_σ₀.mem_nhds hc₀_gt_σ₀)
    refine hev.frequently.mono fun z hz => ?_
    have hPz_ne : P z ≠ 0 := hP_gt_σ₀ z hz
    have hz_gt_θ : θ < z.re := lt_trans hσ₀_gt_θ hz
    have hz_ne0 : z ≠ 0 := by
      intro h0; rw [h0, zero_re] at hz_gt_θ; linarith
    have hz_ne_θ : z - (θ : ℂ) ≠ 0 := by
      intro hsub; rw [sub_eq_zero] at hsub
      have hre : z.re = θ := by rw [hsub, Complex.ofReal_re]
      linarith
    have hMz : M z = landauRHS P a b C θ z := hMellin_σ₀ hz
    dsimp [LHS_cd, RHS_cd]
    rw [hMz]
    by_cases hz1 : z = 1
    · subst hz1
      calc
        landauRHS P a b C θ 1 * P 1 * (1 * (1 - 1)) * (1 - (θ : ℂ)) = 0 := by ring
        _ = (deriv P 1 - (a + b) * P 1) * (1 - (θ : ℂ)) := by rw [hP_one, zero_mul]
        _ = (deriv P 1 - (a + b * 1) * P 1) * (1 - (θ : ℂ)) + (C : ℂ) * P 1 * (1 * (1 - 1)) := by ring
    · have hz_ne1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      rw [landauRHS_eq_of_ne_one P a b C θ hz1]
      dsimp [logDeriv]
      field_simp [hPz_ne, hz_ne0, hz_ne1, hz_ne_θ]
  have hcd_eqOn : EqOn LHS_cd RHS_cd (halfPlane σ_reach) :=
    (hLHS_cd_diffOn.analyticOnNhd hU_reach_open).eqOn_of_preconnected_of_frequently_eq
      (hRHS_cd_diff.differentiableOn.analyticOnNhd hU_reach_open)
      hU_reach_conv.isPreconnected hc₀_mem_reach hfreq_cd
  have hz₁_mem_reach : z₁ ∈ halfPlane σ_reach := by
    change σ_reach < z₁.re; dsimp [σ_reach]; linarith
  have hz₁_ne_θ : z₁ - (θ : ℂ) ≠ 0 := by
    intro hsub; rw [sub_eq_zero] at hsub
    have hre : z₁.re = θ := by rw [hsub, Complex.ofReal_re]
    have hr₀_le2 : r₀ ≤ (σ₀ - θ) / 4 := min_le_right _ _
    linarith
  exact not_cleared_denom_eq_at_zero (hM_diff_reach.differentiableAt (hU_reach_open.mem_nhds hz₁_mem_reach))
    hP_diff hP_nzero hPz₁ hz₁_ne_θ (hcd_eqOn.eventuallyEq_of_mem (hU_reach_open.mem_nhds hz₁_mem_reach))

end GRHIteratedThetaLifts.Section3A
