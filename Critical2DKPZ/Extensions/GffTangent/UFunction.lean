/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# The integrated collision density

The function `uFun` is the function in (6.4) of the four-results note.
The tangent inequality for log Gamma gives its sharp exponential majorant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The integrated collision density at parameter `-l`. -/
noncomputable def uFun (l u : ℝ) : ℝ :=
  ∫ z in Ioi 0, Real.exp (-(l - Real.log u) * z -
    Real.eulerMascheroniConstant * z) / Real.Gamma (1 + z)

/-- The tangent to log Gamma at one bounds the normalized reciprocal Gamma. -/
theorem exp_neg_mul_div_gamma_le_one {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma (1 + z) ≤ 1 := by
  rcases hz.eq_or_lt with hz | hz
  · subst z
    simp only [mul_zero, Real.exp_zero, add_zero, Real.Gamma_one, div_one, le_refl]
  have hg : 0 < Real.Gamma (1 + z) := Real.Gamma_pos_of_pos (by positivity)
  apply (div_le_one hg).mpr
  rw [← Real.exp_log hg, Real.exp_le_exp]
  have hd : HasDerivAt (Real.log ∘ Real.Gamma) (-Real.eulerMascheroniConstant) 1 := by
    simpa only [Real.Gamma_one, div_one, Function.comp_def] using
      Real.hasDerivAt_Gamma_one.log (by simp only [Real.Gamma_one, ne_eq, one_ne_zero,
        not_false_eq_true])
  have hs := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt
    (by norm_num : (1 : ℝ) ∈ Ioi 0) (by change 0 < 1 + z; positivity : 1 + z ∈ Ioi 0)
    (by linarith : (1 : ℝ) < 1 + z) hd
  simp only [slope_def_field, Function.comp_apply, Real.Gamma_one, Real.log_one,
    sub_zero, add_sub_cancel_left] at hs
  exact (le_div_iff₀ hz).mp hs

/-- Continuity of the integrand on its positive integration domain. -/
theorem continuousOn_uFun_integrand (l u : ℝ) :
    ContinuousOn (fun z => Real.exp (-(l - Real.log u) * z -
      Real.eulerMascheroniConstant * z) / Real.Gamma (1 + z)) (Ioi 0) := by
  apply ContinuousOn.div
  · fun_prop
  · apply Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
    intro z hz
    exact add_pos zero_lt_one hz
  · intro z hz
    exact (Real.Gamma_pos_of_pos (add_pos zero_lt_one hz)).ne'

/-- Pointwise domination by the elementary exponential density. -/
theorem uFun_integrand_le (l u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-(l - Real.log u) * z - Real.eulerMascheroniConstant * z) /
      Real.Gamma (1 + z) ≤ Real.exp (-(l - Real.log u) * z) := by
  rw [sub_eq_add_neg, Real.exp_add, mul_div_assoc]
  simpa only [neg_mul] using mul_le_of_le_one_right (Real.exp_nonneg (-(l - Real.log u) * z))
    (exp_neg_mul_div_gamma_le_one hz)

/-- Absolute integrability, accompanying the bound on `uFun`. -/
theorem integrableOn_uFun_integrand {l u : ℝ} (hu : Real.log u < l) :
    IntegrableOn (fun z => Real.exp (-(l - Real.log u) * z -
      Real.eulerMascheroniConstant * z) / Real.Gamma (1 + z)) (Ioi 0) := by
  apply (integrableOn_exp_mul_Ioi (by linarith : -(l - Real.log u) < 0) 0).mono'
    ((continuousOn_uFun_integrand l u).aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _)
      (Real.Gamma_pos_of_pos (add_pos zero_lt_one hz)))]
    exact uFun_integrand_le l u hz.le

/-- Positivity and the sharp upper bound in (6.4); see the companion integrability lemma. -/
theorem uFun_pos_le {l u : ℝ} (_hu : 0 < u) (hul : Real.log u < l) :
    0 < uFun l u ∧ uFun l u ≤ 1 / (l - Real.log u) := by
  have hi := integrableOn_uFun_integrand hul
  constructor
  · unfold uFun
    apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).mpr
    · have he : Function.support (fun z => Real.exp (-(l - Real.log u) * z -
          Real.eulerMascheroniConstant * z) / Real.Gamma (1 + z)) ∩ Ioi 0 = Ioi 0 := by
        apply inter_eq_right.mpr
        intro z hz
        exact (div_pos (Real.exp_pos _)
          (Real.Gamma_pos_of_pos (add_pos zero_lt_one hz))).ne'
      rw [he, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact (div_pos (Real.exp_pos _)
        (Real.Gamma_pos_of_pos (add_pos zero_lt_one hz))).le
  · calc uFun l u ≤ ∫ z in Ioi 0, Real.exp (-(l - Real.log u) * z) := by
          apply integral_mono_ae hi
            (integrableOn_exp_mul_Ioi (by linarith : -(l - Real.log u) < 0) 0)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
          exact uFun_integrand_le l u hz.le
      _ = 1 / (l - Real.log u) := by
        rw [integral_exp_mul_Ioi (by linarith : -(l - Real.log u) < 0) 0]
        simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

/-- The integrand after the substitution `z = s / l`. -/
noncomputable def scaledUIntegrand (l u s : ℝ) : ℝ :=
  Real.exp (-(1 - Real.log u / l) * s - Real.eulerMascheroniConstant * (s / l)) /
    Real.Gamma (1 + s / l)

/-- Rescaling the positive half-line extracts the prefactor `l`. -/
theorem integral_scaledUIntegrand {l : ℝ} (hl : 0 < l) (u : ℝ) :
    (∫ s in Ioi 0, scaledUIntegrand l u s) = l * uFun l u := by
  have he (s : ℝ) : scaledUIntegrand l u s =
      Real.exp (-(l - Real.log u) * (l⁻¹ * s) -
        Real.eulerMascheroniConstant * (l⁻¹ * s)) / Real.Gamma (1 + l⁻¹ * s) := by
    unfold scaledUIntegrand
    rw [div_eq_mul_inv s, mul_comm s l⁻¹]
    congr 2
    field_simp
  simp_rw [he]
  rw [integral_comp_mul_left_Ioi
    (fun z => Real.exp (-(l - Real.log u) * z - Real.eulerMascheroniConstant * z) /
      Real.Gamma (1 + z)) 0 (inv_pos.mpr hl)]
  simp only [mul_zero, inv_inv, smul_eq_mul, uFun]

/-- Pointwise convergence of the rescaled integrands. -/
theorem tendsto_scaledUIntegrand (u : ℝ → ℝ)
    (hu : Tendsto (fun l => Real.log (u l) / l) atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun l => scaledUIntegrand l (u l) s) atTop (𝓝 (Real.exp (-s))) := by
  have hs : Tendsto (fun l : ℝ => s / l) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hexp : Tendsto (fun l => -(1 - Real.log (u l) / l) * s -
      Real.eulerMascheroniConstant * (s / l)) atTop (𝓝 (-s)) := by
    simpa only [sub_zero, neg_mul, one_mul, mul_zero] using
      ((((tendsto_const_nhds (x := (1 : ℝ))).sub hu).neg.mul_const s).sub
        (hs.const_mul Real.eulerMascheroniConstant))
  have hg : ContinuousAt Real.Gamma 1 :=
    Real.hasDerivAt_Gamma_one.continuousAt
  have hden : Tendsto (fun l => Real.Gamma (1 + s / l)) atTop (𝓝 (Real.Gamma 1)) :=
    hg.tendsto.comp (by simpa only [add_zero] using tendsto_const_nhds.add hs)
  simpa only [scaledUIntegrand, Real.Gamma_one, div_one, Function.comp_def, Pi.div_def] using
    (Real.continuous_exp.continuousAt.tendsto.comp hexp).div hden
      (by rw [Real.Gamma_one]; exact one_ne_zero)

/-- A uniform exponential majorant when the logarithmic horizon is small. -/
theorem scaledUIntegrand_le {l u s : ℝ} (hl : 0 < l) (hs : 0 < s)
    (hu : Real.log u / l ≤ 1 / 2) :
    ‖scaledUIntegrand l u s‖ ≤ Real.exp (-(1 / 2 : ℝ) * s) := by
  have hpos : 0 < scaledUIntegrand l u s :=
    div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos (by positivity))
  rw [Real.norm_eq_abs, abs_of_pos hpos, scaledUIntegrand, sub_eq_add_neg,
    Real.exp_add, mul_div_assoc]
  calc Real.exp (-(1 - Real.log u / l) * s) *
        (Real.exp (-(Real.eulerMascheroniConstant * (s / l))) / Real.Gamma (1 + s / l))
      ≤ Real.exp (-(1 - Real.log u / l) * s) := by
        apply mul_le_of_le_one_right (Real.exp_nonneg _)
        simpa only [neg_mul] using exp_neg_mul_div_gamma_le_one (by positivity : 0 ≤ s / l)
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hs.le)

/-- The asymptotic assertion in (6.4), for subexponential positive horizons. -/
theorem tendsto_mul_uFun (u : ℝ → ℝ) (_hu : ∀ l, 0 < u l)
    (hlog : Tendsto (fun l => Real.log (u l) / l) atTop (𝓝 0)) :
    Tendsto (fun l => l * uFun l (u l)) atTop (𝓝 1) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (μ := volume.restrict (Ioi 0))
    (F := fun l s => scaledUIntegrand l (u l) s)
    (f := fun s => Real.exp (-s)) (fun s => Real.exp (-(1 / 2 : ℝ) * s)) ?_ ?_ ?_ ?_
  · have hi : (∫ s in Ioi 0, Real.exp (-s)) = 1 := by
      simpa only [neg_one_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, div_one] using
        integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    rw [hi] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
    exact integral_scaledUIntegrand hl (u l)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
    have hc : ContinuousOn (scaledUIntegrand l (u l)) (Ioi 0) := by
      unfold scaledUIntegrand
      apply ContinuousOn.div
      · fun_prop
      · apply Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
        intro s hs
        exact add_pos zero_lt_one (div_pos hs hl)
      · intro s hs
        exact (Real.Gamma_pos_of_pos (add_pos zero_lt_one (div_pos hs hl))).ne'
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hlog.eventually (gt_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 2))] with l hl hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact scaledUIntegrand_le hl hs hu.le
  · exact integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0
  · exact Filter.Eventually.of_forall (tendsto_scaledUIntegrand u hlog)

end Critical2DKPZ.Extensions.GffTangent
