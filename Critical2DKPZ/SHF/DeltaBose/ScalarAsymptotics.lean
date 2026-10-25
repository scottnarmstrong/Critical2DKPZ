/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Small-time asymptotics of the scalar collision density

Rescaling the Gamma integral by the negative logarithm of time reduces the
asymptotic to dominated convergence and `Γ(1) = 1`. This is independent of the
heat kernel and of the operator-valued collision estimates.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Critical2DKPZ.DeltaBose

/-- The rescaled Gamma integrand, with the singularity at zero removed by recurrence. -/
noncomputable def scaledGammaIntegrand (θ L v : ℝ) : ℝ :=
  v * Real.exp ((θ / L - 1) * v) / Real.Gamma (1 + v / L)

/-- The pointwise substitution in the Laplace integral. -/
theorem scaledGammaIntegrand_eq (θ : ℝ) {L v : ℝ} (hL : 0 < L) (hv : 0 < v) :
    scaledGammaIntegrand θ L v = L * gammaLaplaceIntegrand (θ - L) (L⁻¹ * v) := by
  have hu : 0 < v / L := div_pos hv hL
  rw [scaledGammaIntegrand, gammaLaplaceIntegrand, add_comm 1,
    Real.Gamma_add_one hu.ne']
  have he : (θ / L - 1) * v = (θ - L) * (L⁻¹ * v) := by field_simp
  rw [he]
  field_simp

/-- The change of variables in the absolutely convergent scalar integral. -/
theorem integral_scaledGammaIntegrand (θ : ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ v in Ioi 0, scaledGammaIntegrand θ L v) =
      L ^ 2 * ∫ u in Ioi 0, gammaLaplaceIntegrand (θ - L) u := by
  calc (∫ v in Ioi 0, scaledGammaIntegrand θ L v)
      = ∫ v in Ioi 0, L * gammaLaplaceIntegrand (θ - L) (L⁻¹ * v) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        exact scaledGammaIntegrand_eq θ hL hv
    _ = L ^ 2 * ∫ u in Ioi 0, gammaLaplaceIntegrand (θ - L) u := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 (inv_pos.mpr hL)]
      simp only [mul_zero, inv_inv, smul_eq_mul, pow_two, mul_assoc]

/-- The rescaled density is measurable on the positive integration domain. -/
theorem continuousOn_scaledGammaIntegrand (θ : ℝ) {L : ℝ} (hL : 0 < L) :
    ContinuousOn (scaledGammaIntegrand θ L) (Ioi 0) := by
  unfold scaledGammaIntegrand
  apply ContinuousOn.div
  · fun_prop
  · apply Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (by fun_prop : ContinuousOn (fun v : ℝ => 1 + v / L) (Ioi 0))
    intro v hv
    exact add_pos zero_lt_one (div_pos hv hL)
  · intro v hv
    exact (Real.Gamma_pos_of_pos (add_pos zero_lt_one (div_pos hv hL))).ne'

/-- A common majorant for the rescaled integrands at large logarithmic times. -/
theorem scaledGammaIntegrand_le {θ L v m : ℝ} (hL : 0 < L) (hv : 0 < v)
    (hm : 0 < m) (hGamma : ∀ u : ℝ, 0 < u → m ≤ Real.Gamma u)
    (hθ : 2 * |θ| ≤ L) :
    |scaledGammaIntegrand θ L v| ≤ m⁻¹ * (v * Real.exp (-((1 / 2 : ℝ) * v))) := by
  have hg := Real.Gamma_pos_of_pos (add_pos zero_lt_one (div_pos hv hL))
  have hpos : 0 < scaledGammaIntegrand θ L v := div_pos (mul_pos hv (Real.exp_pos _)) hg
  rw [abs_of_pos hpos, scaledGammaIntegrand, div_eq_mul_inv]
  have hexp : Real.exp ((θ / L - 1) * v) ≤ Real.exp (-((1 / 2 : ℝ) * v)) := by
    apply Real.exp_le_exp.mpr
    have hθL : θ / L ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith only [hθ, le_abs_self θ])
    nlinarith only [mul_nonneg (sub_nonneg.mpr hθL) hv.le]
  have hinv : (Real.Gamma (1 + v / L))⁻¹ ≤ m⁻¹ :=
    inv_anti₀ hm (hGamma _ (by positivity))
  calc v * Real.exp ((θ / L - 1) * v) * (Real.Gamma (1 + v / L))⁻¹
      ≤ (v * Real.exp (-((1 / 2 : ℝ) * v))) * m⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp hv.le) hinv
          (inv_nonneg.mpr hg.le) (by positivity)
    _ = _ := mul_comm _ _

/-- Pointwise convergence of the rescaled integrand. -/
theorem tendsto_scaledGammaIntegrand (θ v : ℝ) :
    Tendsto (fun L : ℝ => scaledGammaIntegrand θ L v) atTop (𝓝 (v * Real.exp (-v))) := by
  have hθ : Tendsto (fun L : ℝ => θ / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hv : Tendsto (fun L : ℝ => v / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hg : ContinuousAt Real.Gamma 1 :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.continuousAt (isOpen_Ioi.mem_nhds zero_lt_one)
  have hv1 : Tendsto (fun L : ℝ => 1 + v / L) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hv
  have he : Tendsto (fun L : ℝ => Real.exp ((θ / L - 1) * v)) atTop
      (𝓝 (Real.exp (-v))) := by
    simpa only [Function.comp_def, zero_sub, neg_one_mul] using
      Real.continuous_exp.continuousAt.tendsto.comp ((hθ.sub_const 1).mul_const v)
  have hnum : Tendsto (fun L : ℝ => v * Real.exp ((θ / L - 1) * v)) atTop
      (𝓝 (v * Real.exp (-v))) := he.const_mul v
  have hden : Tendsto (fun L : ℝ => Real.Gamma (1 + v / L)) atTop (𝓝 (Real.Gamma 1)) :=
    hg.tendsto.comp hv1
  have h : Tendsto (fun L : ℝ => v * Real.exp ((θ / L - 1) * v) / Real.Gamma (1 + v / L))
      atTop (𝓝 ((v * Real.exp (-v)) / Real.Gamma 1)) :=
    hnum.div hden (by simp)
  simpa only [scaledGammaIntegrand, Real.Gamma_one, div_one] using h

/-- The normalized scalar integral converges to one. -/
theorem tendsto_integral_scaledGammaIntegrand (θ : ℝ) :
    Tendsto (fun L : ℝ => ∫ v in Ioi 0, scaledGammaIntegrand θ L v) atTop (𝓝 1) := by
  obtain ⟨m, hm, hGamma⟩ := exists_pos_le_gamma
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (μ := volume.restrict (Ioi 0))
    (fun v : ℝ => m⁻¹ * (v * Real.exp (-((1 / 2 : ℝ) * v))))
    (F := fun L v : ℝ => scaledGammaIntegrand θ L v)
    (f := fun v : ℝ => v * Real.exp (-v))
    ?_ ?_ ?_ ?_
  · simpa only [show (fun v : ℝ => v * Real.exp (-v)) =
        (fun v : ℝ => v * Real.exp (-(1 * v))) by funext; rw [one_mul],
      integral_mul_exp_neg zero_lt_one, inv_one, one_pow] using h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact (continuousOn_scaledGammaIntegrand θ (by linarith)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [eventually_ge_atTop (max 1 (2 * |θ|))] with L hL
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]
    exact scaledGammaIntegrand_le (by linarith only [le_max_left (1 : ℝ) (2 * |θ|), hL])
      hv hm hGamma ((le_max_right _ _).trans hL)
  · exact (integrableOn_mul_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)).const_mul m⁻¹
  · exact Filter.Eventually.of_forall (tendsto_scaledGammaIntegrand θ)

/-- Small-time asymptotics in logarithmic time, equivalent to `t (log t)^2 j_θ(t) → 1`. -/
theorem tendsto_exp_neg_mul_scalarDensity (θ : ℝ) :
    Tendsto (fun L : ℝ => Real.exp (-L) * L ^ 2 * scalarDensity θ (Real.exp (-L)))
      atTop (𝓝 1) := by
  apply (tendsto_integral_scaledGammaIntegrand θ).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [integral_scaledGammaIntegrand θ hL,
    scalarDensity_eq_laplace θ (Real.exp_pos _), Real.log_exp]
  rw [show θ + -L = θ - L by ring]
  field_simp

/-- The sharp small-time asymptotic in the original time variable. -/
theorem tendsto_mul_log_sq_scalarDensity (θ : ℝ) :
    Tendsto (fun t : ℝ => t * (Real.log t) ^ 2 * scalarDensity θ t) (𝓝[>] 0) (𝓝 1) := by
  have hL : Tendsto (fun t : ℝ => -Real.log t) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply ((tendsto_exp_neg_mul_scalarDensity θ).comp hL).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_apply, neg_neg, Real.exp_log ht, neg_sq]

end Critical2DKPZ.DeltaBose
