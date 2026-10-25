/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralGrowth
public import Critical2DKPZ.Spectral.FourierMeasurePairing
import Critical2DKPZ.CovarianceKernel.BallAsymptotic
import Critical2DKPZ.CovarianceKernel.RadialInversion

/-! # Deterministic spectral scale comparisons for the shape lemma -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Fixed positive changes of frequency radius have the same normalized mass. -/
theorem specMass_scaled_inv_tendsto (ν : Measure Plane)
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    {k : ℝ} (hk : 0 < k) :
    Tendsto (fun ε : ℝ => specMass ν (k / ε) / Real.log (Real.log ε⁻¹))
      (𝓝[>] 0) (𝓝 1) := by
  have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hscale := hinv.const_mul_atTop hk
  have hnum := hball.comp hscale
  have hratio := (CovarianceKernel.tendsto_logLog_mul_div_of_pos_const k hk).comp hinv
  have hden := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hscale)
  have hp : Tendsto (fun ε : ℝ =>
      (specMass ν (k * ε⁻¹) / Real.log (Real.log (k * ε⁻¹))) *
      (Real.log (Real.log (k * ε⁻¹)) / Real.log (Real.log ε⁻¹))) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_apply, mul_one] using hnum.mul hratio
  apply hp.congr'
  filter_upwards [hden.eventually_gt_atTop 0] with ε hε
  dsimp only [Function.comp_apply] at hε
  rw [div_eq_mul_inv k ε]
  exact div_mul_div_cancel₀ hε.ne'

/-- The mass of a fixed rescaled annulus is negligible on the double-logarithmic scale. -/
theorem specMass_scaled_annulus_tendsto (ν : Measure Plane)
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun ε : ℝ => (specMass ν (b / ε) - specMass ν (a / ε)) /
      Real.log (Real.log ε⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (specMass_scaled_inv_tendsto ν hball hb).sub
    (specMass_scaled_inv_tendsto ν hball ha)
  simpa only [sub_self, sub_div] using ht


end Critical2DKPZ.Extensions.ScaleLimit
