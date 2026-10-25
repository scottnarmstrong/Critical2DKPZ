/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Cutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Cutoff convergence for smoothed products

Absolute integrability of a compact endpoint pairing implies convergence when both intermediate-variable cutoffs are removed. -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- For a well-defined product, removing both intermediate-variable cutoffs recovers the pairing. -/
theorem smoothedProductPairing_cutoff_tendsto (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) (hwm : Measurable w) (f : C_c(Plane × Plane, ℝ))
    (hdef : SmoothedProductWellDefined μ w ν) :
    Tendsto (fun R : ℝ => ∫ q, f (q.1.1, q.2.2) * w (q.1.2 - q.2.1) *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν)) atTop
      (𝓝 (smoothedProductPairing μ w ν f)) := by
  let g := fun q : (Plane × Plane) × (Plane × Plane) => f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
  have hg : Integrable g (μ.prod ν) := hdef f
  have hmeas (R : ℝ) : AEStronglyMeasurable
      (fun q => g q * ballCutoff R q.1.2 * ballCutoff R q.2.1) (μ.prod ν) := by
    apply Measurable.aestronglyMeasurable
    exact ((f.continuous.measurable.comp (by fun_prop)).mul
      (hwm.comp (by fun_prop))).mul
        ((continuous_ballCutoff R).measurable.comp (by fun_prop)) |>.mul
          ((continuous_ballCutoff R).measurable.comp (by fun_prop))
  have hbound (R : ℝ) : ∀ᵐ q ∂μ.prod ν,
      ‖g q * ballCutoff R q.1.2 * ballCutoff R q.2.1‖ ≤ |g q| := by
    filter_upwards with q
    have hx := ballCutoff_mem_Icc R q.1.2
    have hy := ballCutoff_mem_Icc R q.2.1
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg hx.1 hy.1)]
    have hc : ballCutoff R q.1.2 * ballCutoff R q.2.1 ≤ 1 := by
      nlinarith only [hx.1, hx.2, hy.1, hy.2]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (abs_nonneg (g q))
  have hlim : ∀ᵐ q ∂μ.prod ν, Tendsto
      (fun R : ℝ => g q * ballCutoff R q.1.2 * ballCutoff R q.2.1) atTop (𝓝 (g q)) := by
    filter_upwards with q
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => g q) atTop (𝓝 (g q))).mul
      (tendsto_ballCutoff q.1.2)).mul (tendsto_ballCutoff q.2.1)
    simpa only [mul_one] using h
  exact tendsto_integral_filter_of_dominated_convergence (fun q => |g q|)
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hg.abs hlim

end Critical2DKPZ.SHF.Flow

end
