/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Critical2DKPZ.Extensions.ScaleLimit.DensityIntegration
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Integrability of the planar logarithmic singularity

The positive logarithm is bounded by the inverse radius. This is locally
integrable in dimension two and supplies the moving-diagonal domination.
-/

public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The positive logarithmic singularity is dominated by the inverse radius. -/
theorem posLog_inv_norm_le_inv_norm (z : Plane) :
    max 0 (Real.log ‖z‖⁻¹) ≤ ‖z‖⁻¹ :=
  max_le (inv_nonneg.mpr (norm_nonneg _))
    (Real.log_le_self (inv_nonneg.mpr (norm_nonneg _)))

/-- The planar positive logarithm is integrable on every bounded ball. -/
theorem integrableOn_posLog_inv_norm_ball (R : ℝ) :
    IntegrableOn (fun z : Plane => max 0 (Real.log ‖z‖⁻¹))
      (Metric.ball 0 R) volume := by
  apply integrableOn_ball_of_norm_le_rpow
    (by norm_num [Plane] : 1 ≤ Module.finrank ℝ Plane)
    (by norm_num [Plane] : (1 : ℝ) < Module.finrank ℝ Plane)
    (C := 1) (α := 1)
  · filter_upwards [] with z
    rw [Real.rpow_neg_one, one_mul, Real.norm_of_nonneg (le_max_left _ _)]
    exact posLog_inv_norm_le_inv_norm z
  · exact (measurable_const.max (Real.measurable_log.comp (continuous_norm.measurable.inv))).aestronglyMeasurable

/-- The logarithmic singularity is integrable uniformly in the relative width. -/
theorem exists_sup_integral_posLog (φ ψ : TestFn) (hψ : ∀ v, 0 ≤ ψ v) :
    ∃ M : ℝ, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun p : Plane × Plane =>
        φ p.1 * ψ p.2 * max 0 (Real.log ‖p.1 - ρ • p.2‖⁻¹)) (volume.prod volume) ∧
      (∫ u, ∫ v, φ u * ψ v * max 0 (Real.log ‖u - ρ • v‖⁻¹)) ≤ M := by
  obtain ⟨K, _hK, hs⟩ := exists_subDensity_support_radius φ ψ
  let F : Plane → ℝ := fun w => max 0 (Real.log ‖w‖⁻¹)
  let A : ℝ := ‖(φ : Plane →ᵇ ℝ)‖ * (∫ v, ψ v)
  let R : ℝ := K + 1
  have hFloc : ∀ r : ℝ, 0 < r → IntegrableOn F (Metric.ball 0 r) volume :=
    fun r _ => integrableOn_posLog_inv_norm_ball r
  have hcut : Integrable ((Metric.ball (0 : Plane) R).indicator F) :=
    (integrableOn_posLog_inv_norm_ball R).integrable_indicator measurableSet_ball
  let M : ℝ := A * (∫ w in Metric.ball (0 : Plane) R, F w)
  refine ⟨M, ?_⟩
  intro ρ hρ
  refine ⟨integrable_difference_kernel_product φ ψ hρ F hFloc, ?_⟩
  have hp := integrable_subDensity_kernel_product φ ψ hρ F hFloc
  have hi : Integrable (fun w => subDensity φ ψ ρ w * F w) := by
    simpa only [subDensity, integral_mul_const] using hp.integral_prod_left
  have hb (w : Plane) : subDensity φ ψ ρ w * F w ≤
      A * (Metric.ball (0 : Plane) R).indicator F w := by
    by_cases hw : w ∈ Metric.ball (0 : Plane) R
    · rw [Set.indicator_of_mem hw]
      exact mul_le_mul_of_nonneg_right (density_sub_bound φ ψ hψ ρ w) (le_max_left _ _)
    · have hnorm : K < ‖w‖ := by
        have hh : K + 1 ≤ ‖w‖ := by
          simpa only [Metric.mem_ball, dist_zero_right, R, not_lt] using hw
        exact (lt_add_one K).trans_le hh
      rw [hs ρ hρ w hnorm, Set.indicator_of_notMem hw, zero_mul, mul_zero]
  calc
    _ = ∫ w, subDensity φ ψ ρ w * F w := (integral_subDensity_mul φ ψ hρ F hFloc).symm
    _ ≤ ∫ w, A * (Metric.ball (0 : Plane) R).indicator F w :=
      integral_mono hi (hcut.const_mul A) hb
    _ = M := by rw [integral_const_mul, integral_indicator measurableSet_ball]

end Critical2DKPZ.Extensions.ScaleLimit
