/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.GaussianSquareTails
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Vanishing square tails and eventual uniform integrability -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Cutting off a square above a radius does not increase its norm. -/
theorem norm_square_tail_le (c y : ℝ) :
    ‖y ^ 2 * Set.indicator {z : ℝ | c < |z|} (fun _ : ℝ => (1 : ℝ)) y‖ ≤ y ^ 2 := by
  by_cases hy : y ∈ {z : ℝ | c < |z|}
  · rw [Set.indicator_of_mem hy, mul_one, Real.norm_of_nonneg (sq_nonneg _)]
  · rw [Set.indicator_of_notMem hy, mul_zero, norm_zero]
    exact sq_nonneg y

/-- Integrable square moments have vanishing tail moments at large radii. -/
theorem integrable_square_tail_tendsto (μ : Measure ℝ)
    (hμ : Integrable (fun y : ℝ => y ^ 2) μ) :
    Tendsto (fun c : ℝ => ∫ y : ℝ, y ^ 2 * Set.indicator {z : ℝ | c < |z|}
      (fun _ : ℝ => (1 : ℝ)) y ∂μ) atTop (𝓝 0) := by
  have hmeas (c : ℝ) : AEStronglyMeasurable (fun y : ℝ => y ^ 2 *
      Set.indicator {z : ℝ | c < |z|} (fun _ : ℝ => (1 : ℝ)) y) μ := by
    have hA : MeasurableSet {z : ℝ | c < |z|} := by
      simpa only [Real.norm_eq_abs] using
        (isOpen_lt continuous_const (continuous_norm : Continuous (fun z : ℝ => ‖z‖))).measurableSet
    exact ((measurable_id.pow_const 2).mul
      ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator hA)).aestronglyMeasurable
  have hlim (y : ℝ) : Tendsto (fun c : ℝ => y ^ 2 * Set.indicator {z : ℝ | c < |z|}
      (fun _ : ℝ => (1 : ℝ)) y) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop |y|] with c hc
    rw [Set.indicator_of_notMem (show y ∉ {z : ℝ | c < |z|} from not_lt_of_ge hc), mul_zero]
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => y ^ 2)
      (Eventually.of_forall hmeas)
      (Eventually.of_forall fun c => Eventually.of_forall (norm_square_tail_le c)) hμ
      (Eventually.of_forall hlim)

/-- The square tails of a centred Gaussian vanish at infinity. -/
theorem gaussian_square_tail_tendsto (v : ℝ≥0) :
    Tendsto (fun c : ℝ => ∫ y : ℝ, y ^ 2 * Set.indicator {z : ℝ | c < |z|}
      (fun _ : ℝ => (1 : ℝ)) y ∂gaussianReal 0 v) atTop (𝓝 0) :=
  integrable_square_tail_tendsto _ (memLp_id_gaussianReal 2).integrable_sq


end Critical2DKPZ.Extensions.ScaleLimit
