/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SquareTailScaling
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTailControl
import Mathlib.Tactic

/-! # Scaling and monotonicity of the Gaussian truncated square -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit



/-- The standard Gaussian square-tail function vanishes at infinity. -/
theorem gaussian_squareTail_tendsto_zero :
    Tendsto (fun q : ℝ => ∫ y : ℝ, squareTail q y ∂gaussianReal 0 1) atTop (𝓝 0) :=
  gaussian_square_tail_tendsto 1

/-- Scaling a centered Gaussian gives the exact window variance factor. -/
theorem gaussian_squareTail_scaling {v : ℝ} (hv : 0 < v) (q : ℝ) :
    (∫ y : ℝ, squareTail q y ∂gaussianReal 0 (Real.toNNReal v)) =
      v * (∫ y : ℝ, squareTail (q / Real.sqrt v) y ∂gaussianReal 0 1) := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt v * y) =
      gaussianReal 0 (Real.toNNReal v) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply NNReal.coe_injective
    change Real.sqrt v ^ 2 = ((Real.toNNReal v : ℝ≥0) : ℝ)
    rw [Real.sq_sqrt hv.le, Real.toNNReal_of_nonneg hv.le]
    rfl
  rw [← hmap, integral_map (by fun_prop : AEMeasurable (fun y : ℝ => Real.sqrt v * y) (gaussianReal 0 1))
    (measurable_squareTail q).aestronglyMeasurable]
  have hpoint (y : ℝ) : squareTail q (Real.sqrt v * y) = v * squareTail (q / Real.sqrt v) y := by
    have hq : q = Real.sqrt v * (q / Real.sqrt v) := by field_simp
    conv_lhs => rw [hq]
    rw [squareTail_mul_pos hs, Real.sq_sqrt hv.le]
  simp_rw [hpoint]
  rw [integral_const_mul]

end Critical2DKPZ.Extensions.ScaleLimit
