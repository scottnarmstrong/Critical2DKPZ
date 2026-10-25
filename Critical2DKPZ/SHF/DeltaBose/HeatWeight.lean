/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.Tactic

/-! The planar heat-kernel comparison used in Surendranath–Tsai’s weighted estimates holds with exponential factor `exp(2 a² t)` for every real weight `a`. -/

@[expose] public section

namespace Critical2DKPZ.DeltaBose

/-- The planar coordinate `ℓ¹` norm is the sum of the absolute coordinate values. -/
noncomputable def planeOneNorm (z : Plane) : ℝ := |z 0| + |z 1|

/-- The usual comparison of coordinate and Euclidean norms in dimension two. -/
theorem planeOneNorm_sq_le (z : Plane) : planeOneNorm z ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  rw [planeOneNorm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  nlinarith only [sq_nonneg (|z 0| - |z 1|), sq_abs (z 0), sq_abs (z 1)]

/-- The quadratic inequality obtained by completing the square in the exponential weight comparison. -/
theorem weight_exponent_le {a r s t : ℝ} (ht : 0 < t) (hrs : r ^ 2 ≤ 2 * s) :
    a * r - s / (4 * t) ≤ 2 * a ^ 2 * t := by
  have he : a * r - s / (4 * t) = (a * r * (4 * t) - s) / (4 * t) := by
    field_simp
  rw [he, div_le_iff₀ (by positivity)]
  nlinarith only [sq_nonneg (r - 4 * a * t), hrs]

/-- The heat-kernel comparison holds at positive time for every real exponential weight. -/
theorem heatKernel_mul_exp_oneNorm_le (a : ℝ) {t : ℝ} (ht : 0 < t) (z : Plane) :
    heatKernel t z * Real.exp (a * planeOneNorm z) ≤
      2 * Real.exp (2 * a ^ 2 * t) * heatKernel (2 * t) z := by
  have h := weight_exponent_le (a := a) ht (planeOneNorm_sq_le z)
  have he : -‖z‖ ^ 2 / (2 * t) + a * planeOneNorm z ≤
      2 * a ^ 2 * t + -‖z‖ ^ 2 / (2 * (2 * t)) := by
    have hdiv : -‖z‖ ^ 2 / (2 * t) = -(‖z‖ ^ 2 / (4 * t)) - ‖z‖ ^ 2 / (4 * t) := by ring
    rw [hdiv]
    have hdiv' : -‖z‖ ^ 2 / (2 * (2 * t)) = -(‖z‖ ^ 2 / (4 * t)) := by ring
    rw [hdiv']
    linarith only [h]
  have hcoeff : (2 * Real.pi * t)⁻¹ = 2 * (2 * Real.pi * (2 * t))⁻¹ := by ring
  calc heatKernel t z * Real.exp (a * planeOneNorm z)
      = (2 * Real.pi * t)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * t) + a * planeOneNorm z) := by
        rw [heatKernel, Real.exp_add]
        ring
    _ ≤ (2 * Real.pi * t)⁻¹ * Real.exp (2 * a ^ 2 * t + -‖z‖ ^ 2 / (2 * (2 * t))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = 2 * Real.exp (2 * a ^ 2 * t) * heatKernel (2 * t) z := by
      rw [hcoeff, Real.exp_add, heatKernel]
      ring

end Critical2DKPZ.DeltaBose
