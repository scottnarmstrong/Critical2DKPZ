/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Center and relative heat-kernel coordinates -/

@[expose] public section

open scoped RealInnerProductSpace

namespace Critical2DKPZ.SHF.Flow

/-- The product of two equal-time planar heat kernels factors into center and relative coordinates with the stated Jacobian and variances. -/
theorem heatKernel_pair_factor {t : ℝ} (ht : 0 < t) (x₀ x₁ z : Plane) :
    heatKernel t (z - x₀) * heatKernel t (z - x₁) =
      heatKernel (t / 2) (z - (1 / 2 : ℝ) • (x₀ + x₁)) *
        heatKernel (2 * t) (x₁ - x₀) := by
  have hx₀ : z - x₀ =
      (z - (1 / 2 : ℝ) • (x₀ + x₁)) + (1 / 2 : ℝ) • (x₁ - x₀) := by
    module
  have hx₁ : z - x₁ =
      (z - (1 / 2 : ℝ) • (x₀ + x₁)) - (1 / 2 : ℝ) • (x₁ - x₀) := by
    module
  have hhalf : ‖(1 / 2 : ℝ) • (x₁ - x₀)‖ ^ 2 = ‖x₁ - x₀‖ ^ 2 / 4 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
    ring
  have hnorm :
      ‖z - x₀‖ ^ 2 + ‖z - x₁‖ ^ 2 =
        2 * ‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 + ‖x₁ - x₀‖ ^ 2 / 2 := by
    have hplus := norm_add_sq_real (z - (1 / 2 : ℝ) • (x₀ + x₁))
      ((1 / 2 : ℝ) • (x₁ - x₀))
    have hminus := norm_sub_sq_real (z - (1 / 2 : ℝ) • (x₀ + x₁))
      ((1 / 2 : ℝ) • (x₁ - x₀))
    calc
      ‖z - x₀‖ ^ 2 + ‖z - x₁‖ ^ 2 =
          ‖(z - (1 / 2 : ℝ) • (x₀ + x₁)) + (1 / 2 : ℝ) • (x₁ - x₀)‖ ^ 2 +
            ‖(z - (1 / 2 : ℝ) • (x₀ + x₁)) - (1 / 2 : ℝ) • (x₁ - x₀)‖ ^ 2 := by
              rw [hx₀, hx₁]
      _ = 2 * ‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 +
          2 * ‖(1 / 2 : ℝ) • (x₁ - x₀)‖ ^ 2 := by
              rw [hplus, hminus]
              ring
      _ = 2 * ‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 + ‖x₁ - x₀‖ ^ 2 / 2 := by
              rw [hhalf]
              ring
  have hexp :
      -‖z - x₀‖ ^ 2 / (2 * t) + -‖z - x₁‖ ^ 2 / (2 * t) =
        -‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 / t - ‖x₁ - x₀‖ ^ 2 / (4 * t) := by
    rw [show -‖z - x₀‖ ^ 2 / (2 * t) + -‖z - x₁‖ ^ 2 / (2 * t) =
      -(‖z - x₀‖ ^ 2 + ‖z - x₁‖ ^ 2) / (2 * t) by ring, hnorm]
    field_simp [ht.ne']
    ring
  have hcoeff :
      (2 * Real.pi * t)⁻¹ * (2 * Real.pi * t)⁻¹ =
        (2 * Real.pi * (t / 2))⁻¹ * (2 * Real.pi * (2 * t))⁻¹ := by
    field_simp [ht.ne']
  rw [heatKernel, heatKernel, heatKernel, heatKernel]
  calc
    _ = ((2 * Real.pi * t)⁻¹ * (2 * Real.pi * t)⁻¹) *
        Real.exp (-‖z - x₀‖ ^ 2 / (2 * t) + -‖z - x₁‖ ^ 2 / (2 * t)) := by
          rw [Real.exp_add]
          ring
    _ = ((2 * Real.pi * (t / 2))⁻¹ * (2 * Real.pi * (2 * t))⁻¹) *
        Real.exp (-‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 / t -
          ‖x₁ - x₀‖ ^ 2 / (4 * t)) := by
          rw [hcoeff, hexp]
    _ = _ := by
      rw [show 2 * (t / 2) = t by ring,
        show 2 * (2 * t) = 4 * t by ring]
      rw [show -‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 / t -
          ‖x₁ - x₀‖ ^ 2 / (4 * t) =
          (-‖z - (1 / 2 : ℝ) • (x₀ + x₁)‖ ^ 2 / t) +
            (-‖x₁ - x₀‖ ^ 2 / (4 * t)) by ring,
        Real.exp_add]
      ring

end Critical2DKPZ.SHF.Flow

end
