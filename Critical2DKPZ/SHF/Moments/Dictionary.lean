/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Time and parameter scaling of collision kernels -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

/-- Dividing time by `B` and adding `log B` to the parameter multiplies the scalar density by `B`. -/
theorem scalarDensity_horizon_rescale (θ B t : ℝ) (hB : 0 < B) (ht : 0 < t) :
    B⁻¹ * DeltaBose.scalarDensity (θ + Real.log B) (t / B) =
      DeltaBose.scalarDensity θ t := by
  have hscale := DeltaBose.scalarDensity_scale θ hB (div_pos ht hB)
  have htime : B * (t / B) = t := by field_simp [ne_of_gt hB]
  rw [htime] at hscale
  calc
    B⁻¹ * DeltaBose.scalarDensity (θ + Real.log B) (t / B) =
        B⁻¹ * (B * DeltaBose.scalarDensity θ t) := by rw [← hscale]
    _ = DeltaBose.scalarDensity θ t := by field_simp [ne_of_gt hB]

/-- Two equal-time heat kernels factor into a relative-displacement density of variance `2t` and a center density of variance `t/2`. -/
theorem heatKernel_product_center_factorization {t : ℝ} (ht : 0 < t)
    (x₁ x₂ z : Plane) :
    heatKernel t (z - x₁) * heatKernel t (z - x₂) =
      heatKernel (2 * t) (x₂ - x₁) *
        heatKernel (t / 2) (z - (1 / 2 : ℝ) • (x₁ + x₂)) := by
  have hkernel := Critical2DKPZ.heatKernel_mul_sub ht ht (x₂ - x₁) (z - x₁)
  have harg : (x₂ - x₁) - (z - x₁) = x₂ - z := by abel
  rw [harg] at hkernel
  have hsum : t + t = 2 * t := by ring
  have hcoef : t / (t + t) = 1 / 2 := by rw [hsum]; field_simp [ne_of_gt ht]
  have hvar : t * t / (t + t) = t / 2 := by rw [hsum]; field_simp [ne_of_gt ht]
  have hcenter : z - x₁ - (1 / 2 : ℝ) • (x₂ - x₁) =
      z - (1 / 2 : ℝ) • (x₁ + x₂) := by module
  rw [hvar, hcoef, hcenter, hsum] at hkernel
  have hreverse : heatKernel t (x₂ - z) = heatKernel t (z - x₂) := by
    rw [show x₂ - z = -(z - x₂) by abel, Critical2DKPZ.heatKernel_neg]
  calc
    heatKernel t (z - x₁) * heatKernel t (z - x₂) =
        heatKernel t (z - x₁) * heatKernel t (x₂ - z) := by rw [← hreverse]
    _ = heatKernel (2 * t) (x₂ - x₁) *
        heatKernel (t / 2) (z - (1 / 2 : ℝ) • (x₁ + x₂)) := hkernel

end Critical2DKPZ.SHF.Moments

end
