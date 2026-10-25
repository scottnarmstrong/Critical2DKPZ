/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelScaling
public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib.Tactic

/-! # Positive time comparison for the conjugated diagram chain -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The scalar collision density increases with its parameter. The real
integrals in this comparison are integrable by `integrableOn_gammaLaplaceIntegrand`. -/
theorem scalarDensity_mono_parameter {θ θ' t : ℝ} (hθ : θ ≤ θ') (ht : 0 < t) :
    scalarDensity θ t ≤ scalarDensity θ' t := by
  rw [scalarDensity_eq_laplace θ ht, scalarDensity_eq_laplace θ' ht]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
  apply integral_mono_ae (integrableOn_gammaLaplaceIntegrand _)
    (integrableOn_gammaLaplaceIntegrand _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  unfold gammaLaplaceIntegrand
  exact div_le_div_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (add_le_add hθ le_rfl) hu.le))
    (Real.Gamma_pos_of_pos hu).le

/-- Increasing time by a factor at least one decreases the collision
density by at most the reciprocal of that factor. -/
theorem scalarDensity_le_time_dilate (θ : ℝ) {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t) :
    scalarDensity θ t ≤ a * scalarDensity θ (a * t) := by
  rw [scalarDensity_scale θ (lt_of_lt_of_le zero_lt_one ha) ht]
  exact scalarDensity_mono_parameter (le_add_of_nonneg_right (Real.log_nonneg ha)) ht

/-- At a fixed spatial displacement, increasing time costs only the
planar heat-kernel normalization factor. -/
theorem heatKernel_le_time_dilate {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t) (x : Plane) :
    heatKernel t x ≤ a * heatKernel (a * t) x := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hden : 0 < 2 * t := by positivity
  have hden' : 0 < 2 * (a * t) := by positivity
  have htime : 2 * t ≤ 2 * (a * t) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht.le ha) (by norm_num)
  have hi : (2 * (a * t))⁻¹ ≤ (2 * t)⁻¹ := (inv_le_inv₀ hden' hden).mpr htime
  have hexp : -‖x‖ ^ 2 / (2 * t) ≤ -‖x‖ ^ 2 / (2 * (a * t)) := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonpos_left hi (neg_nonpos.mpr (sq_nonneg ‖x‖))
  have hcoef : a * (2 * Real.pi * (a * t))⁻¹ = (2 * Real.pi * t)⁻¹ := by
    field_simp
  unfold heatKernel
  calc
    _ ≤ (2 * Real.pi * t)⁻¹ * Real.exp (-‖x‖ ^ 2 / (2 * (a * t))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = (a * (2 * Real.pi * (a * t))⁻¹) * Real.exp (-‖x‖ ^ 2 / (2 * (a * t))) :=
      congrArg (fun q : ℝ => q * Real.exp (-‖x‖ ^ 2 / (2 * (a * t)))) hcoef.symm
    _ = _ := mul_assoc _ _ _

end Critical2DKPZ.SHF.Tsai

end
