/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The planar heat kernel has covariance `u I`, is nonnegative, and has unit mass at positive times. -/

public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ

/-- The heat-kernel density vanishes at time zero. -/
@[simp] theorem heatKernel_zero_time (x : Plane) : heatKernel 0 x = 0 := by
  simp only [heatKernel, mul_zero, inv_zero, zero_mul]

/-- The planar heat kernel is invariant under spatial reflection. -/
@[simp] theorem heatKernel_neg (u : ℝ) (x : Plane) : heatKernel u (-x) = heatKernel u x := by
  simp only [heatKernel, norm_neg]

/-- The planar heat kernel is strictly positive at positive times. -/
theorem heatKernel_pos {u : ℝ} (hu : 0 < u) (x : Plane) : 0 < heatKernel u x :=
  mul_pos (inv_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hu)) (Real.exp_pos _)

/-- The planar heat kernel is nonnegative at nonnegative times. -/
theorem heatKernel_nonneg {u : ℝ} (hu : 0 ≤ u) (x : Plane) : 0 ≤ heatKernel u x := by
  rcases hu.eq_or_lt with h | h
  · rw [← h, heatKernel_zero_time]
  · exact (heatKernel_pos h x).le

/-- The heat-kernel value at the origin is the reciprocal of twice pi times time. -/
@[simp] theorem heatKernel_at_zero (u : ℝ) : heatKernel u 0 = (2 * Real.pi * u)⁻¹ := by
  simp only [heatKernel, norm_zero, zero_pow (by decide : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one]

/-- The heat kernel at nonnegative time is bounded by its value at the origin. -/
theorem heatKernel_le_at_zero {u : ℝ} (hu : 0 ≤ u) (x : Plane) :
    heatKernel u x ≤ (2 * Real.pi * u)⁻¹ := by
  have he : Real.exp (-‖x‖ ^ 2 / (2 * u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (mul_nonneg (by norm_num) hu))
  exact mul_le_of_le_one_right (inv_nonneg.mpr (mul_nonneg (mul_nonneg (by norm_num)
    Real.pi_pos.le) hu)) he

/-- The heat kernel is continuous in its spatial argument. -/
theorem continuous_heatKernel (u : ℝ) : Continuous (heatKernel u) := by
  unfold heatKernel
  fun_prop

/-- The heat kernel is measurable in its spatial argument. -/
theorem measurable_heatKernel (u : ℝ) : Measurable (heatKernel u) :=
  (continuous_heatKernel u).measurable

/-- At positive time the heat kernel is a Gaussian function of the spatial norm. -/
theorem heatKernel_eq_exp (u : ℝ) (x : Plane) :
    heatKernel u x = (2 * Real.pi * u)⁻¹ * Real.exp (-((2 * u)⁻¹) * ‖x‖ ^ 2) := by
  rw [heatKernel]
  congr 2
  ring

/-- The heat kernel is integrable at every positive time. -/
theorem integrable_heatKernel {u : ℝ} (hu : 0 < u) : Integrable (heatKernel u) := by
  have hb : 0 < (((2 * u)⁻¹ : ℝ) : ℂ).re := by
    simpa only [Complex.ofReal_re] using inv_pos.mpr (mul_pos (by norm_num) hu)
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : Plane)).re
  have hr : Integrable (fun x : Plane => Real.exp (-((2 * u)⁻¹) * ‖x‖ ^ 2)) := by
    simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_neg, RCLike.re_eq_complex_re, Complex.exp_ofReal_re] using hg
  change Integrable (fun x : Plane => heatKernel u x)
  simp_rw [heatKernel_eq_exp]
  exact hr.const_mul ((2 * Real.pi * u)⁻¹)

/-- The kernel has mass one for every positive heat time. -/
theorem integral_heatKernel {u : ℝ} (hu : 0 < u) : ∫ x : Plane, heatKernel u x = 1 := by
  simp_rw [heatKernel_eq_exp]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm
    (inv_pos.mpr (mul_pos (by norm_num) hu))]
  have hd : Module.finrank ℝ Plane = 2 := by simp only [Plane, finrank_euclideanSpace,
    Fintype.card_fin]
  rw [hd]
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  field_simp

end Critical2DKPZ

end
