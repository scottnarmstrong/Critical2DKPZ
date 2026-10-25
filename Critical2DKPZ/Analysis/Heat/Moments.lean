/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian domination, moments and tails

Explicit constants for the covariance-`u I` planar Gaussian. The even moment of order `2m`
is bounded by `2 m! (4u)^m`, and every natural-order moment is integrable.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ

/-- Split the Gaussian exponential into two equal halves. -/
theorem heatKernel_eq_doubled {u : ℝ} (hu : 0 < u) (x : Plane) :
    heatKernel u x = 2 * Real.exp (-‖x‖ ^ 2 / (4 * u)) * heatKernel (2 * u) x := by
  have hc : (2 * Real.pi * u)⁻¹ = 2 * (2 * Real.pi * (2 * u))⁻¹ := by field_simp
  have he : -‖x‖ ^ 2 / (2 * u) =
      -‖x‖ ^ 2 / (4 * u) + -‖x‖ ^ 2 / (2 * (2 * u)) := by ring
  simp only [heatKernel]
  rw [hc, he, Real.exp_add]
  ring

/-- A polynomial can be absorbed into half of the Gaussian decay. -/
theorem pow_mul_exp_neg_le_factorial (m : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    w ^ m * Real.exp (-w) ≤ (m.factorial : ℝ) := by
  have hf : (0 : ℝ) < m.factorial := by positivity
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp w hw m)
  have h := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-w)).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, neg_add_cancel, Real.exp_zero, mul_one,
    mul_comm (Real.exp w)] using h

/-- Pointwise domination by a Gaussian with twice the variance. -/
theorem norm_pow_mul_heatKernel_le {u : ℝ} (hu : 0 < u) (m : ℕ) (x : Plane) :
    ‖x‖ ^ (2 * m) * heatKernel u x ≤
      (2 * (m.factorial : ℝ) * (4 * u) ^ m) * heatKernel (2 * u) x := by
  have hp := pow_mul_exp_neg_le_factorial m (show 0 ≤ ‖x‖ ^ 2 / (4 * u) by positivity)
  have he : ‖x‖ ^ (2 * m) = (4 * u) ^ m * (‖x‖ ^ 2 / (4 * u)) ^ m := by
    rw [← mul_pow, mul_div_cancel₀ _ (by positivity : 4 * u ≠ 0), pow_mul]
  have hpoly : ‖x‖ ^ (2 * m) * Real.exp (-‖x‖ ^ 2 / (4 * u)) ≤
      (m.factorial : ℝ) * (4 * u) ^ m := by
    rw [he, mul_assoc, neg_div]
    exact (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (4 * u) ^ m)).trans_eq (mul_comm _ _)
  calc
    _ = (‖x‖ ^ (2 * m) * Real.exp (-‖x‖ ^ 2 / (4 * u))) *
        (2 * heatKernel (2 * u) x) := by rw [heatKernel_eq_doubled hu]; ring
    _ ≤ ((m.factorial : ℝ) * (4 * u) ^ m) * (2 * heatKernel (2 * u) x) :=
      mul_le_mul_of_nonneg_right hpoly (mul_nonneg (by norm_num) (heatKernel_nonneg (mul_pos two_pos hu).le x))
    _ = _ := by ring

/-- Every even spatial moment of the heat kernel is integrable at positive time. -/
theorem integrable_norm_pow_mul_heatKernel_even {u : ℝ} (hu : 0 < u) (m : ℕ) :
    Integrable (fun x : Plane => ‖x‖ ^ (2 * m) * heatKernel u x) := by
  apply ((integrable_heatKernel (mul_pos two_pos hu)).const_mul
    (2 * (m.factorial : ℝ) * (4 * u) ^ m)).mono'
  · exact ((continuous_norm.pow _).mul (continuous_heatKernel u)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
      (heatKernel_nonneg hu.le x))]
    exact norm_pow_mul_heatKernel_le hu m x

/-- Even spatial heat-kernel moments satisfy a factorial upper bound. -/
theorem integral_norm_pow_mul_heatKernel_even_le {u : ℝ} (hu : 0 < u) (m : ℕ) :
    ∫ x : Plane, ‖x‖ ^ (2 * m) * heatKernel u x ≤ 2 * (m.factorial : ℝ) * (4 * u) ^ m := by
  have h := integral_mono (integrable_norm_pow_mul_heatKernel_even hu m)
    ((integrable_heatKernel (mul_pos two_pos hu)).const_mul
      (2 * (m.factorial : ℝ) * (4 * u) ^ m)) (norm_pow_mul_heatKernel_le hu m)
  simpa only [integral_const_mul, integral_heatKernel (mul_pos two_pos hu), mul_one] using h

/-- All polynomial moments of a positive-time heat kernel are finite. -/
theorem integrable_norm_pow_mul_heatKernel {u : ℝ} (hu : 0 < u) (m : ℕ) :
    Integrable (fun x : Plane => ‖x‖ ^ m * heatKernel u x) := by
  apply ((integrable_heatKernel hu).add (integrable_norm_pow_mul_heatKernel_even hu m)).mono'
  · exact ((continuous_norm.pow _).mul (continuous_heatKernel u)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _)
      (heatKernel_nonneg hu.le x))]
    have hp : ‖x‖ ^ m ≤ 1 + ‖x‖ ^ (2 * m) := by
      by_cases hx : ‖x‖ ≤ 1
      · exact (pow_le_one₀ (norm_nonneg _) hx).trans (le_add_of_nonneg_right (by positivity))
      · exact (pow_le_pow_right₀ (le_of_not_ge hx) (by omega : m ≤ 2 * m)).trans
          (le_add_of_nonneg_left zero_le_one)
    simpa only [Pi.add_apply, add_mul, one_mul] using mul_le_mul_of_nonneg_right hp (heatKernel_nonneg hu.le x)

/-- Exponential pointwise tail domination at any nonnegative radius. -/
theorem heatKernel_le_tail {u R : ℝ} (hu : 0 < u) (hR : 0 ≤ R) {x : Plane}
    (hx : R ≤ ‖x‖) :
    heatKernel u x ≤ (2 * Real.exp (-R ^ 2 / (4 * u))) * heatKernel (2 * u) x := by
  rw [heatKernel_eq_doubled hu]
  have he : Real.exp (-‖x‖ ^ 2 / (4 * u)) ≤ Real.exp (-R ^ 2 / (4 * u)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (neg_le_neg ((sq_le_sq₀ hR (norm_nonneg _)).mpr hx)) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
    (heatKernel_nonneg (mul_pos two_pos hu).le x)

/-- The planar heat kernel has mass at most `2 * exp (-R² / (4u))` outside the ball of radius `R` at positive time `u`. -/
theorem integral_heatKernel_tail_le {u R : ℝ} (hu : 0 < u) (hR : 0 ≤ R) :
    ∫ x : Plane in {x | R ≤ ‖x‖}, heatKernel u x ≤ 2 * Real.exp (-R ^ 2 / (4 * u)) := by
  let A : Set Plane := {x | R ≤ ‖x‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet
  have hc : 0 ≤ 2 * Real.exp (-R ^ 2 / (4 * u)) := by positivity
  calc
    _ ≤ ∫ x in A, (2 * Real.exp (-R ^ 2 / (4 * u))) * heatKernel (2 * u) x :=
      setIntegral_mono_on (integrable_heatKernel hu).integrableOn
        ((integrable_heatKernel (mul_pos two_pos hu)).const_mul _).integrableOn hA
        (fun _ hx => heatKernel_le_tail hu hR hx)
    _ = (2 * Real.exp (-R ^ 2 / (4 * u))) * ∫ x in A, heatKernel (2 * u) x := integral_const_mul _ _
    _ ≤ (2 * Real.exp (-R ^ 2 / (4 * u))) * ∫ x : Plane, heatKernel (2 * u) x :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral
        (integrable_heatKernel (mul_pos two_pos hu))
        (Filter.Eventually.of_forall (heatKernel_nonneg (mul_pos two_pos hu).le))) hc
    _ = _ := by rw [integral_heatKernel (mul_pos two_pos hu), mul_one]

end Critical2DKPZ

end
