/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! In angular Fourier coordinates, the inverse transform of Gaussian damping is the planar heat kernel at twice the damping parameter. -/

public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Critical2DKPZ

/-- The inverse angular Fourier transform of Gaussian damping equals the planar heat kernel with normalization `(2π)⁻²`. -/
theorem integral_gaussian_mul_cexp {u : ℝ} (hu : 0 < u) (z : Plane) :
    (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) *
      (∫ ξ : Plane, Complex.exp ((-u * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ ξ z : ℂ))) = (heatKernel (2 * u) z : ℂ) := by
  have hb : 0 < (u : ℂ).re := hu
  have hi := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I z
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  simp only [hd, Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_one, Complex.I_sq] at hi
  have he : (fun ξ : Plane => Complex.exp ((-u * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (inner ℝ ξ z : ℂ))) =
      fun ξ => Complex.exp (-(u : ℂ) * (‖ξ‖ : ℂ) ^ 2 +
        Complex.I * (inner ℝ z ξ : ℂ)) := by
    funext ξ
    rw [← Complex.exp_add, real_inner_comm ξ z]
    push_cast
    rfl
  rw [he, hi, heatKernel_eq_exp, Complex.ofReal_mul, Complex.ofReal_exp]
  have hc : (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) * (Real.pi / (u : ℂ)) =
      (((2 * Real.pi * (2 * u))⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hx : (-1 : ℂ) * (‖z‖ : ℂ) ^ 2 / (4 * (u : ℂ)) =
      ((-((2 * (2 * u))⁻¹) * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← mul_assoc, hc, hx]

end Critical2DKPZ

end
