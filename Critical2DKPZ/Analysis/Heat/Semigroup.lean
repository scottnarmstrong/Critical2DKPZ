/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Planar heat kernels satisfy Gaussian convolution and diffusive scaling identities. -/

public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Critical2DKPZ

/-- Completion of squares for two positive heat times. -/
theorem heatKernel_complete_square {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Plane) :
    ‖y‖ ^ 2 / (2 * s) + ‖x - y‖ ^ 2 / (2 * t) =
      ‖x‖ ^ 2 / (2 * (s + t)) +
        ‖y - (s / (s + t)) • x‖ ^ 2 / (2 * (s * t / (s + t))) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm x y]
  field_simp [hs.ne', ht.ne', (add_pos hs ht).ne']
  ring

/-- Product of two heat kernels as one heat kernel times a shifted normalized Gaussian. -/
theorem heatKernel_mul_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Plane) :
    heatKernel s y * heatKernel t (x - y) =
      heatKernel (s + t) x * heatKernel (s * t / (s + t))
        (y - (s / (s + t)) • x) := by
  have hc : (2 * Real.pi * s)⁻¹ * (2 * Real.pi * t)⁻¹ =
      (2 * Real.pi * (s + t))⁻¹ * (2 * Real.pi * (s * t / (s + t)))⁻¹ := by
    field_simp
  have he : -‖y‖ ^ 2 / (2 * s) + -‖x - y‖ ^ 2 / (2 * t) =
      -‖x‖ ^ 2 / (2 * (s + t)) +
        -‖y - (s / (s + t)) • x‖ ^ 2 / (2 * (s * t / (s + t))) := by
    simpa only [neg_div, ← neg_add] using congrArg Neg.neg (heatKernel_complete_square hs ht x y)
  simp only [heatKernel]
  calc
    _ = ((2 * Real.pi * s)⁻¹ * (2 * Real.pi * t)⁻¹) *
        Real.exp (-‖y‖ ^ 2 / (2 * s) + -‖x - y‖ ^ 2 / (2 * t)) := by
      rw [Real.exp_add]
      ring
    _ = ((2 * Real.pi * (s + t))⁻¹ * (2 * Real.pi * (s * t / (s + t)))⁻¹) *
        Real.exp (-‖x‖ ^ 2 / (2 * (s + t)) +
          -‖y - (s / (s + t)) • x‖ ^ 2 / (2 * (s * t / (s + t)))) := by rw [hc, he]
    _ = _ := by rw [Real.exp_add]; ring

/-- Translation does not change the mass of the heat kernel. -/
theorem integral_heatKernel_sub {u : ℝ} (hu : 0 < u) (a : Plane) :
    ∫ y : Plane, heatKernel u (y - a) = 1 := by
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self (heatKernel u) (-a)).trans (integral_heatKernel hu)

/-- Convolution of two positive-time planar heat kernels gives the heat kernel at the sum of the times. -/
theorem integral_heatKernel_mul_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Plane) :
    ∫ y : Plane, heatKernel s y * heatKernel t (x - y) = heatKernel (s + t) x := by
  simp_rw [heatKernel_mul_sub hs ht]
  rw [integral_const_mul, integral_heatKernel_sub (div_pos (mul_pos hs ht) (add_pos hs ht)),
    mul_one]

/-- Diffusive scaling, with the two-dimensional prefactor. -/
theorem heatKernel_scaling {a u : ℝ} (ha : 0 < a) (x : Plane) :
    heatKernel (a ^ 2 * u) (a • x) = (a ^ 2)⁻¹ * heatKernel u x := by
  have he : -(‖a • x‖ ^ 2) / (2 * (a ^ 2 * u)) = -‖x‖ ^ 2 / (2 * u) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
  rw [heatKernel, he, heatKernel]
  rw [show (2 * Real.pi * (a ^ 2 * u))⁻¹ =
    (a ^ 2)⁻¹ * (2 * Real.pi * u)⁻¹ by rw [← mul_inv]; congr 1; ring]
  ring

end Critical2DKPZ

end
