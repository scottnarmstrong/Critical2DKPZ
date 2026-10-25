/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzTranslate
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzSpectralLp
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Translation of the angular Fourier transform -/

public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Spatial translation multiplies the angular Fourier transform by its unit phase. -/
theorem fourierKPZ_translateSchwartz (z : Plane) (f : SchwartzMap Plane ℝ) (ξ : Plane) :
    Spectral.fourierKPZ (translateSchwartz z f) ξ =
      Complex.exp (-(Complex.I * (inner ℝ z ξ : ℝ))) * Spectral.fourierKPZ f ξ := by
  unfold Spectral.fourierKPZ
  calc
    _ = ∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ (x + z) ξ : ℝ))) * (f x : ℂ) := by
      simpa only [translateSchwartz_apply, add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x : Plane =>
          Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * (f (x - z) : ℂ)) z).symm
    _ = ∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ z ξ : ℝ))) *
        (Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * (f x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have h : -(Complex.I * (inner ℝ (x + z) ξ : ℝ)) =
          -(Complex.I * (inner ℝ z ξ : ℝ)) + -(Complex.I * (inner ℝ x ξ : ℝ)) := by
        rw [inner_add_left, Complex.ofReal_add]
        ring
      rw [h, Complex.exp_add, mul_assoc]
    _ = _ := integral_const_mul _ _

/-- The phase multiplier for translation has norm one. -/
theorem norm_translation_phase (z ξ : Plane) :
    ‖Complex.exp (-(Complex.I * (inner ℝ z ξ : ℝ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

end Critical2DKPZ.Extensions.ScaleLimit
