/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandKernelFourier
import Mathlib.Tactic

/-! # Angular Fourier scaling of the normalized band kernel -/

public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Scaling a real planar function transforms its angular frequency inversely. -/
theorem fourierKPZ_inv_smul (f : Plane → ℝ) (a : ℝ) (ha : 0 < a) (ξ : Plane) :
    Spectral.fourierKPZ (fun x => f (a⁻¹ • x)) ξ =
      (a ^ 2 : ℝ) * Spectral.fourierKPZ f (a • ξ) := by
  let G : Plane → ℂ := fun y => Complex.exp (-(Complex.I * (inner ℝ y (a • ξ) : ℂ))) * (f y : ℂ)
  have hchange := Measure.integral_comp_inv_smul (μ := volume) G a
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  simp only [hdim, abs_of_pos (pow_pos ha 2), Complex.real_smul] at hchange
  unfold Spectral.fourierKPZ
  have hleft : (∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ))) *
      (f (a⁻¹ • x) : ℂ)) = ∫ x : Plane, G (a⁻¹ • x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [G, inner_smul_left, inner_smul_right, ha.ne']
  rw [hleft, hchange]

/-- Exact Fourier multiplier of the normalized band kernel. -/
theorem fourierKPZ_zetaScaled_zero (a : ℝ) (ha : 0 < a) (ξ : Plane) :
    Spectral.fourierKPZ (zetaScaled a 0) ξ = (chi (a • ξ) : ℂ) := by
  have heq : (zetaScaled a 0 : Plane → ℝ) = fun x => a⁻¹ ^ 2 * zeta (a⁻¹ • x) := by
    funext x
    simp
  rw [heq, Spectral.fourierKPZ]
  simp_rw [Complex.ofReal_mul, mul_left_comm _ ((a⁻¹ ^ 2 : ℝ) : ℂ)]
  rw [integral_const_mul]
  change ((a⁻¹ ^ 2 : ℝ) : ℂ) * Spectral.fourierKPZ (fun x => zeta (a⁻¹ • x)) ξ = _
  rw [fourierKPZ_inv_smul zeta a ha, fourierKPZ_zeta]
  push_cast
  field_simp [ha.ne']

/-- The band multiplier at any center includes exactly its angular translation phase. -/
theorem fourierKPZ_zetaScaled (a : ℝ) (ha : 0 < a) (y ξ : Plane) :
    Spectral.fourierKPZ (zetaScaled a y) ξ =
      Complex.exp (-(Complex.I * (inner ℝ y ξ : ℂ))) * (chi (a • ξ) : ℂ) := by
  rw [zetaScaled_eq_translate a y, fourierKPZ_translate, fourierKPZ_zetaScaled_zero a ha]

end Critical2DKPZ.Extensions.ScaleLimit
