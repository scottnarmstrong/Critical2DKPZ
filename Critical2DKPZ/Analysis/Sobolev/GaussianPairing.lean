/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.AngularFourier
public import Critical2DKPZ.Analysis.Heat.InverseFourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Heat smoothing from the angular Fourier integral

The Fourier interchange is justified separately at each positive heat time using the integrable
majorant `exp(-u|ξ|²) |f(y)|`. No integrability in heat time near zero is presumed.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Critical2DKPZ

open Analysis.Sobolev

/-- The planar Gaussian Fourier multiplier is integrable for every positive heat time. -/
theorem integrable_gaussian_multiplier {u : ℝ} (hu : 0 < u) :
    Integrable (fun ξ : Plane => Real.exp (-u * ‖ξ‖ ^ 2)) := by
  have hb : 0 < (u : ℂ).re := hu
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : Plane)).re
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, RCLike.re_eq_complex_re, Complex.exp_ofReal_re] using hg

/-- The Fourier and spatial integrals at fixed positive heat time have an integrable product majorant. -/
theorem integrable_gaussian_pairing {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) (x : Plane) :
    Integrable (fun p : Plane × Plane =>
      Complex.exp ((inner ℝ p.1 (x - p.2) : ℝ) * Complex.I) *
        ((Real.exp (-u * ‖p.1‖ ^ 2) : ℂ) * (f p.2 : ℂ))) (volume.prod volume) := by
  have hb := ((integrable_gaussian_multiplier hu).ofReal (𝕜 := ℂ)).mul_prod
    (hf.ofReal (𝕜 := ℂ))
  have hc : Continuous (fun p : Plane × Plane =>
      Complex.exp ((inner ℝ p.1 (x - p.2) : ℝ) * Complex.I)) := by fun_prop
  apply hb.mono (hc.aestronglyMeasurable.mul hb.aestronglyMeasurable)
  filter_upwards [] with p
  simp only [Pi.mul_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- Inverting the Gaussian Fourier multiplier against an L¹ function gives its heat convolution. -/
theorem integral_gaussian_angularFourier {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) (x : Plane) :
    (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) *
      (∫ ξ : Plane, (Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) *
        Complex.exp ((inner ℝ ξ x : ℝ) * Complex.I) * angularFourierIntegral f ξ) =
      ∫ y : Plane, (heatKernel (2 * u) (x - y) : ℂ) * (f y : ℂ) := by
  let G : Plane → Plane → ℂ := fun ξ y =>
    Complex.exp ((inner ℝ ξ (x - y) : ℝ) * Complex.I) *
      ((Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) * (f y : ℂ))
  have he (ξ : Plane) : (Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) *
      Complex.exp ((inner ℝ ξ x : ℝ) * Complex.I) * angularFourierIntegral f ξ =
        ∫ y : Plane, G ξ y := by
    rw [angularFourierIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [G]
    have hp : Complex.exp ((inner ℝ ξ x : ℝ) * Complex.I) *
        Complex.exp ((-inner ℝ ξ y : ℝ) * Complex.I) =
        Complex.exp ((inner ℝ ξ (x - y) : ℝ) * Complex.I) := by
      rw [← Complex.exp_add, inner_sub_right]
      congr 1
      push_cast
      ring
    calc
      _ = (Complex.exp ((inner ℝ ξ x : ℝ) * Complex.I) *
          Complex.exp ((-inner ℝ ξ y : ℝ) * Complex.I)) *
            ((Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) * (f y : ℂ)) := by ring
      _ = _ := by rw [hp]
  simp_rw [he]
  rw [integral_integral_swap (integrable_gaussian_pairing hu hf x), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [show (∫ ξ : Plane, G ξ y) =
      (∫ ξ : Plane, Complex.exp ((-u * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ ξ (x - y) : ℂ))) * (f y : ℂ) by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [G]
    rw [Complex.ofReal_exp, mul_comm Complex.I _]
    ring]
  rw [← mul_assoc, integral_gaussian_mul_cexp hu]

end Critical2DKPZ

end
