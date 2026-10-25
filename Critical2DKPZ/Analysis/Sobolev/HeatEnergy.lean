/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.AngularFourierBasic
public import Critical2DKPZ.Analysis.Sobolev.GaussianPairing
import Mathlib.Tactic.Ring

/-!
# Heat-damped Fourier energy as a spatial quadratic form

The fixed positive time identity holds already for real L¹ functions. Its proof uses the uniform
Fourier bound and the product majorant established for Gaussian pairing.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

namespace Critical2DKPZ

open Analysis.Sobolev

/-- The Gaussian quadratic form, with all fixed-time interchanges justified by `L¹` bounds. -/
theorem integral_gaussian_fourier_energy_complex {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) :
    (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) *
      (∫ ξ : Plane, (Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral f ξ *
        conj (angularFourierIntegral f ξ)) =
      ∫ y : Plane, (f y : ℂ) *
        ∫ x : Plane, (heatKernel (2 * u) (y - x) : ℂ) * (f x : ℂ) := by
  let H : Plane → Plane → ℂ := fun ξ y =>
    Complex.exp ((inner ℝ ξ y : ℝ) * Complex.I) *
      ((Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) * (f y : ℂ)) * angularFourierIntegral f ξ
  have hb := ((integrable_gaussian_multiplier hu).ofReal (𝕜 := ℂ)).mul_prod
    (hf.ofReal (𝕜 := ℂ))
  have hphase : Continuous (fun p : Plane × Plane =>
      Complex.exp ((inner ℝ p.1 p.2 : ℝ) * Complex.I)) := by fun_prop
  have hF := continuous_angularFourierIntegral hf
  have hH : Integrable (Function.uncurry H) (volume.prod volume) := by
    apply (hb.norm.mul_const (∫ x : Plane, ‖f x‖)).mono'
      ((hphase.aestronglyMeasurable.mul hb.aestronglyMeasurable).mul
        (hF.comp continuous_fst).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖Complex.exp ((inner ℝ p.1 p.2 : ℝ) * Complex.I) *
      ((Real.exp (-u * ‖p.1‖ ^ 2) : ℂ) * (f p.2 : ℂ)) * angularFourierIntegral f p.1‖ ≤ _
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_left (norm_angularFourierIntegral_le f p.1)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have he (ξ : Plane) : (Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral f ξ *
      conj (angularFourierIntegral f ξ) = ∫ y : Plane, H ξ y := by
    rw [conj_angularFourierIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [H]
    ring
  simp_rw [he]
  rw [integral_integral_swap hH, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  have hi : (∫ ξ : Plane, H ξ y) = (f y : ℂ) *
      ∫ ξ : Plane, (Real.exp (-u * ‖ξ‖ ^ 2) : ℂ) *
        Complex.exp ((inner ℝ ξ y : ℝ) * Complex.I) * angularFourierIntegral f ξ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [H]
    ring
  rw [hi, mul_left_comm, integral_gaussian_angularFourier hu hf]

/-- Real spatial quadratic form for the heat-damped Fourier energy. -/
theorem integral_gaussian_fourier_energy {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) :
    ((2 * Real.pi)⁻¹ ^ 2) *
      (∫ ξ : Plane, Real.exp (-u * ‖ξ‖ ^ 2) * ‖angularFourierIntegral f ξ‖ ^ 2) =
      ∫ y : Plane, f y * ∫ x : Plane, heatKernel (2 * u) (y - x) * f x := by
  apply Complex.ofReal_injective
  simp_rw [Complex.ofReal_mul, ← integral_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_pow,
    ← Complex.mul_conj']
  simp_rw [← integral_complex_ofReal, Complex.ofReal_mul]
  simpa only [Complex.ofReal_pow, Complex.ofReal_inv, mul_assoc] using!
    integral_gaussian_fourier_energy_complex hu hf

/-- Integrability of the heat-damped Fourier energy at every strictly positive heat time. -/
theorem integrable_gaussian_fourier_energy {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) :
    Integrable (fun ξ : Plane => Real.exp (-u * ‖ξ‖ ^ 2) * ‖angularFourierIntegral f ξ‖ ^ 2) := by
  have hF := continuous_angularFourierIntegral hf
  have hc : Continuous (fun ξ : Plane =>
      Real.exp (-u * ‖ξ‖ ^ 2) * ‖angularFourierIntegral f ξ‖ ^ 2) := by fun_prop
  apply ((integrable_gaussian_multiplier hu).mul_const ((∫ x : Plane, ‖f x‖) ^ 2)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_angularFourierIntegral_le f ξ) 2)
    (Real.exp_nonneg _)

end Critical2DKPZ

end
