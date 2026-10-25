/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Plancherel
public import Critical2DKPZ.Analysis.Sobolev.Seminorm
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Angular and unitary Fourier coordinates differ by a `2π` change of variables, giving the planar Plancherel factor `(2π)⁻²`. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace Critical2DKPZ.Analysis.Sobolev

/-- Fourier integral with angular frequency, exactly `∫ f(x) exp(-i⟪ξ,x⟫) dx`. -/
def angularFourierIntegral (f : Plane → ℝ) (ξ : Plane) : ℂ :=
  ∫ x : Plane, Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ)

/-- The factor converting the angular-frequency convention to Mathlib's convention. -/
theorem angularFourierIntegral_eq_fourier (f : Plane → ℝ) (ξ : Plane) :
    angularFourierIntegral f ξ = 𝓕 (fun x => (f x : ℂ)) ((2 * Real.pi)⁻¹ • ξ) := by
  rw [angularFourierIntegral, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [real_inner_smul_right, smul_eq_mul]
  have he : -2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ x ξ) = -inner ℝ ξ x := by
    rw [real_inner_comm x ξ]
    field_simp
  rw [he]

/-- The real and imaginary parts of the angular Fourier integral are the cosine and negative sine integrals of an integrable real function. -/
theorem angularFourierIntegral_eq_cos_sin {f : Plane → ℝ} (hf : Integrable f) (ξ : Plane) :
    angularFourierIntegral f ξ =
      (∫ x, f x * Real.cos (inner ℝ ξ x) : ℝ) -
        Complex.I * (∫ x, f x * Real.sin (inner ℝ ξ x) : ℝ) := by
  have hc : Integrable (fun x : Plane => f x * Real.cos (inner ℝ ξ x)) :=
    hf.mul_bdd (Real.continuous_cos.comp (innerSL ℝ ξ).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable (fun x : Plane => f x * Real.sin (inner ℝ ξ x)) :=
    hf.mul_bdd (Real.continuous_sin.comp (innerSL ℝ ξ).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have he : (fun x : Plane => Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ)) =
      fun x => ((f x * Real.cos (inner ℝ ξ x) : ℝ) : ℂ) -
        Complex.I * ((f x * Real.sin (inner ℝ ξ x) : ℝ) : ℂ) := by
    funext x
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [angularFourierIntegral, he, integral_sub hc.ofReal (hs.ofReal.const_mul _),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

/-- The localized Fourier transform of a locally integrable function is its angular Fourier integral after multiplication by the localizer. -/
theorem localizedFourier_ofFun {f : Plane → ℝ}
    (hf : LocallyIntegrable f volume) (χ : TestFn) (ξ : Plane) :
    localizedFourier (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) χ ξ =
      angularFourierIntegral (fun x => χ x * f x) ξ := by
  have hi : Integrable (fun x => χ x * f x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  rw [angularFourierIntegral_eq_cos_sin hi, localizedFourier,
    Distribution.ofFun_apply (hf.locallyIntegrableOn _), Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  congr 2
  · apply integral_congr_ae
    filter_upwards [] with x
    simp only [TestFn.mulCos_apply, smul_eq_mul]
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [TestFn.mulSin_apply, smul_eq_mul]
    ring

/-- Angular-frequency Plancherel identifies the squared spatial L² norm with `(2π)⁻²` times the squared Fourier L² norm. -/
theorem lintegral_angularFourier_norm_sq {f : Plane → ℝ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
      ∫⁻ ξ : Plane, ENNReal.ofReal (‖angularFourierIntegral f ξ‖ ^ 2) =
      ∫⁻ x : Plane, ENNReal.ofReal (f x ^ 2) := by
  have hFc : Continuous (𝓕 (fun x : Plane => (f x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1.ofReal
  have hm : Measurable (fun ξ : Plane =>
      ENNReal.ofReal (‖𝓕 (fun x : Plane => (f x : ℂ)) ξ‖ ^ 2)) := by
    simpa only [Pi.pow_apply] using (hFc.norm.pow 2).measurable.ennreal_ofReal
  have hs : Measurable (fun ξ : Plane => (2 * Real.pi)⁻¹ • ξ) :=
    (continuous_id.const_smul ((2 * Real.pi)⁻¹ : ℝ)).measurable
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hc : ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
      ENNReal.ofReal |(((2 * Real.pi)⁻¹) ^ 2)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  simp_rw [angularFourierIntegral_eq_fourier]
  rw [← lintegral_map hm hs, Measure.map_addHaar_smul volume (by positivity : (2 * Real.pi)⁻¹ ≠ 0),
    hd, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, hc, one_mul]
  have hf := eLpNorm_fourier_eq_of_integrable hf2.ofReal hf1.ofReal
  have h2 := congrArg (fun v : ℝ≥0∞ => v ^ (2 : ℝ)) hf
  have hfmeas := (hFc.aestronglyMeasurable (μ := volume))
  have hFpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hfmeas
  have hfPow := eLpNorm_nnreal_pow_eq_lintegral (f := fun x : Plane => (f x : ℂ))
    (p := (2 : NNReal)) (by norm_num) hf2.ofReal.aestronglyMeasurable
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at hFpow hfPow h2
  have hEnergy := hFpow.symm.trans (h2.trans hfPow)
  simpa only [NNReal.coe_ofNat, ENNReal.rpow_two, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] using! hEnergy

end Critical2DKPZ.Analysis.Sobolev

end
