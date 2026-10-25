/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Defs
public import Critical2DKPZ.Analysis.Sobolev.FrequencyScaling
public import Critical2DKPZ.Analysis.Sobolev.Seminorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-! Localized function energies agree with weighted Fourier Sobolev energies in unitary coordinates, including infinite energies. -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Local negative Sobolev energy equals the weighted Fourier energy after changing angular frequency to `2π η`. -/
theorem localNegSobolevSq_eq_scaled_localizedFourier (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevSq a T χ =
      ∫⁻ η : Plane, ENNReal.ofReal
        ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) *
          ‖localizedFourier T χ ((2 * Real.pi) • η)‖ ^ 2) := by
  let H : Plane → ℝ≥0∞ := fun η => ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) *
      ‖localizedFourier T χ ((2 * Real.pi) • η)‖ ^ 2)
  have hweight : Continuous (fun η : Plane =>
      (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a)) := by
    have hb : Continuous (fun η : Plane => (1 : ℝ) + (2 * Real.pi * ‖η‖) ^ 2) := by
      fun_prop
    exact hb.rpow_const fun η => Or.inl (by positivity)
  have hmod : Continuous (fun η : Plane =>
      localizedFourier T χ ((2 * Real.pi) • η)) :=
    (continuous_localizedFourier T χ).comp (by fun_prop)
  have hm : Measurable H := by
    dsimp [H]
    exact (hweight.mul (hmod.norm.pow 2)).measurable.ennreal_ofReal
  have hscale (ξ : Plane) :
      (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hnormscale (ξ : Plane) :
      2 * Real.pi * ‖(2 * Real.pi)⁻¹ • ξ‖ = ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
    field_simp
  unfold localNegSobolevSq
  rw [← lintegral_angular_frequency_scaling hm]
  congr 1
  apply lintegral_congr
  intro ξ
  dsimp [H]
  rw [hscale, hnormscale, norm_localizedFourier_sq]

/-- The norm square of the Fourier transform of a real distribution is even in frequency. -/
theorem norm_localizedFourier_sq_neg (T : Distr) (χ : TestFn) (ξ : Plane) :
    ‖localizedFourier T χ (-ξ)‖ ^ 2 = ‖localizedFourier T χ ξ‖ ^ 2 := by
  have hc : χ.mulCos (-ξ) = χ.mulCos ξ := by
    ext x
    change χ x * Real.cos (inner ℝ (-ξ) x) = χ x * Real.cos (inner ℝ ξ x)
    simp [inner_neg_left, Real.cos_neg]
  have hs : χ.mulSin (-ξ) = -χ.mulSin ξ := by
    ext x
    change χ x * Real.sin (inner ℝ (-ξ) x) = -(χ x * Real.sin (inner ℝ ξ x))
    simp [inner_neg_left, Real.sin_neg]
  rw [norm_localizedFourier_sq, norm_localizedFourier_sq, hc, hs]
  simp

/-- Scaled local negative Sobolev energy is unchanged by reflection of the Fourier frequency. -/
theorem localNegSobolevSq_eq_scaled_localizedFourier_neg (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevSq a T χ =
      ∫⁻ η : Plane, ENNReal.ofReal
        ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) *
          ‖localizedFourier T χ (-((2 * Real.pi) • η))‖ ^ 2) := by
  rw [localNegSobolevSq_eq_scaled_localizedFourier]
  apply lintegral_congr
  intro η
  rw [norm_localizedFourier_sq_neg]

/-- For locally integrable functions, local negative Sobolev energy equals the unitary Fourier Sobolev energy of the localized function at the opposite order. -/
theorem localNegSobolevSq_ofFun_eq_sobolevNormSq (a : ℝ) {f : Plane → ℝ}
    (hf : LocallyIntegrable f volume) (χ : TestFn) :
    localNegSobolevSq a (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) χ =
      sobolevNormSq 2 (-a) (fun x => χ x * f x) := by
  have hi : Integrable (fun x => χ x * f x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  have hFc := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (hi.ofReal (𝕜 := ℂ))
  let H : Plane → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (-a) *
      ‖𝓕 (fun x => ((χ x * f x : ℝ) : ℂ)) ξ‖ ^ 2)
  have hm : Measurable H := by
    have hw : Continuous (fun ξ : Plane => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (-a)) :=
      (continuous_const.add ((continuous_const.mul continuous_norm).pow 2)).rpow_const
        (fun ξ => Or.inl (by positivity : (1 : ℝ) + (2 * Real.pi * ‖ξ‖) ^ 2 ≠ 0))
    exact (hw.mul (hFc.norm.pow 2)).measurable.ennreal_ofReal
  have hs (ξ : Plane) : 2 * Real.pi * ‖(2 * Real.pi)⁻¹ • ξ‖ = ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  unfold localNegSobolevSq
  simp_rw [← norm_localizedFourier_sq, localizedFourier_ofFun hf,
    angularFourierIntegral_eq_fourier]
  change ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
    (∫⁻ ξ : Plane, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
      ‖𝓕 (fun x => ((χ x * f x : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • ξ)‖ ^ 2)) = ∫⁻ ξ : Plane, H ξ
  have he (ξ : Plane) : ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
      ‖𝓕 (fun x => ((χ x * f x : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • ξ)‖ ^ 2) =
      H ((2 * Real.pi)⁻¹ • ξ) := by
    dsimp only [H]
    rw [hs]
  simp_rw [he]
  exact lintegral_angular_frequency_scaling hm

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
