/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzShapeComparison
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzField
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The band-field assertion of the shape lemma -/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The angular Fourier transform at zero is the integral of the real compact test. -/
theorem fourierKPZ_test_zero (φ : TestFn) :
    Spectral.fourierKPZ φ 0 = (∫ x, φ x : ℝ) := by
  unfold Spectral.fourierKPZ
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  exact Complex.ofRealCLM.integral_comp_comm
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The difference of the band field and the original tested distribution
represents one dilated, translated zero-frequency Schwartz shape. -/
theorem band_test_difference_ae_eq (hD : StationarySpectralData P D ν)
    (φ : TestFn) {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (x : Plane) :
    (fun ω => bandField hD (κ * ε) x ω - D ω (φ.dilate ε x)) =ᵐ[P]
      fun ω => schwartzExt hD (translateSchwartz x (shapeDilate ε hε.ne'
        (shapeDilate κ hκ.ne' zeta - Spectral.testFnToRealSchwartz φ))) ω := by
  have hshape : translateSchwartz x (shapeDilate ε hε.ne'
      (shapeDilate κ hκ.ne' zeta - Spectral.testFnToRealSchwartz φ)) =
      zetaScaled (κ * ε) x - Spectral.testFnToRealSchwartz (φ.dilate ε x) := by
    rw [shapeDilate_sub, shapeDilate_comp, shapeDilate_zeta]
    have hsub (f g : SchwartzMap Plane ℝ) :
        translateSchwartz x (f - g) = translateSchwartz x f - translateSchwartz x g := by
      ext y
      rfl
    rw [hsub, ← zetaScaled_eq_translate, shapeDilate_test]
  rw [hshape, map_sub]
  filter_upwards [bandField_ae_eq hD (κ * ε) x, schwartzExt_test hD (φ.dilate ε x),
    Lp.coeFn_sub (schwartzExt hD (zetaScaled (κ * ε) x))
      (schwartzExt hD (Spectral.testFnToRealSchwartz (φ.dilate ε x)))] with ω hband htest hsub
  rw [hband, ← htest]
  exact hsub.symm

/-- The band shape comparison: the normalized difference tends to zero in L2
at every positive scale time and every fixed positive change of width. -/
theorem shape_second_statement (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω,
      ((Real.sqrt (L : ℝ))⁻¹ * (bandField hD (κ * scaleRadius L s) x ω -
        D ω (φ.dilate (scaleRadius L s) x))) ^ 2 ∂P) atTop (𝓝 0) := by
  let ψ := shapeDilate κ hκ.ne' zeta - Spectral.testFnToRealSchwartz φ
  have hψ : schwartzFourier ψ 0 = 0 := by
    dsimp [ψ]
    rw [map_sub, sub_apply, schwartzFourier_apply, schwartzFourier_apply,
      fourierKPZ_shapeDilate zeta hκ, smul_zero, fourierKPZ_zeta,
      chi_eq_one (by simp : ‖(0 : Plane)‖ ≤ 1)]
    change (1 : ℂ) - Spectral.fourierKPZ φ 0 = 0
    rw [fourierKPZ_test_zero, hφ, Complex.ofReal_one, sub_self]
  apply (schwartzExt_shape_at_scaleRadius hD ψ hψ x hs).congr
  intro L
  have hrep := band_test_difference_ae_eq hD φ hκ (scaleRadius_pos L s) x
  have hsqrt : ((Real.sqrt (L : ℝ))⁻¹) ^ 2 = (L : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt L.property.le]
  calc
    _ = ∫ ω, (L : ℝ)⁻¹ * schwartzExt hD (translateSchwartz x
        (shapeDilate (scaleRadius L s) (scaleRadius_pos L s).ne' ψ)) ω ^ 2 ∂P :=
      (integral_const_mul _ _).symm
    _ = ∫ ω, ((Real.sqrt (L : ℝ))⁻¹ *
        (bandField hD (κ * scaleRadius L s) x ω - D ω (φ.dilate (scaleRadius L s) x))) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hrep] with ω hω
      rw [hω, mul_pow, hsqrt]

end Critical2DKPZ.Extensions.ScaleLimit
