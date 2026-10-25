/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandAverageFactorization
public import Critical2DKPZ.Extensions.ScaleLimit.ShapeDilation
import Critical2DKPZ.Extensions.ScaleLimit.SchwartzShapeComparison
import Critical2DKPZ.Extensions.ScaleLimit.SchwartzFourierTranslation
import Mathlib.Tactic

/-! # Spectral multipliers of the band averages and high remainders -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The compact frequency realization of a band kernel. -/
def compactBandPhase {ν : Measure Plane} [IsLocallyFiniteMeasure ν]
    (a : ℝ) (f : C(Metric.closedBall (0 : Plane) (2 / a), ℂ)) : Lp ℂ 2 ν :=
  compactSpectralEmbedding ν (2 / a)
    (⟨fun ξ => (chi (a • (ξ : Plane)) : ℂ), by fun_prop⟩ * f)

/-- Its pointwise multiplier is the band cutoff times the compact function. -/
theorem compactBandPhase_ae_eq {ν : Measure Plane} [IsLocallyFiniteMeasure ν]
    [ν.HasTemperateGrowth] (a : ℝ) (ha : 0 < a) (y : Plane) :
    spectralLp (ν := ν) (zetaScaled a y) =
      compactBandPhase (ν := ν) a (compactPhase (2 / a) (by positivity) y) := by
  unfold compactBandPhase
  apply Lp.ext
  filter_upwards [spectralLp_ae_eq (ν := ν) (zetaScaled a y),
    compactSpectralEmbedding_ae_eq ν (2 / a)
      (⟨fun ξ => (chi (a • (ξ : Plane)) : ℂ), by fun_prop⟩ *
        compactPhase (2 / a) (by positivity) y)] with ξ hf hJ
  rw [hf, hJ, fourierKPZ_zetaScaled a ha]
  classical
  by_cases hξ : ξ ∈ Metric.closedBall (0 : Plane) (2 / a)
  · simp only [compactSpectralFun, hξ, dite_true]
    change _ = (chi (a • ξ) : ℂ) * compactPhase (2 / a) (by positivity) y ⟨ξ, hξ⟩
    rw [compactPhase_apply, mul_comm]
  · simp only [compactSpectralFun, hξ, dite_false]
    have hn : 2 ≤ ‖a • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      have hh : 2 / a < ‖ξ‖ := lt_of_not_ge (fun h => hξ (mem_closedBall_zero_iff.mpr h))
      exact (div_le_iff₀ ha).mp hh.le |>.trans_eq (mul_comm _ _)
    rw [chi_eq_zero hn, Complex.ofReal_zero, mul_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The spectral contraction maps the explicit compact band multiplier to
its stochastic spatial average. -/
theorem bandAverage_eq_spectral_contraction (hD : StationarySpectralData P D ν)
    [IsLocallyFiniteMeasure ν] [ν.HasTemperateGrowth]
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 P)
    (hT : ∀ ψ, T (spectralLp (ν := ν) ψ) = schwartzExt hD ψ)
    (a : ℝ) (ha : 0 < a) (φ : TestFn) (x : Plane) (r : ℝ) :
    bandAverage hD a φ x r = T (compactBandPhase (ν := ν) a
      (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z))) := by
  let M : C(Metric.closedBall (0 : Plane) (2 / a), ℂ) →L[ℝ]
      C(Metric.closedBall (0 : Plane) (2 / a), ℂ) :=
    ContinuousLinearMap.mul ℝ _ ⟨fun ξ => (chi (a • (ξ : Plane)) : ℂ), by fun_prop⟩
  let S := T.comp ((compactSpectralEmbedding ν (2 / a)).comp M)
  apply bandAverage_eq_phase_average hD a ha S
  intro y
  rw [← hT, compactBandPhase_ae_eq a ha y]
  rfl

/-- The averaged spectral band has the expected cutoff-times-test multiplier. -/
theorem compactBandPhase_average_ae_eq {ν : Measure Plane} [IsLocallyFiniteMeasure ν]
    {a : ℝ} (ha : 0 < a) (φ : TestFn) (x : Plane) (r : ℝ) :
    (compactBandPhase (ν := ν) a
      (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z)) : Plane → ℂ) =ᵐ[ν]
      fun ξ => (chi (a • ξ) : ℂ) *
        (Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ))) * Spectral.fourierKPZ φ (r • ξ)) := by
  unfold compactBandPhase
  filter_upwards [compactSpectralEmbedding_ae_eq ν (2 / a)
    (⟨fun ξ => (chi (a • (ξ : Plane)) : ℂ), by fun_prop⟩ *
      (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z)))] with ξ hξ
  rw [hξ]
  classical
  by_cases hmem : ξ ∈ Metric.closedBall (0 : Plane) (2 / a)
  · simp only [compactSpectralFun, hmem, dite_true]
    change (chi (a • ξ) : ℂ) * _ = _
    rw [compactPhase_average_apply]
  · simp only [compactSpectralFun, hmem, dite_false]
    have hn : 2 ≤ ‖a • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      have hh : 2 / a < ‖ξ‖ := lt_of_not_ge (fun h => hmem (mem_closedBall_zero_iff.mpr h))
      exact (div_le_iff₀ ha).mp hh.le |>.trans_eq (mul_comm _ _)
    rw [chi_eq_zero hn, Complex.ofReal_zero, zero_mul]

/-- The Fourier transform of a dilated test, in the angular convention. -/
theorem fourierKPZ_dilate_test (φ : TestFn) (x : Plane) {r : ℝ} (hr : 0 < r) (ξ : Plane) :
    Spectral.fourierKPZ (φ.dilate r x) ξ =
      Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ))) * Spectral.fourierKPZ φ (r • ξ) := by
  change Spectral.fourierKPZ (Spectral.testFnToRealSchwartz (φ.dilate r x)) ξ = _
  rw [← shapeDilate_test r hr.ne' x φ, fourierKPZ_translateSchwartz,
    fourierKPZ_shapeDilate _ hr]
  rfl

/-- The high-frequency remainder is controlled by its exact spectral multiplier.
The contraction, averaging and all L2 integrability come from the spectral data. -/
theorem norm_bandHighRemainder_sq_le (hD : StationarySpectralData P D ν)
    (φ : TestFn) (x : Plane) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ‖bandHighRemainder hD a φ x r‖ ^ 2 ≤
      ∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * Spectral.fourierKPZ φ (r • ξ)‖ ^ 2 ∂ν := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  obtain ⟨T, hTnorm, hT⟩ := exists_spectral_contraction P ν
    (schwartzExt hD) (schwartzExt_covariance hD)
  have htest : testRandomLp hD (φ.dilate r x) =
      T (spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x))) := by
    rw [hT]
    apply Lp.ext
    exact (testRandomLp_coe hD _).trans (schwartzExt_test hD _).symm
  let V := spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)) -
    compactBandPhase (ν := ν) a
      (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z))
  have heq : bandHighRemainder hD a φ x r = T V := by
    rw [bandHighRemainder, htest, bandAverage_eq_spectral_contraction hD T hT a ha, ← map_sub]
  have hn : ‖T V‖ ≤ ‖V‖ := by
    calc
      _ ≤ ‖T‖ * ‖V‖ := T.le_opNorm V
      _ ≤ 1 * ‖V‖ := mul_le_mul_of_nonneg_right hTnorm (norm_nonneg V)
      _ = _ := one_mul _
  calc
    _ ≤ ‖V‖ ^ 2 := by rw [heq]; exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    _ = _ := by
      rw [norm_Lp_two_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub
        (spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)))
        (compactBandPhase (ν := ν) a
          (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z))),
        spectralLp_ae_eq (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)),
        compactBandPhase_average_ae_eq (ν := ν) ha φ x r] with ξ hsub hf hg
      change V ξ = _ at hsub
      change ‖V ξ‖ ^ 2 = _
      rw [hsub]
      change ‖spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)) ξ -
        compactBandPhase (ν := ν) a
          (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z)) ξ‖ ^ 2 = _
      rw [hf, hg]
      change ‖Spectral.fourierKPZ (φ.dilate r x) ξ - _‖ ^ 2 = _
      rw [fourierKPZ_dilate_test φ x hr]
      have halg (p q c : ℂ) : p * q - c * (p * q) = p * ((1 - c) * q) := by ring
      rw [halg, norm_mul, norm_translation_phase, one_mul]

end Critical2DKPZ.Extensions.ScaleLimit
