/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzPairingConstruction
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzFourierTranslation
import Critical2DKPZ.Extensions.ScaleLimit.SchwartzLpLimit

/-! # Translated cutoffs approximate the translated stochastic Schwartz pairing -/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Translation of a compact test agrees with Schwartz translation. -/
theorem testSchwartzLinear_dilate_one (f : TestFn) (z : Plane) :
    testSchwartzLinear (f.dilate 1 z) = translateSchwartz z (testSchwartzLinear f) := by
  ext x
  change (1 : ℝ)⁻¹ ^ 2 * f ((1 : ℝ)⁻¹ • (x - z)) = f (x - z)
  simp

/-- The spectral limit identifies the stochastic limit for any compact-test approximation. -/
theorem testRandomLp_tendsto_of_spectral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) [ν.HasTemperateGrowth]
    (t : ℕ → TestFn) (f : SchwartzMap Plane ℝ)
    (ht : Tendsto (fun n => testSpectralLp ν (t n)) atTop (𝓝 (schwartzSpectralLp ν f))) :
    Tendsto (fun n => testRandomLp hD (t n)) atTop (𝓝 (schwartzPairing hD f)) := by
  let J := isometryOnClosure (testRandomLp hD) (testSpectralLp ν) (testRandomLp_norm hD)
  have hc : Tendsto (fun n => closureRangeMap (testSpectralLp ν) (t n)) atTop
      (𝓝 (schwartzClosedSpectral ν f)) := tendsto_subtype_rng.mpr ht
  have h := J.continuous.continuousAt.tendsto.comp hc
  convert h using 1
  · apply funext
    intro n
    exact (isometryOnClosure_apply (testRandomLp hD) (testSpectralLp ν)
      (testRandomLp_norm hD) (t n)).symm
  · rfl

/-- The Fourier transforms of translated compact cutoffs converge in spectral L². -/
theorem translated_cutoff_spectral_tendsto (ν : Measure Plane) [ν.HasTemperateGrowth]
    (f : SchwartzMap Plane ℝ) (z : Plane) :
    Tendsto (fun n => testSpectralLp ν ((Spectral.scaledCutoffTestFn n f).dilate 1 z))
      atTop (𝓝 (schwartzSpectralLp ν (translateSchwartz z f))) := by
  have hb := (Spectral.scaledCutoffSchwartz_isVonNBounded f).image
    (schwartzFourier.comp (SchwartzMap.compSubConstCLM ℝ z))
  rw [← Set.range_comp] at hb
  have h := tendsto_schwartz_toLp_of_bounded_pointwise ν
    (fun n => schwartzFourier (translateSchwartz z (Spectral.scaledCutoffSchwartz n f)))
    (schwartzFourier (translateSchwartz z f)) hb (fun ξ => ?_)
  · convert h using 1
    · apply funext
      intro n
      change schwartzSpectralLp ν
        (testSchwartzLinear ((Spectral.scaledCutoffTestFn n f).dilate 1 z)) = _
      rw [testSchwartzLinear_dilate_one, testSchwartzLinear_cutoff]
      rfl
    · rfl
  · simp only [schwartzFourier_apply, fourierKPZ_translateSchwartz]
    exact tendsto_const_nhds.mul (by
      simpa only [schwartzFourier_apply] using schwartzFourier_cutoff_tendsto f ξ)

/-- Translated compact cutoffs converge to the translated stochastic pairing. -/
theorem schwartzPairing_translated_cutoff_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (f : SchwartzMap Plane ℝ) (z : Plane) :
    Tendsto (fun n => testRandomLp hD ((Spectral.scaledCutoffTestFn n f).dilate 1 z))
      atTop (𝓝 (schwartzPairing hD (translateSchwartz z f))) := by
  let : ν.HasTemperateGrowth := spectral_hasTemperateGrowth hD
  exact testRandomLp_tendsto_of_spectral hD _ _ (translated_cutoff_spectral_tendsto ν f z)

end Critical2DKPZ.Extensions.ScaleLimit
