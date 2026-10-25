/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralDilationDerivative
public import Critical2DKPZ.Extensions.ScaleLimit.HighBandEnergy
import Mathlib.Tactic

/-! # The high remainder as a differentiable spectral L2 curve -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- A selected contraction from spectral to random L2, fixed for all radii. -/
def spectralPairingMap (hD : StationarySpectralData P D ν) : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 P := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  exact (exists_spectral_contraction P ν (schwartzExt hD) (schwartzExt_covariance hD)).choose

/-- Its operator norm is at most one. -/
theorem norm_spectralPairingMap_le (hD : StationarySpectralData P D ν) :
    ‖spectralPairingMap hD‖ ≤ 1 := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  exact (exists_spectral_contraction P ν (schwartzExt hD) (schwartzExt_covariance hD)).choose_spec.1

/-- The selected contraction agrees with the stochastic Schwartz extension. -/
theorem spectralPairingMap_schwartz (hD : StationarySpectralData P D ν)
    [ν.HasTemperateGrowth] (ψ : SchwartzMap Plane ℝ) :
    spectralPairingMap hD (spectralLp (ν := ν) ψ) = schwartzExt hD ψ :=
  (exists_spectral_contraction P ν (schwartzExt hD) (schwartzExt_covariance hD)).choose_spec.2 ψ

/-- Translation phase times the complementary fine-band cutoff. -/
def highFrequencyPhase (a : ℝ) (x ξ : Plane) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ))) * (1 - (chi (a • ξ) : ℂ))

/-- The high-frequency phase is measurable. -/
theorem measurable_highFrequencyPhase (a : ℝ) (x : Plane) :
    Measurable (highFrequencyPhase a x) := by unfold highFrequencyPhase; fun_prop

/-- Its pointwise operator norm is at most one. -/
theorem norm_highFrequencyPhase_le (a : ℝ) (x ξ : Plane) :
    ‖highFrequencyPhase a x ξ‖ ≤ 1 := by
  rw [highFrequencyPhase, norm_mul]
  have hp : ‖Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hp, one_mul]
  exact norm_one_sub_chi_le _

/-- The exact high-remainder multiplier is realized by the same spectral
contraction at every positive radius. -/
theorem bandHighRemainder_eq_spectral_curve (hD : StationarySpectralData P D ν)
    [ν.HasTemperateGrowth] (φ : TestFn) (x : Plane) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    bandHighRemainder hD a φ x r = spectralPairingMap hD
      (spectralMultipliedDilate ν (highFrequencyPhase a x) (measurable_highFrequencyPhase a x)
        (norm_highFrequencyPhase_le a x) (schwartzFourier (Spectral.testFnToRealSchwartz φ)) r) := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  have htest : testRandomLp hD (φ.dilate r x) = spectralPairingMap hD
      (spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x))) := by
    rw [spectralPairingMap_schwartz]
    apply Lp.ext
    exact (testRandomLp_coe hD _).trans (schwartzExt_test hD _).symm
  rw [bandHighRemainder, htest, bandAverage_eq_spectral_contraction hD (spectralPairingMap hD)
    (spectralPairingMap_schwartz hD) a ha, ← map_sub]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub
    (spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)))
    (compactBandPhase (ν := ν) a
      (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z))),
    spectralLp_ae_eq (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)),
    compactBandPhase_average_ae_eq (ν := ν) ha φ x r,
    spectralMultipliedDilate_ae_eq ν (highFrequencyPhase a x) (measurable_highFrequencyPhase a x)
      (norm_highFrequencyPhase_le a x) (schwartzFourier (Spectral.testFnToRealSchwartz φ)) hr.ne']
    with ξ hsub hf hg hh
  rw [hsub, hh]
  change spectralLp (ν := ν) (Spectral.testFnToRealSchwartz (φ.dilate r x)) ξ -
    compactBandPhase (ν := ν) a
      (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z)) ξ = _
  rw [hf, hg, schwartzFourier_apply]
  change Spectral.fourierKPZ (φ.dilate r x) ξ - _ = _
  rw [fourierKPZ_dilate_test φ x hr]
  change _ = highFrequencyPhase a x ξ * Spectral.fourierKPZ φ (r • ξ)
  unfold highFrequencyPhase
  ring

/-- The high remainder's L2 radius derivative. -/
def bandHighRemainderDerivative (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) (r : ℝ) : Lp ℝ 2 P := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  exact r⁻¹ • spectralPairingMap hD
    (spectralMultipliedDilate ν (highFrequencyPhase a x) (measurable_highFrequencyPhase a x)
      (norm_highFrequencyPhase_le a x) (radialSchwartzDerivative
        (schwartzFourier (Spectral.testFnToRealSchwartz φ))) r)

/-- L2 differentiability in the radius, without an uncountable choice of
representatives or a pathwise temperedness assumption. -/
theorem hasDerivAt_bandHighRemainder (hD : StationarySpectralData P D ν)
    (φ : TestFn) (x : Plane) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    HasDerivAt (bandHighRemainder hD a φ x) (bandHighRemainderDerivative hD a φ x r) r := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  have hh := (spectralPairingMap hD).hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_spectralMultipliedDilate ν (highFrequencyPhase a x) (measurable_highFrequencyPhase a x)
      (norm_highFrequencyPhase_le a x) (schwartzFourier (Spectral.testFnToRealSchwartz φ)) hr)
  rw [map_smul] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with q hq
  exact bandHighRemainder_eq_spectral_curve hD φ x ha hq

/-- The high-remainder radius derivative is continuous at every positive radius. -/
theorem continuousAt_bandHighRemainderDerivative (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (bandHighRemainderDerivative hD a φ x) r := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  exact (continuousAt_id.inv₀ hr.ne').smul
    ((spectralPairingMap hD).continuous.continuousAt.comp
      (continuousAt_spectralMultipliedDilate ν (highFrequencyPhase a x) (measurable_highFrequencyPhase a x)
        (norm_highFrequencyPhase_le a x) (radialSchwartzDerivative
          (schwartzFourier (Spectral.testFnToRealSchwartz φ))) hr))

end Critical2DKPZ.Extensions.ScaleLimit
