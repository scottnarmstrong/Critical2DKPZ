/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.TestPairingLp

/-! # Covariance and norm equality for the test pairing -/

public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The real inner product of spectral classes is the paper's Fourier pairing. -/
theorem schwartzSpectralLp_inner (ν : Measure Plane) [ν.HasTemperateGrowth]
    (f g : SchwartzMap Plane ℝ) :
    inner ℝ (schwartzSpectralLp ν f) (schwartzSpectralLp ν g) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [schwartzSpectralLp_coe ν f, schwartzSpectralLp_coe ν g] with ξ hf hg
  rw [hf, hg, real_inner_comm, Complex.inner]
  rfl

/-- Covariance is the real inner product of the stochastic L² classes. -/
theorem testRandomLp_inner {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (f g : TestFn) :
    inner ℝ (testRandomLp hD f) (testRandomLp hD g) =
      ∫ ω, D ω f * D ω g ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testRandomLp_coe hD f, testRandomLp_coe hD g] with ω hf hg
  rw [hf, hg, real_inner_comm, RCLike.inner_apply]
  rfl

/-- The spectral isometry hypothesis gives norm equality on the original test space. -/
theorem testRandomLp_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) [ν.HasTemperateGrowth] (f : TestFn) :
    ‖testRandomLp hD f‖ = ‖testSpectralLp ν f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    testRandomLp_inner, hD.isometry]
  exact (schwartzSpectralLp_inner ν (Spectral.testFnToRealSchwartz f)
    (Spectral.testFnToRealSchwartz f)).symm

end Critical2DKPZ.Extensions.ScaleLimit
