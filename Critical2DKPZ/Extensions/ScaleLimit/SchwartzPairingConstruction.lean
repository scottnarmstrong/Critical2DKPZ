/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.TestPairingLp
public import Critical2DKPZ.Extensions.ScaleLimit.IsometryClosure
public import Critical2DKPZ.Extensions.ScaleLimit.TestPairingIsometry
import Critical2DKPZ.Extensions.ScaleLimit.SpectralCutoffLimit

/-! # Constructing the stochastic Schwartz pairing -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The compact cutoff, regarded as a test and as a Schwartz function, has the same values. -/
theorem testSchwartzLinear_cutoff (n : ℕ) (f : SchwartzMap Plane ℝ) :
    testSchwartzLinear (Spectral.scaledCutoffTestFn n f) = Spectral.scaledCutoffSchwartz n f := by
  ext x
  rfl

/-- The Fourier transform of any Schwartz test lies in the closed spectral range of compact tests. -/
theorem schwartzSpectralLp_mem_closure (ν : Measure Plane) [ν.HasTemperateGrowth]
    (f : SchwartzMap Plane ℝ) :
    schwartzSpectralLp ν f ∈ (testSpectralLp ν).range.topologicalClosure := by
  apply (testSpectralLp ν).range.isClosed_topologicalClosure.mem_of_tendsto
    (schwartzFourier_cutoff_toLp_tendsto ν f)
  apply Eventually.of_forall
  intro n
  apply (testSpectralLp ν).range.le_topologicalClosure
  refine ⟨Spectral.scaledCutoffTestFn n f, ?_⟩
  change schwartzSpectralLp ν (testSchwartzLinear (Spectral.scaledCutoffTestFn n f)) = _
  rw [testSchwartzLinear_cutoff]
  rfl

/-- The spectral Schwartz map with codomain in the closed range of compact tests. -/
def schwartzClosedSpectral (ν : Measure Plane) [ν.HasTemperateGrowth] :
    SchwartzMap Plane ℝ →L[ℝ] (testSpectralLp ν).range.topologicalClosure :=
  (schwartzSpectralLp ν).codRestrict _ (schwartzSpectralLp_mem_closure ν)


/-- The stochastic Schwartz pairing obtained by extending the original spectral isometry. -/
def schwartzPairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Ω → Distr} {ν : Measure Plane} (hD : StationarySpectralData P D ν) :
    SchwartzMap Plane ℝ →L[ℝ] Lp ℝ 2 P := by
  let : ν.HasTemperateGrowth := spectral_hasTemperateGrowth hD
  exact (isometryOnClosure (testRandomLp hD) (testSpectralLp ν)
    (testRandomLp_norm hD)).toContinuousLinearMap.comp (schwartzClosedSpectral ν)

/-- The constructed pairing extends the original distribution on every compact test. -/
theorem schwartzPairing_test {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (f : TestFn) :
    schwartzPairing hD (Spectral.testFnToRealSchwartz f) = testRandomLp hD f := by
  let : ν.HasTemperateGrowth := spectral_hasTemperateGrowth hD
  exact isometryOnClosure_apply (testRandomLp hD) (testSpectralLp ν) (testRandomLp_norm hD) f

/-- The constructed extension preserves the complete spectral covariance pairing. -/
theorem schwartzPairing_covariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (f g : SchwartzMap Plane ℝ) :
    (∫ ω, schwartzPairing hD f ω * schwartzPairing hD g ω ∂P) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν := by
  let : ν.HasTemperateGrowth := spectral_hasTemperateGrowth hD
  let J := isometryOnClosure (testRandomLp hD) (testSpectralLp ν) (testRandomLp_norm hD)
  have hJ := J.inner_map_map (schwartzClosedSpectral ν f) (schwartzClosedSpectral ν g)
  have hreal : (∫ ω, schwartzPairing hD f ω * schwartzPairing hD g ω ∂P) =
      inner ℝ (schwartzPairing hD f) (schwartzPairing hD g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact ae_of_all P fun ω => by simp only [RCLike.inner_apply, conj_trivial]; ring
  rw [hreal]
  change inner ℝ (J (schwartzClosedSpectral ν f)) (J (schwartzClosedSpectral ν g)) = _
  rw [hJ]
  exact schwartzSpectralLp_inner ν f g

/-- Compact cutoffs converge to the constructed stochastic pairing in L². -/
theorem schwartzPairing_cutoff_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) (f : SchwartzMap Plane ℝ) :
    Tendsto (fun n => testRandomLp hD (Spectral.scaledCutoffTestFn n f)) atTop
      (𝓝 (schwartzPairing hD f)) := by
  let : ν.HasTemperateGrowth := spectral_hasTemperateGrowth hD
  let J := isometryOnClosure (testRandomLp hD) (testSpectralLp ν) (testRandomLp_norm hD)
  have h : Tendsto (fun n => schwartzClosedSpectral ν (Spectral.scaledCutoffSchwartz n f))
      atTop (𝓝 (schwartzClosedSpectral ν f)) :=
    tendsto_subtype_rng.mpr (schwartzFourier_cutoff_toLp_tendsto ν f)
  have hJ := J.continuous.continuousAt.tendsto.comp h
  convert hJ using 1
  · apply funext
    intro n
    dsimp only [Function.comp_apply]
    rw [← testSchwartzLinear_cutoff]
    exact (isometryOnClosure_apply (testRandomLp hD) (testSpectralLp ν)
      (testRandomLp_norm hD) (Spectral.scaledCutoffTestFn n f)).symm
  · rfl

end Critical2DKPZ.Extensions.ScaleLimit
