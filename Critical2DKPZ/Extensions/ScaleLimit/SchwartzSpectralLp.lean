/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralData
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Critical2DKPZ.Spectral.ScaledLocalizers
import Critical2DKPZ.CovarianceKernel.RadialInversion
import Critical2DKPZ.Spectral.BochnerSchwartzSchwartzExtension
import Mathlib.MeasureTheory.Function.L2Space

/-! # The angular Fourier transform in spectral L² -/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The angular Fourier transform on real Schwartz space, as a continuous real linear map. -/
def schwartzFourier : SchwartzMap Plane ℝ →L[ℝ] SchwartzMap Plane ℂ :=
  ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Spectral.angularFrequencyEquiv).restrictScalars ℝ).comp
    (((SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ).comp
      (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM))

@[simp] theorem schwartzFourier_apply (f : SchwartzMap Plane ℝ) (ξ : Plane) :
    schwartzFourier f ξ = Spectral.fourierKPZ f ξ := by
  have h : Spectral.fourierKPZ f ξ =
      Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral f ξ := by
    unfold Spectral.fourierKPZ Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    rw [real_inner_comm x ξ]
    push_cast
    ring
  rw [h, Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral_eq_fourier]
  rfl

/-- The spectral growth hypothesis supplies the integrable polynomial weights for Schwartz tests. -/
theorem spectral_hasTemperateGrowth {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : Ω → Distr} {ν : Measure Plane}
    (hD : StationarySpectralData P D ν) : ν.HasTemperateGrowth := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  obtain ⟨A, hA, hbound⟩ :=
    CovarianceKernel.spectralBallMass_logGrowth_of_tendsto ν hD.ballAsymp
  apply Spectral.measure_hasTemperateGrowth_of_polynomial_ball_growth
  refine ⟨2 * A, 1, fun R hR => ?_⟩
  have hlog : Real.log R ≤ R := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h := hbound R hR
  change (ν (Metric.closedBall 0 R)).toReal ≤ A * (1 + Real.log R) at h
  calc
    _ ≤ A * (1 + Real.log R) := h
    _ ≤ A * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) hA
    _ = 2 * A * R ^ 1 := by ring

/-- Fourier transforms of the compact cutoffs converge at every frequency. -/
theorem schwartzFourier_cutoff_tendsto (f : SchwartzMap Plane ℝ) (ξ : Plane) :
    Tendsto (fun n => schwartzFourier (Spectral.scaledCutoffSchwartz n f) ξ)
      atTop (𝓝 (schwartzFourier f ξ)) :=
  Spectral.tendsto_fourier_scaledCutoffSchwartz_apply f (Spectral.angularFrequencyEquiv ξ)

/-- The transformed cutoff family is bounded in every Schwartz seminorm. -/
theorem schwartzFourier_cutoff_bounded (f : SchwartzMap Plane ℝ) :
    Bornology.IsVonNBounded ℝ
      (Set.range fun n : ℕ => schwartzFourier (Spectral.scaledCutoffSchwartz n f)) := by
  have h := (Spectral.scaledCutoffSchwartz_isVonNBounded f).image schwartzFourier
  rw [← Set.range_comp] at h
  exact h

end Critical2DKPZ.Extensions.ScaleLimit
