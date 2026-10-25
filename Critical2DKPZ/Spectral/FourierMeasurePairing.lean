/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartz
public import Critical2DKPZ.Spectral.FourierConvention
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Integrability of Fourier pairings against tempered measures -/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory
open scoped ComplexConjugate FourierTransform

namespace Critical2DKPZ.Spectral

/-- The continuous linear change of variables from the paper's angular frequency to Mathlib's
Fourier frequency. -/
noncomputable def angularFrequencyEquiv : Plane ≃L[ℝ] Plane := by
  let c : ℝ := (2 * Real.pi)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  let e : Plane ≃ₗ[ℝ] Plane := LinearEquiv.smulOfNeZero ℝ Plane c hc.ne'
  have he (x : Plane) : ‖e x‖ = c * ‖x‖ := by
    simp [e, c, LinearEquiv.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs]
  exact ContinuousLinearEquiv.ofHomothety e c hc he

/-- The paper's Fourier transform of a test function, regarded as a Schwartz function of
frequency. -/
def fourierKPZSchwartz (f : TestFn) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyEquiv
    (𝓕 (testFnToSchwartzMap f))

@[simp] theorem fourierKPZSchwartz_apply (f : TestFn) (ξ : Plane) :
    fourierKPZSchwartz f ξ = fourierKPZ (f : Plane → ℝ) ξ := by
  rw [fourierKPZ_eq_angularFourierIntegral,
    Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral_eq_fourier]
  change (𝓕 (testFnToSchwartzMap f)) (angularFrequencyEquiv ξ) =
    𝓕 (fun x : Plane => (f x : ℂ)) ((2 * Real.pi)⁻¹ • ξ)
  congr 1

/-- The real part of the Fourier pairing of two test functions, represented as a Schwartz
function of frequency. -/
def fourierKPZRealPairSchwartz (f g : TestFn) : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM
    (SchwartzMap.pairing (𝕜 := ℝ) (ContinuousLinearMap.mul ℝ ℂ)
      (fourierKPZSchwartz f)
      ((fourierKPZSchwartz g).postcompCLM (𝕜 := ℝ) Complex.conjCLE))

@[simp] theorem fourierKPZRealPairSchwartz_apply (f g : TestFn) (ξ : Plane) :
    fourierKPZRealPairSchwartz f g ξ =
      (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re := by
  simp [fourierKPZRealPairSchwartz, fourierKPZSchwartz_apply]

/-- Polynomial ball growth makes the real Fourier pairing integrable. -/
theorem integrable_fourierKPZRealPair_of_polynomial_ball_growth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (ν (Metric.closedBall (0 : Plane) R)).toReal ≤ A * R ^ k)
    (f g : TestFn) :
    Integrable (fun ξ : Plane => (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re) ν := by
  letI : ν.HasTemperateGrowth :=
    measure_hasTemperateGrowth_of_polynomial_ball_growth ν hgrowth
  have hpair : Integrable (fourierKPZRealPairSchwartz f g) ν :=
    SchwartzMap.integrable (μ := ν) (fourierKPZRealPairSchwartz f g)
  have heq : (fun ξ : Plane => (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re) =
      fourierKPZRealPairSchwartz f g := by
    funext ξ
    rw [fourierKPZRealPairSchwartz_apply]
  rw [heq]
  exact hpair

end Critical2DKPZ.Spectral

end
