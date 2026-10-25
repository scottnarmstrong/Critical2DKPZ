/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandDecomposition
public import Critical2DKPZ.Extensions.ScaleLimit.BandFieldDerivatives
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.MeanValue

/-! # Compact frequency representation of band averages -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The compact phase has the sharp Lipschitz constant given by the frequency radius. -/
theorem compactPhase_lipschitz (R : ℝ) (hR : 0 ≤ R) :
    LipschitzWith ⟨R, hR⟩ (compactPhase R hR) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_compactPhase R hR).differentiable (by simp))
  intro y
  change ‖fderiv ℝ (compactPhase R hR) y‖ ≤ R
  simpa only [norm_iteratedFDeriv_one, pow_one] using
    norm_iteratedFDeriv_compactPhase R hR 1 y

/-- Integrability in the uniform norm on the compact frequency ball. -/
theorem compactPhase_average_integrable (K : ℝ) (hK : 0 ≤ K)
    (φ : TestFn) (x : Plane) (r : ℝ) :
    Integrable (fun z : Plane => φ z • compactPhase K hK (x + r • z)) := by
  have hc : Continuous (fun z : Plane => compactPhase K hK (x + r • z)) :=
    (contDiff_compactPhase K hK).continuous.comp
      (continuous_const.add (continuous_const_smul r))
  exact hc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    φ.continuous φ.hasCompactSupport

/-- The compact phase average is exactly the Fourier multiplier of the test. -/
theorem compactPhase_average_apply (K : ℝ) (hK : 0 ≤ K)
    (φ : TestFn) (x : Plane) (r : ℝ) (ξ : Metric.closedBall (0 : Plane) K) :
    (∫ z : Plane, φ z • compactPhase K hK (x + r • z)) ξ =
      Complex.exp (-(Complex.I * (inner ℝ x (ξ : Plane) : ℂ))) *
        Spectral.fourierKPZ φ (r • (ξ : Plane)) := by
  rw [ContinuousMap.integral_apply (compactPhase_average_integrable K hK φ x r)]
  simp only [ContinuousMap.smul_apply, compactPhase_apply, RCLike.real_smul_eq_coe_mul]
  unfold Spectral.fourierKPZ
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have he : -(Complex.I * (inner ℝ (x + r • z) (ξ : Plane) : ℂ)) =
      -(Complex.I * (inner ℝ x (ξ : Plane) : ℂ)) +
        -(Complex.I * (inner ℝ z (r • (ξ : Plane)) : ℂ)) := by
    rw [inner_add_left, real_inner_smul_left, inner_smul_right,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  rw [he, Complex.exp_add]
  change (φ z : ℂ) * (_ * _) = _ * (_ * (φ z : ℂ))
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- Every band phase factorization commutes with spatial averaging. -/
theorem bandAverage_eq_phase_average (hD : StationarySpectralData P D ν)
    (a : ℝ) (ha : 0 < a)
    (S : C(Metric.closedBall (0 : Plane) (2 / a), ℂ) →L[ℝ] Lp ℝ 2 P)
    (hS : ∀ y, schwartzExt hD (zetaScaled a y) =
      S (compactPhase (2 / a) (by positivity) y))
    (φ : TestFn) (x : Plane) (r : ℝ) :
    bandAverage hD a φ x r =
      S (∫ z : Plane, φ z • compactPhase (2 / a) (by positivity) (x + r • z)) := by
  rw [← S.integral_comp_comm (compactPhase_average_integrable (2 / a) (by positivity) φ x r)]
  unfold bandAverage smoothSchwartzAverage
  apply integral_congr_ae
  filter_upwards [] with z
  rw [map_smul, ← hS, ← zetaScaled_eq_translate]

end Critical2DKPZ.Extensions.ScaleLimit
