/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.GaussianTestNormalization
public import Critical2DKPZ.NonGaussian.FlatEndpointSingularity
public import Critical2DKPZ.NonGaussian.Inputs
import Mathlib.Tactic

/-! Non-Gaussianity follows from endpoint-limit nonsingularity and singularity of the flat endpoint measure. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales
open scoped CompactlySupported BoundedContinuousFunction Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- Endpoint-limit nonsingularity and singularity of the flat endpoint measure rule out Gaussian laws for nonzero nonnegative KPZ test pairings. -/
theorem criticalKPZ_nonGaussian_of_endpoint_nonsingularity
    (hEndpointNonsingularityInput : ∀ (_hVD : Smoothing.PropVDBound) (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
    (_hsym : ShfSymmetriesAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z) (_hsq : HeatStartSqAt P Z) (_hdense : DenseSHFAt ϑ P Z)
    {t : ℝ} (_ht : 0 < t) (ψ : TestFn) (_hψ : ∀ x, 0 ≤ ψ x) (_hψ₁ : ∫ x, ψ x = 1)
    (μ : Measure Plane) [IsFiniteMeasure μ] (r : ℕ → ℝ) (_hr : Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)))
    (_hμ : ∀ φ : C_c(Plane, ℝ),
      Tendsto (fun n => ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x φ ω) - ∫ y, φ y ∂μ| ∂P)
        atTop (𝓝 0)),
    0 < P {ω | ¬ μ ⟂ₘ (Z (2 * t / 3) t ω).map Prod.snd})
    (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (hEnd : EndpointLimitAt P Z H)
    (t : ℝ) (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₀ : ψ ≠ 0) :
    ∀ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) ≠ gaussianReal m v := by
  intro m v hGaussian
  obtain ⟨φ, hφ, hφmean, hφGaussian⟩ := exists_normalized_test_gaussian_of
    ϑ P Z hZ H hH ht ψ hψ hψ₀ ⟨m, v, hGaussian⟩
  obtain ⟨μ, r, hμfinite, _, hr, hμ⟩ := hEnd ht φ hφ hφmean hφGaussian
  let : IsFiniteMeasure μ := hμfinite
  have hPositive := hEndpointNonsingularityInput hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense ht φ hφ hφmean μ r hr hμ
  have hSingular := shf_flatEndpoint_mutuallySingular_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense
    (s := 2 * t / 3) (t := t) (by positivity) (by linarith only [ht]) μ
  have hZero : P {ω | ¬ μ ⟂ₘ (Z (2 * t / 3) t ω).map Prod.snd} = 0 := ae_iff.mp hSingular
  exact (ne_of_gt hPositive) hZero

end Critical2DKPZ.NonGaussian

end
