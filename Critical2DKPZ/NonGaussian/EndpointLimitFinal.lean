/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitAssembly
import Critical2DKPZ.NonGaussian.EndpointConvergence

/-! # Endpoint concentration and deterministic endpoint limits -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- The spatially averaged endpoint pairings concentrate under Gaussian rigidity. -/
theorem endpointPairing_average_concentrates_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
    (φ : C_c(Plane, ℝ)) :
    Tendsto (fun r => ∫ ω, |(∫ x, ψ x * endpointPairing Z r t x φ ω) -
        ∫ ω', (∫ x, ψ x * endpointPairing Z r t x φ ω') ∂P| ∂P) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  exact endpointPairing_average_concentrates_of_log_perturbation avgLogField_sub_tendsto_of
    ϑ P Z hZ hsym hC12 hHeatStartLogInput hHeatStartLogFieldInput H hH ht ψ hψ hψ₁ hG φ

/-- The averaged endpoint distribution has a deterministic subprobability limit along a subsequence. -/
theorem exists_endpoint_limit_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v) :
    ∃ (μ : Measure Plane) (r : ℕ → ℝ), IsFiniteMeasure μ ∧ μ Set.univ ≤ 1 ∧
      Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)) ∧ ∀ φ : C_c(Plane, ℝ),
        Tendsto (fun n => ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x φ ω) - ∫ y, φ y ∂μ| ∂P)
          atTop (𝓝 0) := by
  exact exists_endpoint_limit_of_log_perturbation avgLogField_sub_tendsto_of
    ϑ P Z hZ hsym hC12 hHeatStartLogInput hHeatStartLogFieldInput H hH ht ψ hψ hψ₁ hG

end Critical2DKPZ.NonGaussian
