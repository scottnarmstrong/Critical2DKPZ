/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn

public import Critical2DKPZ.Assembly.Final
public import Critical2DKPZ.Assembly.RootInputs
public import Critical2DKPZ.NonGaussian.ConditionalNonGaussianAssembly
public import Critical2DKPZ.NonGaussian.EndpointLimitNonsingularity

/-! # Non-Gaussianity of the critical KPZ process

Theorem 1.6 of the paper follows from Gaussian rigidity, deterministic polymer endpoint limits and their incompatibility with the singularity of the stochastic heat flow.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- At every positive time, the critical KPZ field tested against a nonzero nonnegative smooth compactly supported function has a non-Gaussian law, including exclusion of degenerate Gaussian laws (Theorem 1.6 of the paper). -/
theorem criticalKPZ_nonGaussian (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (t : ℝ) (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₀ : ψ ≠ 0) :
    ∀ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) ≠ gaussianReal m v :=
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  NonGaussian.criticalKPZ_nonGaussian_of_endpoint_nonsingularity
    (fun hVD ϑ _ _ P _ Z hZ hsym hHeatStartLogInput hsq hdense _ ht ψ hψ hψ₁ μ _ r hr hμ =>
      NonGaussian.endpoint_limit_not_singular_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense ht ψ hψ hψ₁ μ
        r hr hμ)
    (fun A => Critical2DKPZ.Provider.prop_VD A) ϑ P Z hZ hsym
    (Assembly.heatStartLogAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.heatStartSqAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.denseSHFAt ϑ P Z hZ) H hH (Assembly.endpointLimitAt_of ϑ P Z hZ hsym H hH)
    t ht ψ hψ hψ₀

end Critical2DKPZ.Provider

end

end
