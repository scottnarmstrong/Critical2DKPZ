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
public import Critical2DKPZ.Provider.CriticalKPZCovarianceKernel

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **Theorem 1.4 (ii)** (`thm:properties`, covariance kernel, §1.3), flat initial condition. -/
theorem criticalKPZ_covarianceKernel (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (t : ℝ) (ht : 0 < t) :
    ∃ C : Plane → ℝ, (∀ z, 0 ≤ C z) ∧ (∀ z w, ‖z‖ = ‖w‖ → C z = C w) ∧
      (∀ K, IsCompact K → MemLp C 2 (volume.restrict K)) ∧ ContinuousOn C {0}ᶜ ∧
      (∀ f g : TestFn, cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) ∧
      Tendsto (fun z => C z / Real.log (Real.log ‖z‖⁻¹)) (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
  by exact Critical2DKPZ.Provider.criticalKPZ_covarianceKernel ϑ P Z hZ H hH t ht
end Critical2DKPZ

end

end
