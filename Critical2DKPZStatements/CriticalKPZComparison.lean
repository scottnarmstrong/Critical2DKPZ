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
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Provider.CriticalKPZComparison

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **Comparison principle** (§1.2): for bounded Lipschitz `h₀, h₀'`,
`|ℋ_t(h₀, ψ) − ℋ_t(h₀', ψ)| ≤ ‖ψ‖₁ ‖h₀ − h₀'‖_∞`, for the regularised fields and in the limit. -/
theorem criticalKPZ_comparison (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h₀ h₀' : Plane →ᵇ ℝ) (hL : ∃ L, LipschitzWith L h₀)
    (hL' : ∃ L, LipschitzWith L h₀') (ψ : TestFn) :
    (∀ δ, 0 < δ → δ < t → ∀ᵐ ω ∂P,
      |(∫ x, ψ x * kpzRegularized P Z t δ h₀ x ω) - ∫ x, ψ x * kpzRegularized P Z t δ h₀' x ω| ≤
        (∫ x, |ψ x|) * ‖h₀ - h₀'‖) ∧
    ∀ᵐ ω ∂P, |H t h₀ ω ψ - H t h₀' ω ψ| ≤ (∫ x, |ψ x|) * ‖h₀ - h₀'‖ :=
  by exact Critical2DKPZ.Provider.criticalKPZ_comparison ϑ P Z hZ H hH t ht h₀ h₀' hL hL' ψ
end Critical2DKPZ

end

end
