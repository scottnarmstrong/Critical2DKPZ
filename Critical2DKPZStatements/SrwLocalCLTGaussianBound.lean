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
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SiteToPlane
public import Critical2DKPZ.Definitions.SrwKernel
public import Critical2DKPZ.Provider.SrwLocalCLTGaussianBound

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **local CLT and Gaussian bound for the simple random walk on `ℤ²`** (additive local CLT
LL10 Thm 2.3.5 eq. (2.23), cited by KPZ as Thm 2.3.11; Gaussian bound LL10 Props 2.1.2, 2.4.6; HS93): `q_n(z) = 2 g_{n/2}(z) + O(n⁻²)` uniformly over sites of the parity of
`n`, and `q_n(z) ≤ C n⁻¹ e^{−c|z|²/n}`. -/
theorem srw_localCLT_gaussianBound :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z : Site, Even (z 0 + z 1 + n) →
      |srwKernel n z - 2 * heatKernel (n / 2) (siteToPlane z)| ≤ C / (n : ℝ) ^ 2) ∧
    (∃ C c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site,
      srwKernel n z ≤ C / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n)) :=
  by exact Critical2DKPZ.Provider.srw_localCLT_gaussianBound
end Critical2DKPZ

end

end
