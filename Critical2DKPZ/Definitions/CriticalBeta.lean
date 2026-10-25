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
public import Critical2DKPZ.Definitions.CriticalSigmaSq

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- Critical disorder strength `β_N = √(log(1 + σ_N²)) ≥ 0`, the nonnegative solution of
`e^{β_N²} − 1 = σ_N²` (§1.1) whenever `σ_N² ≥ 0`; this holds as soon as `N ≥ 1` and
`log N > |ϑ|` (`criticalBeta_spec`). For the finitely many other `N` the source's `β_N` is undefined
and the value is a junk value of Mathlib's conventions (`x / 0 = 0`, `log (−x) = log x`, `√` of a
negative number is `0`): it is `0` for `N = 0` and when `σ_N² ∈ [−2, 0]`, and positive for `N = 1` and
when `σ_N² < −2`. Statements about `β_N` are asymptotic in `N` or restricted to such `N`. -/
def criticalBeta (ϑ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (1 + criticalSigmaSq ϑ N))

end Critical2DKPZ

end

end
