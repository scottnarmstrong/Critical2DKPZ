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
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.PointToPlane
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SrwKernel

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- `Ẑ_{s,n}(x) = Z_{s,n}(q_s^{(x)}, 1) = ∑_y q_s(y − x) Z_{s,n}(y)` (§2.1): disorder removed up
to time `s`, the walk still started at `x` at time `0`. -/
def smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site) (ω : Disorder) : ℝ :=
  ∑' y : Site, srwKernel s (y - x) * pointToPlane β s (n - s) y ω

end Critical2DKPZ

end

end
