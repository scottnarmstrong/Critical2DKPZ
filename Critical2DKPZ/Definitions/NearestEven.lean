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
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.Site

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- A nearest point `[x]` of the even lattice `{z : z₁ + z₂ ∈ 2ℤ}` (§1.1). Writing
`x = (u + v, u − v)`, the even lattice is `{(a + b, a − b) : a, b ∈ ℤ}` and
`|x − (a + b, a − b)|² = 2 ((u − a)² + (v − b)²)`; we take `a = round u`, `b = round v`
(ties broken towards `+∞`, the fixed tie-breaking rule required by the source). -/
def nearestEven (x : Plane) : Site :=
  let a := round ((x 0 + x 1) / 2)
  let b := round ((x 0 - x 1) / 2)
  ![a + b, a - b]

end Critical2DKPZ

end

end
