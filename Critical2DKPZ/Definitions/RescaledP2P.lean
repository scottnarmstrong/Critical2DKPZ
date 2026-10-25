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
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.LatticePoint
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.PointToPoint

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- Rescaled point-to-point partition function `𝒵^{ϑ,(N)}_{s,t}(x, y)` (§1.1), as a density on
`ℝ² × ℝ²`; it uses the walk from time `[Ns]` to time `[Nt]` (for `s > t` the natural subtraction gives
zero steps, a value no statement uses). -/
def rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) (ω : Disorder) : ℝ :=
  (N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t) - evenCeil (N * s))
    (latticePoint N p.1) (latticePoint N p.2) ω

end Critical2DKPZ

end

end
