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
public import Critical2DKPZ.Definitions.LocNegSobolevTop
public import Critical2DKPZ.Definitions.LocNegSobolevTopToDistr
public import Critical2DKPZ.Definitions.LocalNegSobolevSq
public import Critical2DKPZ.Definitions.TestFn

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

@[reducible, instance] def LocNegSobolevTop.topologicalSpace (s : ℝ) : TopologicalSpace (LocNegSobolevTop s) :=
  TopologicalSpace.generateFrom
    {U | ∃ (T : Distr) (χ : TestFn) (ε : ℝ≥0∞), 0 < ε ∧
      U = {S : LocNegSobolevTop s | localNegSobolevSq s (S.toDistr - T) χ < ε}}

end Critical2DKPZ

end

end
