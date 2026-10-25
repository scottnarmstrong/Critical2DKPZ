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
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.TestFnMulCos
public import Critical2DKPZ.Definitions.TestFnMulSin

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- `‖χ T‖²_{H^{-s}}` with the normalization of §6:
`(2π)^{-2} ∫ (1 + |ξ|²)^{-s} |(χT)^(ξ)|² dξ`, where `(χT)^(ξ) = T(χ e^{-i⟪ξ,·⟫})`, so that
`|(χT)^(ξ)|² = T(χ cos⟪ξ,·⟫)² + T(χ sin⟪ξ,·⟫)²`. Valued in `[0, ∞]`. -/
def localNegSobolevSq (s : ℝ) (T : Distr) (χ : TestFn) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
    ∫⁻ ξ : Plane, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-s) *
      ((T (χ.mulCos ξ)) ^ 2 + (T (χ.mulSin ξ)) ^ 2))

end Critical2DKPZ

end

end
