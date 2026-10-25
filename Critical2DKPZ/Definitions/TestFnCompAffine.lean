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
public import Critical2DKPZ.Definitions.TestFn

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

namespace TestFn

/-- `y ↦ φ(z + R y)` (§1.3, with `R` the rotation `e^{iα}·`). -/
def compAffine (φ : TestFn) (z : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) : TestFn where
  toFun y := φ (z + R y)
  contDiff' := φ.contDiff.comp (contDiff_const.add R.contDiff)
  hasCompactSupport' := by
    have h := φ.hasCompactSupport.comp_homeomorph (R.toHomeomorph.trans (Homeomorph.addLeft z))
    convert h using 1
    funext y
    rfl
  tsupport_subset' := fun _ _ => trivial

end TestFn

end Critical2DKPZ

end

end
