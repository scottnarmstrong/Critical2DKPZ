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

/-- `S_a φ(y) = a⁻¹ φ(y / √a)` for `a > 0` (§1.3), written `(√a)⁻² φ((√a)⁻¹ y)`.
(For `a ≤ 0` this is the zero function.) -/
def scale (φ : TestFn) (a : ℝ) : TestFn where
  toFun y := (Real.sqrt a)⁻¹ ^ 2 * φ ((Real.sqrt a)⁻¹ • y)
  contDiff' := by
    have := φ.contDiff
    fun_prop
  hasCompactSupport' := by
    rcases eq_or_ne (Real.sqrt a)⁻¹ 0 with h0 | hs
    · have h1 : (fun y : Plane => (Real.sqrt a)⁻¹ ^ 2 * φ ((Real.sqrt a)⁻¹ • y)) = fun _ => 0 := by
        funext y; simp [h0]
      rw [h1]
      exact HasCompactSupport.zero
    · convert (φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero _ hs)).mul_left
        (f := fun _ => (Real.sqrt a)⁻¹ ^ 2) using 1
      funext y
      rfl
  tsupport_subset' := fun _ _ => trivial

end TestFn

end Critical2DKPZ

end

end
