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

/-- `φ_ε^{(x)}(y) = ε^{-2} φ((y − x)/ε)` (§1.3). (For `ε = 0` this is the zero function.) -/
def dilate (φ : TestFn) (ε : ℝ) (x : Plane) : TestFn where
  toFun y := ε⁻¹ ^ 2 * φ (ε⁻¹ • (y - x))
  contDiff' := by
    have := φ.contDiff
    fun_prop
  hasCompactSupport' := by
    rcases eq_or_ne ε 0 with rfl | hε
    · have h0 : (fun y : Plane => (0 : ℝ)⁻¹ ^ 2 * φ ((0 : ℝ)⁻¹ • (y - x))) = fun _ => 0 := by
        funext y; simp
      rw [h0]
      exact HasCompactSupport.zero
    · have h := φ.hasCompactSupport.comp_homeomorph
        ((Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε)))
      convert h.mul_left (f := fun _ => ε⁻¹ ^ 2) using 1
      funext y
      simp [sub_eq_add_neg]
  tsupport_subset' := fun _ _ => trivial

end TestFn

end Critical2DKPZ

end

end
