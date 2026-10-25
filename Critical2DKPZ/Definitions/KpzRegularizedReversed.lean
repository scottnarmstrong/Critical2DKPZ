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
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ShfPairing

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- Reversed regularised log-SHF `ℋ^{(δ)}_{t,T}(x, h₀) = log 𝒵_{t+δ,T}(g_δ^{(x)}, e^{h₀})
− E log 𝒵_{t+δ,T}(g_δ^{(0)}, 1)` (§5). -/
def kpzRegularizedReversed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t T δ : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) :
    ℝ :=
  Real.log (shfPairing Z (t + δ) T (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) -
    ∫ ω', Real.log (shfPairing Z (t + δ) T (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P

end Critical2DKPZ

end

end
