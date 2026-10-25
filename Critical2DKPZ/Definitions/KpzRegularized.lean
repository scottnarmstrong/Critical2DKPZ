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

/-- Temporally regularised log-SHF `ℋ^{ϑ,(δ)}_t(h₀, x)` (§1.2):
`log 𝒵_{t−δ}(e^{h₀}, g_δ^{(x)}) − E log 𝒵_{t−δ}(1, g_δ^{(0)})`. The source's centring
`E log 𝒵_{t−δ}(1, g_δ^{(x)})` does not depend on `x` (translation invariance of the SHF, the SHF symmetries); it is
taken at `x = 0` as in §2.2. -/
def kpzRegularized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) :
    ℝ :=
  Real.log (shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y)) (fun y => heatKernel δ (y - x)) ω) -
    ∫ ω', Real.log (shfPairing Z 0 (t - δ) (fun _ => 1) (fun y => heatKernel δ y) ω') ∂P

end Critical2DKPZ

end

end
