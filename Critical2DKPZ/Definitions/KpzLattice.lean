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
public import Critical2DKPZ.Definitions.KpzLatticeCentring
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.RescaledP2P

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- Renormalised log-partition function `ℋ^{ϑ,(N)}_t(h₀, x)` (§1.2):
`log 𝒵^{(N)}_t(e^{h₀}, x) − E log 𝒵^{(N)}_t(1, x)`, with `𝒵^{(N)}_t(u₀, x) = ∫ u₀(y) 𝒵^{(N)}_{0,t}(y, x) dy`
(§1.1); the centring is taken at `x = 0` (it does not depend on `x`, §1.2). -/
def kpzLattice (ϑ : ℝ) (N : ℕ) (t : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) : ℝ :=
  Real.log (∫ y, Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) - kpzLatticeCentring ϑ N t

end Critical2DKPZ

end

end
