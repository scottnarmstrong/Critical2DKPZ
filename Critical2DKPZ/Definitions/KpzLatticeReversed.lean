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
public import Critical2DKPZ.Definitions.CellAverage
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.LatticePoint
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ProfileP2Fun

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- Reversed lattice field `ℋ^{(N)}_{t,T}(x, h₀) = log Z_{[Nt],[NT]}(x_N, f_N) − E log Z_{[Nt],[NT]}(x_N, 1)`
(§5). -/
def kpzLatticeReversed (ϑ : ℝ) (N : ℕ) (t T : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) : ℝ :=
  Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t)) (evenCeil (N * T))
      (fun w => if w = latticePoint N x then 1 else 0) (cellAverage N fun y => Real.exp (h₀ y)) ω) -
    ∫ ω', Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * t)) (evenCeil (N * T))
      (fun w => if w = latticePoint N x then 1 else 0) (fun _ => 1) ω') ∂disorderLaw

end Critical2DKPZ

end

end
