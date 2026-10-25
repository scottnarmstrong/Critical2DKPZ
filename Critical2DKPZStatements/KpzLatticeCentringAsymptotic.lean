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
public import Critical2DKPZ.Definitions.KpzLatticeCentring
public import Critical2DKPZ.Provider.KpzLatticeCentringAsymptotic

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **Centring** (`eq:centering-constant` §1.2, Lemma 4.3 `lem:centering` §4.4):
`c^{ϑ,(N)}_t = −½ log log N + O(1)`. -/
theorem kpzLatticeCentring_asymptotic (ϑ t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ᶠ N in atTop, |kpzLatticeCentring ϑ N t + (1 / 2) * Real.log (Real.log N)| ≤ C :=
  by exact Critical2DKPZ.Provider.kpzLatticeCentring_asymptotic ϑ t ht
end Critical2DKPZ

end

end
