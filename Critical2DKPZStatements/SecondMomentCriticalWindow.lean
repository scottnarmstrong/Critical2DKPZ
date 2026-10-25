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
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.CriticalSigmaSq
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.PointToPlane
public import Critical2DKPZ.Provider.SecondMomentCriticalWindow

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **second moments in the critical window** (CSZ19a Prop A.2, KPZ §4.1 and
`claim:VN`): `E Z_{[Nt]}(0)² ∼ C_{ϑ,t} log N` with `C_{ϑ,t} > 0`, and
`σ_N² E Z_k(0)² ≤ C_ϑ / log(1 + N/k)` for `1 ≤ k ≤ N`, for all large `N`. -/
theorem secondMoment_criticalWindow (ϑ : ℝ) :
    (∀ t : ℝ, 0 < t → ∃ C : ℝ, 0 < C ∧
      Tendsto (fun N : ℕ => (∫ ω, pointToPlane (criticalBeta ϑ N) 0 (evenCeil (N * t)) 0 ω ^ 2
        ∂disorderLaw) / Real.log N) atTop (nhds C)) ∧
    (∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ N →
      criticalSigmaSq ϑ N * ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
        C / Real.log (1 + (N : ℝ) / k)) :=
  by exact Critical2DKPZ.Provider.secondMoment_criticalWindow ϑ
end Critical2DKPZ

end

end
