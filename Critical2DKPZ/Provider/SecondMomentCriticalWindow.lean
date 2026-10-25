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
import Critical2DKPZ.Renewal.CumulativeUniformLimit
import Critical2DKPZ.Renewal.PolymerBridge

/-! # Second moments in the critical window

Claim B.1 and equation (4.1) of the paper follow from the critical renewal limit and a uniform logarithmic renewal bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The point-to-plane second moment has a positive logarithmic asymptotic at each fixed positive time and satisfies a uniform logarithmic bound throughout the critical window (Claim B.1 and equation (4.1) of the paper). -/
theorem secondMoment_criticalWindow (ϑ : ℝ) :
    (∀ t : ℝ, 0 < t → ∃ C : ℝ, 0 < C ∧
      Tendsto (fun N : ℕ => (∫ ω, pointToPlane (criticalBeta ϑ N) 0 (evenCeil (N * t)) 0 ω ^ 2
        ∂disorderLaw) / Real.log N) atTop (nhds C)) ∧
    (∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ N →
      criticalSigmaSq ϑ N * ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
        C / Real.log (1 + (N : ℝ) / k)) := by
  constructor
  · intro t ht
    refine ⟨Renewal.scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) t,
      Renewal.scalarRenewalPrimitive_pos _ ht, ?_⟩
    have hlim := Renewal.tendsto_criticalRenewalFunction_evenCeil ϑ ht
    apply hlim.congr'
    filter_upwards [Renewal.eventually_freeSecondMoment_eq_criticalRenewalFunction ϑ]
      with N hN
    rw [← hN]
    rfl
  · exact Renewal.secondMoment_log_bound ϑ

end Critical2DKPZ.Provider

end

end
