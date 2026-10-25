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
public import Critical2DKPZ.Definitions.BlockCount
public import Critical2DKPZ.Definitions.BlockTime
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.SmoothedP2Plane

public import Critical2DKPZ.MomentBounds.CSZ25BlockMomentAssembly
public import Critical2DKPZ.MomentBounds.CCR25MomentBoundFour

/-! # Moments on geometric blocks

Lemma B.2 of the paper bounds second and fourth moments on geometric blocks uniformly on compact parameter intervals, using the fourth-moment estimate and its block specialization.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The variance and centered fourth moment of each geometric block partition function satisfy uniform bounds on compact parameter and block-scale intervals (Lemma B.2 of the paper). -/
theorem blockMoments (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i ≤ blockCount N ρ →
        Var[fun ω => smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω;
          disorderLaw] ≤ C / ((blockCount N ρ : ℝ) + 1 - i) ∧
        ∫ ω, |smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (i - 1)) (blockTime N ρ i) 0 ω - 1| ^ 4
          ∂disorderLaw ≤ C / ((blockCount N ρ : ℝ) + 1 - i) ^ 2 :=
  MomentBounds.blockMoments_of_blockFourthMomentBound
    (MomentBounds.blockFourthMomentBound_of_genMomentBound
      (MomentBounds.genMomentBound_of_ccr 4 fun _ =>
        MomentBounds.ccrMomentBound_four_of_wordRuns MomentBounds.wordRunsBound_four)) A ρ₀ ρ₁ hρ

end Critical2DKPZ.Provider

end

end
