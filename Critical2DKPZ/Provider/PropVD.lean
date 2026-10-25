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
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.GaussianityDefect
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SmoothedP2Plane

public import Critical2DKPZ.MomentBounds.CSZ25BlockMomentAssembly
public import Critical2DKPZ.MomentBounds.CCR25MomentBoundFour
public import Critical2DKPZ.OnePoint.MomentProductSmallTimeOrigin
public import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
public import Critical2DKPZ.OnePoint.BlockRatioTiltedLawEstimates

/-! # One-point moment comparison

Proposition 4.1 of the paper follows from the small-time origin estimate, geometric block moments and the tilted ratio bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The Gaussianity defect of a smoothed log partition function lies between zero and the logarithm of the partition function’s second-to-negative-first moment ratio, with uniform bounds and short-time decay (Proposition 4.1 of the paper). -/
theorem prop_VD (A : ℝ) :
    (∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ < T₁ → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (x : Site) (s n : ℕ), Even s → Even n → s ≤ n → T₀ * N ≤ n → (n : ℝ) ≤ T₁ * N →
        0 ≤ gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s n x ω)) ∧
        gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s n x ω)) ≤
          Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n x ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n x ω)⁻¹ ∂disorderLaw) ∧
        Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n x ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n x ω)⁻¹ ∂disorderLaw) ≤ C) ∧
    (∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ (x : Site) (s : ℕ), Even s → s ≤ evenCeil (Real.sqrt δ * N) →
          Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s (evenCeil (Real.sqrt δ * N)) x ω ^ 2
              ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s (evenCeil (Real.sqrt δ * N)) x ω)⁻¹ ∂disorderLaw) ≤
            C / |Real.log δ| ^ ((1 : ℝ) / 4) + o N) :=
  have hC6 : OnePoint.BlockMomentsBound := fun A ρ₀ ρ₁ hρ =>
    MomentBounds.blockMoments_of_blockFourthMomentBound
      (MomentBounds.blockFourthMomentBound_of_genMomentBound
        (MomentBounds.genMomentBound_of_ccr 4 fun _ =>
          MomentBounds.ccrMomentBound_four_of_wordRuns MomentBounds.wordRunsBound_four)) A ρ₀ ρ₁ hρ
  have hQ : OnePoint.TiltedRatioBound := fun A =>
    OnePoint.blockGoodSet_tilted_compl_and_ratio_bound_of hC6 A
  ⟨OnePoint.prop_VD_part1_of A (OnePoint.smallTimeOriginBound_of hC6 hQ A),
    OnePoint.prop_VD_part2_of A (OnePoint.smallTimeOriginBound_of hC6 hQ A)⟩

end Critical2DKPZ.Provider

end

end
