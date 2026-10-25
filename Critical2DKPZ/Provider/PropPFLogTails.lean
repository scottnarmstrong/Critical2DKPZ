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
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.DisorderPast
public import Critical2DKPZ.Definitions.EndpointDist
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.ProfileP2Fun
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SmoothedEndpointDist

public import Critical2DKPZ.MomentBounds.CSZ25BlockMomentAssembly
public import Critical2DKPZ.MomentBounds.CCR25MomentBoundFour
public import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates
public import Critical2DKPZ.FutureProfiles.SplitTranslationConsequences
public import Critical2DKPZ.FutureProfiles.ProfileOrigin
public import Critical2DKPZ.FutureProfiles.LogTailsOrigin
public import Critical2DKPZ.FutureProfiles.AdaptiveLeftTail
public import Critical2DKPZ.FutureProfiles.ProfileEstimates

/-! # Profile comparison and logarithmic tails

Propositions 4.4 and 4.5 of the paper follow from open-string and ratio estimates, geometric block moments and bounds on evolved endpoint profiles.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- Evolved polymer endpoint profiles satisfy comparison and second-moment bounds on high-probability events, and their logarithms satisfy uniform finite-order moment bounds (Propositions 4.4 and 4.5 of the paper). -/
theorem prop_PF_logTails (A : ℝ) :
    (∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A,
      ∃ G : Site → Set Disorder, ∀ x : Site,
        MeasurableSet[disorderPast (evenCeil (Real.sqrt δ * N))] (G x) ∧
        (disorderLaw (G x)ᶜ).toReal ≤ C / |Real.log δ| ∧
        ∫ ω in G x, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) (fun _ => 1) ω -
          profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
            (fun _ => 1) ω| ∂disorderLaw ≤ C / |Real.log δ| ∧
        (∫ ω in G x, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) (fun _ => 1) ω ^ 2
            ∂disorderLaw ≤ C * |Real.log δ|) ∧
        (∫ ω in G x, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
            (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ C * |Real.log δ|) ∧
        ∀ (f : Site → ℝ) (M : ℝ), (∀ z, |f z| ≤ M) →
          ∫ ω in G x, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) f ω -
            profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
              f ω| ∂disorderLaw ≤ C * M * Real.sqrt (Real.log |Real.log δ|) / |Real.log δ|) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (f : Site → ℝ) (L : ℝ), (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ L) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, ∀ x : Site,
          eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) x ω) f ω)) p disorderLaw ≤
            ENNReal.ofReal (C * Real.log |Real.log δ| + L + ε) ∧
          eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) x ω)
              f ω)) p disorderLaw ≤
            ENNReal.ofReal (C * Real.log |Real.log δ| + L + ε)) :=
  have hC6 : OnePoint.BlockMomentsBound := fun A ρ₀ ρ₁ hρ =>
    MomentBounds.blockMoments_of_blockFourthMomentBound
      (MomentBounds.blockFourthMomentBound_of_genMomentBound
        (MomentBounds.genMomentBound_of_ccr 4 fun _ =>
          MomentBounds.ccrMomentBound_four_of_wordRuns MomentBounds.wordRunsBound_four)) A ρ₀ ρ₁ hρ
  have hDiscrepancyStringInput : FutureProfiles.OpenStringBound := fun A => Blocks.openDiscrepancyMass_sq_integral_le A
  have hBlockRatioInput : FutureProfiles.RatioBoundP := fun A =>
    OnePoint.blockGoodSet_compl_and_ratio_bound_of hC6 A
  have hPE : FutureProfiles.ProfileEstimatesBound := fun A =>
    FutureProfiles.profile_estimates_of hDiscrepancyStringInput hBlockRatioInput A
  have hO : FutureProfiles.PropPFOriginBound := fun A =>
    FutureProfiles.prop_PF_origin_of hDiscrepancyStringInput hPE A
  have hT : FutureProfiles.LogProfileTailBound := fun A =>
    FutureProfiles.log_profile_tail_le_of hPE A
  have hL : FutureProfiles.LogTailsOriginBound := fun A => FutureProfiles.logTails_origin_of hT A
  FutureProfiles.prop_PF_logTails_of hO hL A

end Critical2DKPZ.Provider

end

end
