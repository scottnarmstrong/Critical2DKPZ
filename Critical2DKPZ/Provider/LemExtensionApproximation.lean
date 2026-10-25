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
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.KpzLatticeReversed
public import Critical2DKPZ.Definitions.KpzLatticeReversedReg
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn
import Critical2DKPZ.Provider.BlockMoments
import Critical2DKPZ.Provider.PropVD
import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates
import Critical2DKPZ.FutureProfiles.ProfileEstimates
import Critical2DKPZ.FutureProfiles.ProfileOrigin
import Critical2DKPZ.FutureProfiles.LogTailsOrigin
import Critical2DKPZ.FutureProfiles.AdaptiveLeftTail
import Critical2DKPZ.Smoothing.LatticeSmoothingRescaling

/-! # Approximation with a general terminal profile

Lemma 5.3 of the paper follows from geometric block moments, the one-point moment comparison and the smoothing estimate for a unit time interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The tested reversed lattice field and its temporal regularization differ in L² by at most a constant times the negative one-fortieth power of the absolute logarithm of the regularization scale, asymptotically and uniformly on compact time-gap and parameter intervals (Lemma 5.3 of the paper). -/
theorem lem_extension_approximation (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a b A : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ t T : ℝ, 0 ≤ t → T - t ∈ Set.Icc a b →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ x, φ x *
            (kpzLatticeReversed ϑ N t T h₀ x ω - kpzLatticeReversedReg ϑ N t T δ h₀ x ω))
            2 disorderLaw ≤ ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) := by
  have hC6 : OnePoint.BlockMomentsBound := fun A ρ₀ ρ₁ hρ =>
    Critical2DKPZ.Provider.blockMoments A ρ₀ ρ₁ hρ
  have hDiscrepancyStringInput : FutureProfiles.OpenStringBound := fun A =>
    Critical2DKPZ.Blocks.openDiscrepancyMass_sq_integral_le A
  have hBlockRatioInput : FutureProfiles.RatioBoundP := fun A =>
    OnePoint.blockGoodSet_compl_and_ratio_bound_of hC6 A
  have hPE : FutureProfiles.ProfileEstimatesBound := fun A =>
    FutureProfiles.profile_estimates_of hDiscrepancyStringInput hBlockRatioInput A
  have hO : FutureProfiles.PropPFOriginBound := fun A =>
    FutureProfiles.prop_PF_origin_of hDiscrepancyStringInput hPE A
  have hTail : FutureProfiles.LogProfileTailBound := fun A =>
    FutureProfiles.log_profile_tail_le_of hPE A
  have hL : FutureProfiles.LogTailsOriginBound := fun A =>
    FutureProfiles.logTails_origin_of hTail A
  exact Critical2DKPZ.Smoothing.lem_extension_approximation_of
    (fun A => Critical2DKPZ.Provider.prop_VD A) hO hL h₀ φ a b A ha hab

end Critical2DKPZ.Provider

end

end
