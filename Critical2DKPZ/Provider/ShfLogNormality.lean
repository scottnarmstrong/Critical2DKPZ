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
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ShfPairing

public import Critical2DKPZ.Provider.BlockMoments
public import Critical2DKPZ.LogNormality.SHFLogNormality
public import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates
public import Critical2DKPZ.FutureProfiles.ProfileEstimates
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard

/-! # Small-scale log-normality of the stochastic heat flow

Theorem 8.1 of the paper follows from lattice block moments, endpoint profile estimates and convergence of heat-start logarithms and their means.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- Centered delayed heat-start logarithms of the stochastic heat flow, divided by the square root of log log of the inverse spatial scale, converge in law to a standard Gaussian (Theorem 8.1 of the paper). -/
theorem shf_logNormality (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (x : Plane) :
    TendstoInDistribution
      (fun (ε : Set.Ioo (0 : ℝ) 1) ω =>
        (Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1 (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω) -
          ∫ ω', Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1 (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x))
            (fun _ => 1) ω') ∂P) /
        Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹)))
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) id (fun _ => P) (gaussianReal 0 1) :=
  have hC6 : OnePoint.BlockMomentsBound := fun A ρ₀ ρ₁ hρ =>
    Critical2DKPZ.Provider.blockMoments A ρ₀ ρ₁ hρ
  have hDiscrepancyStringInput : FutureProfiles.OpenStringBound := fun A => Blocks.openDiscrepancyMass_sq_integral_le A
  have hBlockRatioInput : FutureProfiles.RatioBoundP := fun A =>
    OnePoint.blockGoodSet_compl_and_ratio_bound_of hC6 A
  have hPE : FutureProfiles.ProfileEstimatesBound := fun A =>
    FutureProfiles.profile_estimates_of hDiscrepancyStringInput hBlockRatioInput A
  LogNormality.shf_logNormality_of hC6 hPE ϑ P Z hZ
    (LogNormality.logHeatPairingLimit_of ϑ P Z hZ
      (fun hs hst hδ x g => SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g)
      (fun k s t δ x g h =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ k s t δ x g h)
      (fun s t δ x h₀ hs hst hδ =>
        let h := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst hδ
        ⟨h.1, h.2.1⟩)) x

end Critical2DKPZ.Provider

end

end
