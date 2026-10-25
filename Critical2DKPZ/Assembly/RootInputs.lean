/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Provider.BlockMoments
public import Critical2DKPZ.Provider.PropVD
public import Critical2DKPZ.Provider.ShfLogNormality
public import Critical2DKPZ.Provider.ThmToyJoint
public import Critical2DKPZ.Smoothing.EnergyDilatePerturb
public import Critical2DKPZ.Provider.LemExtensionApproximation
public import Critical2DKPZ.SmallScales.Inputs
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.LocalSobolev.ReversalLaw
public import Critical2DKPZ.LocalSobolev.FlatCovariance
public import Critical2DKPZ.Assembly.HeatStartLog
public import Critical2DKPZ.Assembly.Invariance
public import Critical2DKPZ.SHF.Symmetries.DenseTransport
public import Critical2DKPZ.SmallScales.HeatStartMoments
public import Critical2DKPZ.NonGaussian.EndpointLimitFinal
public import Critical2DKPZ.NonGaussian.Inputs

/-! # Moment, covariance and transport estimates for critical fields

These estimates give the smoothing energy bound, joint convergence, reversal law and endpoint limits used in the KPZ process theorems. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped BoundedContinuousFunction

universe u

namespace Critical2DKPZ.Assembly

open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales

/-- The lattice smoothing error has a uniform unit-horizon energy bound over spatial dilations. -/
theorem latticeSmoothingErrorEnergy : SmallScales.LatticeSmoothingErrorEnergy :=
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
  Smoothing.latticeSmoothingError_unit_le_energy_dilate_of_perturb
    Smoothing.latticeSmoothingError_perturb_le (fun A => Critical2DKPZ.Provider.prop_VD A) hO hL

/-- The critical stochastic heat flow has the small-scale log-normal limit. -/
theorem small_scale_shf_log_normality : SmallScales.SmallScaleSHFLogNormality.{u} :=
  fun ϑ _ _ P _ Z hZ x => Critical2DKPZ.Provider.shf_logNormality ϑ P Z hZ x

/-- Reversed lattice fields converge jointly to the critical stochastic heat flow. -/
theorem toyJointAt_of_isCriticalSHF (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : ToyJointAt ϑ P Z :=
  fun T hT => Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT

/-- The SHF reversal law at every horizon (`ShfReversalLawAt`), at every critical SHF. -/
theorem shfReversalLawAt_of_isCriticalSHF (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : SmallScales.ShfReversalLawAt P Z :=
  fun T => LocalSobolev.shfReversal_measureLaw_of ϑ P Z hZ T

/-- Flat regularized KPZ fields satisfy the covariance bound. -/
theorem flatCovarianceAt_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z) : SmallScales.FlatCovarianceAt P Z :=
  fun _ _ ht₀ => LocalSobolev.kpzRegularized_flat_covariance_le_of
    (fun A => Critical2DKPZ.Provider.prop_VD A) ϑ P Z hZ
    (heatStartLogAt_of_isCriticalSHF ϑ P Z hZ) hsym ht₀

/-- Test pairings of the KPZ process are measurable and invariant under the stated transports. -/
theorem kpzTransportAt_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) :
    SmallScales.KpzTransportAt P H :=
  fun k t ht φ =>
    have h7 := criticalKPZ_invariance_of.{u, u} ϑ P Z hZ hsym
      (fun ϑ _ _ _ _ P P' _ _ Z Z' hZ hZ' k s t hst =>
        SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P' Z Z' hZ hZ' k s t hst)
      (fun ϑ _ _ _ _ P P' _ _ Z Z' hZ hZ' k s t hst =>
        SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P' Z Z' hZ hZ' k s t hst)
      H hH k t ht φ
    ⟨h7.1, h7.2.1⟩

/-- Heat-start fields have uniformly bounded second moments on time intervals bounded away from zero. -/
theorem heatStartSqAt_of_isCriticalSHF (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : SmallScales.HeatStartSqAt P Z :=
  fun _ _ hτ₀ => SmallScales.heatStart_sq_integral_le_of ϑ P Z hZ
    (heatStartLogAt_of_isCriticalSHF ϑ P Z hZ) hτ₀

/-- The KPZ process admits the stated endpoint limits. -/
theorem endpointLimitAt_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) :
    NonGaussian.EndpointLimitAt P Z H :=
  fun _ ht ψ hψ hψ₁ hG => NonGaussian.exists_endpoint_limit_of ϑ P Z hZ hsym
    (toyJointAt_of_isCriticalSHF ϑ P Z hZ) (heatStartLogAt_of_isCriticalSHF ϑ P Z hZ)
    (heatStartLogFieldAt_of_isCriticalSHF ϑ P Z hZ) H hH ht ψ hψ hψ₁ hG

end Critical2DKPZ.Assembly

end

end
