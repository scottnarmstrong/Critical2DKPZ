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
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.KpzLatticeReversed
public import Critical2DKPZ.Definitions.KpzRegularizedReversed
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ShfSigma
public import Critical2DKPZ.Definitions.TestFn

public import Critical2DKPZ.Provider.BlockMoments
public import Critical2DKPZ.Provider.PropVD
public import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates
public import Critical2DKPZ.FutureProfiles.ProfileEstimates
public import Critical2DKPZ.FutureProfiles.ProfileOrigin
public import Critical2DKPZ.FutureProfiles.LogTailsOrigin
public import Critical2DKPZ.FutureProfiles.AdaptiveLeftTail
public import Critical2DKPZ.Smoothing.LatticeSmoothingRescaling
public import Critical2DKPZ.Smoothing.UnitHorizonPerturbed
public import Critical2DKPZ.JointConvergence.ThmToyJointLimit
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
public import Critical2DKPZ.SHF.Symmetries.LatticeReversal

/-! # Joint convergence of the lattice fields

Theorem 5.1 of the paper follows from positive heat pairings, time reversal of the stochastic heat flow and the lattice smoothing estimate for general terminal profiles.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- Tested reversed lattice fields converge jointly in law to measurable stochastic heat flow observables, with finite-order Lᵖ convergence and a quantitative L² rate for their temporal regularizations and joint law equal to that of any associated critical KPZ field (Theorem 5.1 of the paper). -/
theorem thm_toy_joint (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (T : ℝ) (hT : 0 < T) :
    ∃ X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ,
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn), 0 ≤ t → t < T → Measurable[shfSigma Z] (X t h₀ φ)) ∧
      (∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a : ℝ), 0 < a → a ≤ T → ∃ C δ₁ : ℝ, 0 < δ₁ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ t : ℝ, 0 ≤ t → t ≤ T - a →
          eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) 2 P ≤
            ENNReal.ofReal (C * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40))) ∧
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞), 0 ≤ t → t < T → 1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm (fun ω =>
            (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
        (∀ i, 0 ≤ t i ∧ t i < T) →
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
            ∫ x, φ i x * kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω)
          atTop (fun ω i => X (t i) (h₀ i) (φ i) ω) (fun _ => disorderLaw) P) ∧
      (∀ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr, IsCriticalKPZ P Z H →
        ∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
          (∀ i, 0 ≤ t i ∧ t i < T) →
          P.map (fun ω i => X (t i) (h₀ i) (φ i) ω) = P.map (fun ω i => H (T - t i) (h₀ i) ω (φ i))) :=
  have hDiscrepancyStringInput : FutureProfiles.OpenStringBound := fun A => Blocks.openDiscrepancyMass_sq_integral_le A
  have hBlockRatioInput : FutureProfiles.RatioBoundP := fun A =>
    OnePoint.blockGoodSet_compl_and_ratio_bound_of
      (fun A ρ₀ ρ₁ hρ => Critical2DKPZ.Provider.blockMoments A ρ₀ ρ₁ hρ) A
  have hPE : FutureProfiles.ProfileEstimatesBound := fun A =>
    FutureProfiles.profile_estimates_of hDiscrepancyStringInput hBlockRatioInput A
  have hO : FutureProfiles.PropPFOriginBound := fun A =>
    FutureProfiles.prop_PF_origin_of hDiscrepancyStringInput hPE A
  have hTail : FutureProfiles.LogProfileTailBound := fun A =>
    FutureProfiles.log_profile_tail_le_of hPE A
  have hL : FutureProfiles.LogTailsOriginBound := fun A =>
    FutureProfiles.logTails_origin_of hTail A
  JointConvergence.thm_toy_joint_of ϑ P Z hZ T hT
    (fun hs hst hδ x g => SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g)
    (fun k s t δ x g h =>
      SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ k s t δ x g h)
    (fun s t δ x h₀ hs hst hδ =>
      let h :=
        SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst hδ
      ⟨h.1, h.2.1⟩)
    (fun k s t hst => SHF.Symmetries.isCriticalSHF_reverse_fdd ϑ P Z hZ T k s t hst)
    (fun h₀ φ a b A ha hab => Smoothing.lem_extension_approximation_of_perturb
      Smoothing.latticeSmoothingError_perturb_le
      (fun A => Critical2DKPZ.Provider.prop_VD A) hO hL h₀ φ a b A ha hab)

end Critical2DKPZ.Provider

end

end
