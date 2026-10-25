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
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.TestFnCompAffine
public import Critical2DKPZ.Definitions.TestFnScale

public import Critical2DKPZ.Assembly.Final
public import Critical2DKPZ.Assembly.Invariance
public import Critical2DKPZ.SHF.Symmetries.DenseTransport

/-! # Invariance of the critical KPZ process

Proposition 1.8 of the paper follows from the symmetries and uniqueness in law of the stochastic heat flow and convergence of the regularized fields.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The finite-dimensional laws of the flat critical KPZ process are invariant under spatial translations and rotations and satisfy parabolic scaling covariance (Proposition 1.8 of the paper). -/
theorem criticalKPZ_invariance (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) (φ : Fin k → TestFn) :
    (∀ i, AEMeasurable (fun ω => H (t i) 0 ω (φ i)) P) ∧
    (∀ (z : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane), LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
      P.map (fun ω i => H (t i) 0 ω ((φ i).compAffine z R)) = P.map (fun ω i => H (t i) 0 ω (φ i))) ∧
    (∀ a : ℝ, 0 < a → ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)), IsCriticalSHF (ϑ + Real.log a) P' Z' →
      ∀ H' : ℝ → (Plane →ᵇ ℝ) → Ω' → Distr, IsCriticalKPZ P' Z' H' →
        P.map (fun ω i => H (a * t i) 0 ω ((φ i).scale a)) = P'.map (fun ω i => H' (t i) 0 ω (φ i))) :=
  Assembly.criticalKPZ_invariance_of ϑ P Z hZ (Assembly.shfSymmetriesAt ϑ P Z hZ)
    (fun ϑ _ _ _ _ P P' _ _ Z Z' hZ hZ' k s t hst =>
      SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P' Z Z' hZ hZ' k s t hst)
    (fun ϑ _ _ _ _ P P' _ _ Z Z' hZ hZ' k s t hst =>
      SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P' Z Z' hZ hZ' k s t hst)
    H hH k t ht φ

end Critical2DKPZ.Provider

end

end
