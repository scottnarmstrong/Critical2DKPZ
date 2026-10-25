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
public import Critical2DKPZ.Definitions.TestFnDilate

public import Critical2DKPZ.Assembly.Final
public import Critical2DKPZ.SmallScales.SmallScaleCLT
public import Critical2DKPZ.Assembly.RootInputs

/-! # Small-scale Gaussian fluctuations of the critical KPZ process

The small-scale KPZ limit in Theorem 1.4(i) of the paper follows from stochastic heat flow symmetries, the delayed heat-start central limit theorem, joint field convergence and the lattice smoothing estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The flat critical KPZ field tested against a nonnegative function on shrinking spatial scales and divided by the square root of the iterated logarithm converges in law to a centered Gaussian with variance equal to the squared test mass (Theorem 1.4(i) of the paper). -/
theorem criticalKPZ_smallScaleCLT (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (x : Plane) (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) :
    TendstoInDistribution
      (fun ε ω => H t 0 ω (φ.dilate ε x) / Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (gaussianReal 0 ((∫ y, φ y) ^ 2).toNNReal) :=
  SmallScales.criticalKPZ_smallScaleCLT_of ϑ P Z hZ (Assembly.shfSymmetriesAt ϑ P Z hZ)
    Assembly.small_scale_shf_log_normality (Assembly.toyJointAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.heatStartLogAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.heatStartLogFieldAt_of_isCriticalSHF ϑ P Z hZ)
    Assembly.latticeSmoothingErrorEnergy H hH t ht x φ hφ

end Critical2DKPZ.Provider

end

end
