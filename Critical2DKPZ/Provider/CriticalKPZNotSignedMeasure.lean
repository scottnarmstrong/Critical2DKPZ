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

public import Critical2DKPZ.Assembly.Final
public import Critical2DKPZ.SmallScales.SignedMeasureContradiction
public import Critical2DKPZ.Assembly.RootInputs

/-! # Absence of a signed-measure representation

Proposition 1.5 of the paper follows from the small-scale central limit theorem and spatial transport of the critical KPZ field.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- At every positive time, the critical KPZ field almost surely has no representation as a difference of locally finite measures (Proposition 1.5 of the paper). -/
theorem criticalKPZ_not_signedMeasure (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (t : ℝ) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ¬ ∃ μ ν : Measure Plane, IsLocallyFiniteMeasure μ ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : TestFn, H t 0 ω φ = (∫ x, φ x ∂μ) - ∫ x, φ x ∂ν :=
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  SmallScales.criticalKPZ_not_signedMeasure_of ϑ P Z hZ hsym Assembly.small_scale_shf_log_normality
    (Assembly.toyJointAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.heatStartLogAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.heatStartLogFieldAt_of_isCriticalSHF ϑ P Z hZ) Assembly.latticeSmoothingErrorEnergy
    H hH (Assembly.kpzTransportAt_of ϑ P Z hZ hsym H hH) t ht

end Critical2DKPZ.Provider

end

end
