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
public import Critical2DKPZ.Definitions.IsEhrhardType
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn

public import Critical2DKPZ.Assembly.Final
public import Critical2DKPZ.Assembly.EhrhardType
public import Critical2DKPZ.Assembly.HeatStartLog

/-! # Ehrhard-type laws of the critical KPZ process

Proposition 3.8 of the paper follows from the Ehrhard-type laws of heat-start logarithms and weak convergence of the regularized fields.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The critical KPZ field tested against a nonnegative smooth compactly supported function is almost everywhere measurable and has an Ehrhard-type law (Proposition 3.8 of the paper). -/
theorem criticalKPZ_isEhrhardType (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (t : ℝ) (ht : 0 < t)
    (φ : TestFn) (hφ : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun ω => H t 0 ω φ) P ∧ IsEhrhardType (P.map (fun ω => H t 0 ω φ)) :=
  Assembly.criticalKPZ_isEhrhardType_of ϑ P Z hZ
    (Assembly.heatStartLogFieldAt_of_isCriticalSHF ϑ P Z hZ)
    (Assembly.shfSymmetriesAt ϑ P Z hZ) H hH t ht φ hφ

end Critical2DKPZ.Provider

end

end
