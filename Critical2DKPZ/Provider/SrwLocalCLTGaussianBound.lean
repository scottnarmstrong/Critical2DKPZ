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
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SiteToPlane
public import Critical2DKPZ.Definitions.SrwKernel
import Critical2DKPZ.RandomWalk.Estimates

/-! # Local central limit and Gaussian bounds for the planar walk

Lemma A.2 of the paper follows from the planar walk local central limit estimate and Gaussian upper bound, with the parity normalization retained.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ.Provider

/-- The planar simple random walk kernel satisfies a parity-normalized local central limit estimate and a Gaussian upper bound (Lemma A.2 of the paper). -/
theorem srw_localCLT_gaussianBound :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z : Site, Even (z 0 + z 1 + n) →
      |srwKernel n z - 2 * heatKernel (n / 2) (siteToPlane z)| ≤ C / (n : ℝ) ^ 2) ∧
    (∃ C c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site,
      srwKernel n z ≤ C / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n)) := by
  obtain ⟨C, _, h⟩ := Critical2DKPZ.srwKernel_localCLT
  exact ⟨⟨C, h⟩, Critical2DKPZ.srwKernel_gaussianBound⟩

end Critical2DKPZ.Provider

end

end
