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
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.TestFn

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- `H` is a **Critical 2D KPZ Process** for the SHF `Z`: for all `t > 0`, bounded continuous `h₀`
and test functions `φ`, `ℋ^{(δ)}_t(h₀, φ) → H t h₀ (φ)` in probability as `δ ↓ 0` (§1.2).
This determines `H t h₀` up to a null set; its existence is Theorem 1.2. -/
def IsCriticalKPZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn),
    TendstoInMeasure P (fun δ ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) (nhdsWithin 0 (Set.Ioi 0))
      (fun ω => H t h₀ ω φ)

end Critical2DKPZ

end

end
