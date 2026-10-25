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
public import Critical2DKPZ.Provider.LemExtensionApproximation

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **log-polymer smoothing for general initial conditions** (KPZ Lemma 5.3
`lem:extension-approximation`, §5.2, generalizing Proposition 2.3 `prop:smo`, §2.2):
`limsup_N ‖ℋ^{(N)}_{t,T}(φ, h₀) − ℋ^{(N;δ)}_{t,T}(φ, h₀)‖_{L²} ≤ C |log δ|^{-1/40}` for small `δ`, with `C`
locally uniform in `(T − t, ϑ)`. -/
theorem lem_extension_approximation (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a b A : ℝ) (ha : 0 < a)
    (hab : a ≤ b) :
    ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ϑ ∈ Set.Icc (-A) A, ∀ t T : ℝ, 0 ≤ t →
      T - t ∈ Set.Icc a b → ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        eLpNorm (fun ω => ∫ x, φ x * (kpzLatticeReversed ϑ N t T h₀ x ω -
            kpzLatticeReversedReg ϑ N t T δ h₀ x ω)) 2 disorderLaw ≤
          ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε) :=
  by exact Critical2DKPZ.Provider.lem_extension_approximation h₀ φ a b A ha hab
end Critical2DKPZ

end

end
