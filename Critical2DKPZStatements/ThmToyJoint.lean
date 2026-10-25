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
public import Critical2DKPZ.Provider.ThmToyJoint

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **finite-dimensional convergence** (KPZ Theorem 5.1 `thm:toy-joint`, §5, with the rate
`prop:eq-temporal-approximation` §5.3 and joint initial conditions, remark §6.2):
for `0 ≤ t < T` the fields `ℋ^{(δ)}_{t,T}(φ, h₀)` converge to SHF-measurable limits `X t h₀ φ` at rate
`|log(δ/(T−t))|^{-1/40}` in `L²`, uniformly for `t ∈ [0, T − a]`, and in every `Lᵖ`, `p < ∞`; the lattice
fields converge in law to the limits jointly over finitely many `(tᵢ, h₀ᵢ, φᵢ)`; and by time reversal the
limits have the joint law of `(ℋ_{T−tᵢ}(h₀ᵢ, φᵢ))ᵢ`. -/
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
  by exact Critical2DKPZ.Provider.thm_toy_joint ϑ P Z hZ T hT
end Critical2DKPZ

end

end
