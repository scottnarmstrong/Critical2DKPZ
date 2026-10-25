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
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsEhrhardType
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Provider.ShfSymmetries

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **symmetries and regularity of the SHF** used by the KPZ proofs (§1.3, §5,
§6.2, §3.4): an SHF stays an SHF under (i) spatial translations, (ii) rotations,
(iii) time shifts, and (iv) diffusive scaling with `ϑ ↦ ϑ + log a`; (v) time reversal on `[0, T]` preserves
the law of finitely many pairings; (vi) pairings are continuous in probability in `(s, t)`;
(vii) pairings of a heat kernel with `e^{h₀}` are a.s. positive with logarithm of Ehrhard type. -/
theorem shf_symmetries (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    (∀ z : Plane, IsCriticalSHF ϑ P fun s t ω => (Z s t ω).map fun p => (p.1 + z, p.2 + z)) ∧
    (∀ R : Plane ≃ₗᵢ[ℝ] Plane, LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
      IsCriticalSHF ϑ P fun s t ω => (Z s t ω).map fun p => (R p.1, R p.2)) ∧
    (∀ u : ℝ, 0 ≤ u → IsCriticalSHF ϑ P fun s t ω => Z (s + u) (t + u) ω) ∧
    (∀ a : ℝ, 0 < a → IsCriticalSHF (ϑ + Real.log a) P fun s t ω =>
      ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)) ∧
    (∀ (T : ℝ) (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      ∀ φ : Fin k → C_c(Plane × Plane, ℝ),
        P.map (fun ω i => ∫ p, φ i (p.2, p.1) ∂(Z (T - t i) (T - s i) ω)) =
          P.map (fun ω i => ∫ p, φ i p ∂(Z (s i) (t i) ω))) ∧
    (∀ (φ : C_c(Plane × Plane, ℝ)) (s t : ℝ), 0 ≤ s → s < t →
      TendstoInMeasure P (fun (q : ℝ × ℝ) ω => ∫ p, φ p ∂(Z q.1 q.2 ω))
        (nhdsWithin (s, t) {q | 0 ≤ q.1 ∧ q.1 < q.2}) (fun ω => ∫ p, φ p ∂(Z s t ω))) ∧
    (∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P ∧
      IsEhrhardType (P.map fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))) :=
  by exact Critical2DKPZ.Provider.shf_symmetries ϑ P Z hZ
end Critical2DKPZ

end

end
