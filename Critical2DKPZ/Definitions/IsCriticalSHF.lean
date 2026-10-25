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
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.RescaledP2P
public import Critical2DKPZ.Definitions.RescaledP2Plane

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- `Z` is a **Critical 2D Stochastic Heat Flow** with parameter `ϑ` on `(Ω, P)`: for `0 ≤ s < t`,
`Z s t` is a random measure on `ℝ² × ℝ²` which, almost surely, is locally finite and has a locally
finite first marginal `Z_{s,t}(dx, ℝ²)`; and for every finite family of pairs
`0 ≤ sᵢ < tᵢ` and test functions `φᵢ ∈ C_c(ℝ² × ℝ²)`, `ψᵢ ∈ C_c(ℝ²)`, the pairings of the rescaled
polymer partition functions (point-to-point and point-to-plane together) converge jointly in law to
the pairings
`(∫ φᵢ dZ_{sᵢ,tᵢ}, ∫ ψᵢ(x) Z_{sᵢ,tᵢ}(dx, ℝ²))` (Theorem A, §1.1). Its existence is Theorem A. -/
def IsCriticalSHF (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  (∀ s t, 0 ≤ s → s < t → Measurable (Z s t)) ∧
  (∀ s t, 0 ≤ s → s < t → ∀ᵐ ω ∂P,
    IsLocallyFiniteMeasure (Z s t ω) ∧ IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst)) ∧
  ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i) →
    ∀ (φ : Fin k → C_c(Plane × Plane, ℝ)) (ψ : Fin k → C_c(Plane, ℝ)),
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ((∫ p, φ i p * rescaledP2P ϑ N (s i) (t i) p ω),
           (∫ x, ψ i x * rescaledP2Plane ϑ N (s i) (t i) x ω)))
        atTop
        (fun ω i => ((∫ p, φ i p ∂(Z (s i) (t i) ω)),
                     (∫ x, ψ i x ∂((Z (s i) (t i) ω).map Prod.fst))))
        (fun _ => disorderLaw) P

end Critical2DKPZ

end

end
