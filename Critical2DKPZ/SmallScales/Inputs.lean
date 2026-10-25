/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.TestFnCompAffine
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Smoothing.Basic
import Mathlib.Probability.Moments.Covariance

/-! # Small-scale logarithmic, smoothing and symmetry properties -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- Small-scale logarithmic normality holds for centered heat-start pairings of every critical stochastic heat flow on a probability space in `Type u`. -/
def SmallScaleSHFLogNormality : Prop :=
  ∀ (ϑ : ℝ) ⦃Ω : Type u⦄ [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF ϑ P Z → ∀ x : Plane,
  TendstoInDistribution
      (fun (ε : Set.Ioo (0 : ℝ) 1) ω =>
        (Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
            (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω) -
          ∫ ω', Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
            (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω') ∂P) /
          Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹)))
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) id (fun _ => P) (gaussianReal 0 1)

/-- The lattice smoothing error has a uniform second-moment norm bound in terms of heat energy and the test function's integral. -/
def LatticeSmoothingErrorEnergy : Prop :=
  ∀ A H : ℝ,
  ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
      Integrable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) → ∀ c₀ c₁ : ℝ, 0 < c₀ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ M : ℕ in atTop, Even M → ∀ c ∈ Set.Icc c₀ c₁,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ j k : ℕ, Even j → Even k →
        (j : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ j + 6 →
        (k : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ k + 6 →
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
          eLpNorm (Smoothing.latticeSmoothingError (criticalBeta ϑ M) M M k j h₀
              (fun y => c * φ (Real.sqrt c • y))) 2 disorderLaw ≤
            ENNReal.ofReal (Real.sqrt
                (C * Smoothing.heatEnergy (Real.sqrt δ) (fun y => c * φ (Real.sqrt c • y)) /
                  |Real.log δ|) +
              C * (∫ x, |c * φ (Real.sqrt c • x)|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε)

/-- Finite collections of test pairings are almost everywhere measurable and have laws invariant under translations and orientation-preserving rotations. -/
def KpzTransportAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) : Prop :=
  ∀ (k : ℕ) (t : Fin k → ℝ), (∀ i, 0 < t i) → ∀ φ : Fin k → TestFn,
    (∀ i, AEMeasurable (fun ω => H (t i) 0 ω (φ i)) P) ∧
      (∀ (z : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane),
        LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
          P.map (fun ω i => H (t i) 0 ω ((φ i).compAffine z R)) =
            P.map (fun ω i => H (t i) 0 ω (φ i)))

/-- Regularized flat fields have finite second moments and nonnegative covariances bounded by a double logarithm of inverse separation. -/
def FlatCovarianceAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ ⦃t₀ t₁ : ℝ⦄, 0 < t₀ →
  ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ δ δ' : ℝ,
    0 < δ → δ < t / 2 → 0 < δ' → δ' < t / 2 → ∀ x y : Plane, x ≠ y →
      MemLp (kpzRegularized P Z t δ 0 x) 2 P ∧
        0 ≤ covariance (kpzRegularized P Z t δ 0 x) (kpzRegularized P Z t δ' 0 y) P ∧
        covariance (kpzRegularized P Z t δ 0 x) (kpzRegularized P Z t δ' 0 y) P ≤
          C * (1 + Real.log (1 + max 0 (Real.log ‖x - y‖⁻¹)))

/-- Unit-mass nonnegative test pairings have finite second moments at small scales and variance asymptotic to the double logarithm of inverse scale. -/
def ShrinkingVarianceAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) : Prop :=
  ∀ ⦃t : ℝ⦄, 0 < t → ∀ φ : TestFn, (∀ y, 0 ≤ φ y) → ∫ y, φ y = 1 → ∀ x : Plane,
    (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), MemLp (fun ω => H t 0 ω (φ.dilate ε x)) 2 P) ∧
      Tendsto
        (fun ε => Var[fun ω => H t 0 ω (φ.dilate ε x); P] / Real.log (Real.log ε⁻¹))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1)

/-- Finite-dimensional measure laws are invariant under simultaneous time reversal and exchange of spatial endpoints. -/
def ShfReversalLawAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ T : ℝ, ∀ (k : ℕ) (s t : Fin k → ℝ),
    (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      P.map (fun ω i => (Z (T - t i) (T - s i) ω).map Prod.swap) =
        P.map (fun ω i => Z (s i) (t i) ω)

/-- Heat-start pairings have finite second moments bounded by one plus a constant times the logarithm of inverse smoothing time. -/
def HeatStartSqAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ ⦃τ₀ τ₁ : ℝ⦄, 0 < τ₀ →
  ∃ C δ₀ : ℝ, 0 < δ₀ ∧
    ∀ s T δ : ℝ, 0 ≤ s → τ₀ ≤ T - s → T - s ≤ τ₁ → 0 < δ → δ ≤ δ₀ → ∀ x : Plane,
      MemLp (fun ω => shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) 2 P ∧
        ∫ ω, shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω ^ 2 ∂P ≤
          1 + C * Real.log δ⁻¹

end Critical2DKPZ.SmallScales
