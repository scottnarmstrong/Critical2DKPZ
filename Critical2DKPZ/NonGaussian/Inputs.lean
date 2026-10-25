/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Basic
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.SmallScales.Inputs
public import Critical2DKPZ.SHF.Tsai.Defs

/-! # Endpoint limits and SHF properties on countable sets of times -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- A deterministic subprobability subsequential limit of averaged endpoint pairings
under Gaussianity of a tested KPZ field. -/
def EndpointLimitAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) : Prop :=
  ∀ ⦃t : ℝ⦄, 0 < t → ∀ ψ : TestFn, (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 →
    (∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v) →
  ∃ (μ : Measure Plane) (r : ℕ → ℝ), IsFiniteMeasure μ ∧ μ Set.univ ≤ 1 ∧
      Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)) ∧ ∀ φ : C_c(Plane, ℝ),
        Tendsto (fun n => ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x φ ω) - ∫ y, φ y ∂μ| ∂P)
          atTop (𝓝 0)

/-- Tsai’s SHF axioms on every countable set of nonnegative times. -/
def DenseSHFAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ D : Set ℝ, D.Countable → (∀ s ∈ D, 0 ≤ s) →
    SHF.Tsai.IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z

end Critical2DKPZ.NonGaussian

end
