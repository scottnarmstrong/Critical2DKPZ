/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.SHF.Moments.PairingFubini

/-! # Polymer random measures and their subsequential limits

The limit condition requires joint convergence of compact and flat pairings at finitely many time pairs. -/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology

noncomputable section

namespace Critical2DKPZ.SHF.Limit

/-- The rescaled point-to-point partition function defines a random measure on the product plane. -/
def polymerMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder) : Measure (Plane × Plane) :=
  (volume : Measure (Plane × Plane)).withDensity fun p =>
    ENNReal.ofReal (rescaledP2P ϑ N s t p ω)

/-- `Z` is a limit, along the subsequence `ψ`, of the polymer measures on the strict pairs of `D`:
compact pairings and flat pairings converge jointly in law. -/
def IsPolymerSubseqLimit (ϑ : ℝ) (D : Set ℝ) (ψ : ℕ → ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  (∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z s t) ∧
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s t ω) ∧
      IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst)) ∧
  ∀ (k : ℕ) (s t : Fin k → ℝ),
    (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
    ∀ (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)),
      TendstoInDistribution
        (fun (n : ℕ) (ω : Disorder) (i : Fin k) =>
          ((∫ p, φ i p ∂(polymerMeasure ϑ (ψ n) (s i) (t i) ω)),
           (∫ x, χ i x ∂((polymerMeasure ϑ (ψ n) (s i) (t i) ω).map Prod.fst))))
        atTop
        (fun ω i =>
          ((∫ p, φ i p ∂(Z (s i) (t i) ω)),
           (∫ x, χ i x ∂((Z (s i) (t i) ω).map Prod.fst))))
        (fun _ => disorderLaw) P

end Critical2DKPZ.SHF.Limit

end
