/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.KPZModulusInputs
import Critical2DKPZ.Extensions.ScaleLimit.StationarySpectralTightness

/-! # The scale modulus for the flat critical KPZ field

The stationary spectral modulus applies to the literal KPZ scaled pairing.
All its spectral, finite-dimensional and moment hypotheses are supplied by
the previously proved input package.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The flat KPZ scale process has a uniform asymptotic modulus in probability. -/
theorem kpz_modulus
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (S : ℝ≥0) (hS : 0 < S) :
    ∀ η : ℝ, 0 < η → ∀ ρ : ℝ, 0 < ρ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℝ, ∀ L : Set.Ioi (0 : ℝ), L₀ ≤ (L : ℝ) →
        P {ω | ∃ s r : ScaleInterval S, dist (s : ℝ) (r : ℝ) ≤ δ ∧
          η < |scaledPairing (H t 0 ω) φ x L s - scaledPairing (H t 0 ω) φ x L r|}
          ≤ ENNReal.ofReal ρ := by
  obtain ⟨ν, hν, hfdd, hvar, hinc⟩ := exists_kpz_modulus_inputs ϑ P Z hZ H hH ht x φ hφ hφ1
  exact scale_modulus_of_stationary_spectral hν φ hφ hφ1 x hfdd hvar hinc S hS

end Critical2DKPZ.Extensions.ScaleLimit
