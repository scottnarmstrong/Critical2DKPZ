/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.WindowOscillation
public import Critical2DKPZ.Extensions.ScaleLimit.GaussianWindowModulus
public import Critical2DKPZ.Extensions.ScaleLimit.L2ErrorSum
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTail
import Mathlib.Tactic

/-! # Uniform spectral modulus of continuity in probability -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- Proposition 5.5: stationary spectral data and the source positive-time
Brownian limits and second moments imply a uniform modulus in probability.
The conclusion concerns the literal scaled pairing at every sample. -/
theorem scale_modulus_of_stationary_spectral (hD : StationarySpectralData P D ν)
    (φ : TestFn) (_hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hvar : ∀ s : ℝ, 0 < s → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, scaledPairing (D ω) φ x L s ^ 2 ∂P) atTop (𝓝 s))
    (hinc : ∀ s t : ℝ, 0 < s → s < t → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 (t - s)))
    (S : ℝ≥0) (hS : 0 < S) :
    ∀ η : ℝ, 0 < η → ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∃ L₀ : ℝ,
      ∀ L : Set.Ioi (0 : ℝ), L₀ ≤ (L : ℝ) →
        P {ω | ∃ s r : ScaleInterval S, dist (s : ℝ) (r : ℝ) ≤ δ ∧
          η < |scaledPairing (D ω) φ x L s - scaledPairing (D ω) φ x L r|} ≤ ENNReal.ofReal ρ := by
  obtain ⟨C, c, hC, hc, hwindow⟩ := window_oscillation hD φ hφ1 x hfdd hvar hinc
  intro η hη ρ hρ
  obtain ⟨δ, hδ, hevent⟩ := modulus_of_gaussian_window_bounds P
    (fun L r ω => scaledPairing (D ω) φ x L r) hC hc hwindow
    (show 0 < (S : ℝ) from hS) η hη ρ hρ
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hevent
  exact ⟨δ, hδ, (L₀ : ℝ), fun L hL => hL₀ L hL⟩

end Critical2DKPZ.Extensions.ScaleLimit
