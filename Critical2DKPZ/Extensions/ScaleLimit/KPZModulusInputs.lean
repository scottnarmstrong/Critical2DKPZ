/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.KPZSpectralData
public import Critical2DKPZ.Extensions.ScaleLimit.FiniteDimensional
public import Critical2DKPZ.Extensions.ScaleLimit.L2Replacements

/-! # The KPZ inputs of the stationary spectral modulus theorem

The flat KPZ distribution satisfies the stationary spectral hypotheses,
Brownian finite-dimensional limits and moment limits used in Proposition 5.5
at every positive observation time and every spatial center.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The stationary spectral package, Brownian finite-dimensional convergence,
and the one-time and increment moment limits needed by the spectral modulus. -/
theorem exists_kpz_modulus_inputs
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) :
    ∃ ν : Measure Plane, StationarySpectralData P (H t 0) ν ∧
      (∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) →
        TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
          scaledPairing (H t 0 ω) φ x L (i.1 : ℝ)) atTop id (fun _ => P)
          (BrownianReal.projectiveFamily I)) ∧
      (∀ s : ℝ, 0 < s →
        Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω, scaledPairing (H t 0 ω) φ x L s ^ 2 ∂P)
          atTop (𝓝 s)) ∧
      (∀ u v : ℝ, 0 < u → u < v →
        Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω,
          (scaledPairing (H t 0 ω) φ x L v - scaledPairing (H t 0 ω) φ x L u) ^ 2 ∂P)
          atTop (𝓝 (v - u))) := by
  obtain ⟨ν, hν⟩ := exists_stationary_spectral_data ϑ P Z hZ H hH t ht
  refine ⟨ν, hν, fun I _ => ?_, fun s hs => ?_, fun u v hu huv => ?_⟩
  · exact kpz_scale_finiteDimensional_tendstoInDistribution ϑ P Z hZ H hH ht x φ hφ hφ1 I
  · exact tendsto_second_moment_scaled ϑ P Z hZ H hH t ht φ hφ hφ1 x hs
  · simpa only [abs_of_pos (sub_pos.mpr huv)] using
      tendsto_second_moment_increment ϑ P Z hZ H hH t ht φ hφ hφ1 x (hu.trans huv) hu

end Critical2DKPZ.Extensions.ScaleLimit
