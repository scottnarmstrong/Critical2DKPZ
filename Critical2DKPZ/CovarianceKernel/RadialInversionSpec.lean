/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialInversionLp
public import Critical2DKPZ.CovarianceKernel.SpectralMeasure
public import Critical2DKPZ.CovarianceKernel.BallAsymptotic

/-! # Regularity consequences for the KPZ Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate Topology

namespace Critical2DKPZ.CovarianceKernel

universe u

/-- Spectral-mass squeeze and logarithmic spectral growth give continuity away from zero, local square
integrability, and the sharp diagonal asymptotic for the Bessel inversion. -/
theorem besselInversion_regular_of_spectralMeasure
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) {t : ℝ} (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    ContinuousOn (besselInversion ν) {0}ᶜ ∧
      (∀ K : Set Plane, IsCompact K →
        MemLp (besselInversion ν) 2 (volume.restrict K)) ∧
      Tendsto (fun z => besselInversion ν z /
        Real.log (Real.log ‖z‖⁻¹)) (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
  have hM := kpz_spectralMeasure_ball_asymp_of ϑ P Z hZ H hH hShrinkingVarianceInput ht ν hν
  obtain ⟨A, hA, hGrowth⟩ := spectralBallMass_logGrowth_of_tendsto ν hM
  exact ⟨continuousOn_besselInversion_of_logGrowth ν hA hGrowth,
    (fun K hK => besselInversion_memLp_two_on_compact_of_ballMass ν hM K hK),
    besselInversion_diagonal_asymptotic_of_ballMass ν hM⟩

end Critical2DKPZ.CovarianceKernel

end
