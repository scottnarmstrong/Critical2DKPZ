/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralData
public import Critical2DKPZ.Extensions.ScaleLimit.Centring
public import Critical2DKPZ.Spectral.FourierMeasurePairing
import Critical2DKPZ.Provider.CriticalKPZCovarianceKernel
import Critical2DKPZ.CovarianceKernel.BallAsymptotic
import Critical2DKPZ.CovarianceKernel.RadialInversion
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Spectral hypotheses at every positive observation time

The main spectral representation and ball asymptotic already hold for every
positive time. Centring turns the covariance pairing into a second-moment pairing.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction ComplexConjugate

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Every flat critical KPZ field has the spectral data of Proposition 5.5. -/
theorem exists_spectral_data (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) :
    ∃ ν : Measure Plane, IsLocallyFiniteMeasure ν ∧
      (∀ f : TestFn, MemLp (Spectral.fourierKPZ f) 2 ν) ∧
      (∀ f g : TestFn, (∫ ω, H t 0 ω f * H t 0 ω g ∂P) =
        ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν) ∧
      Tendsto (fun R : ℝ => (ν (Metric.closedBall (0 : Plane) R)).toReal /
        Real.log (Real.log R)) atTop (𝓝 1) := by
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  have hrev := Assembly.shfReversalLawAt_of_isCriticalSHF ϑ P Z hZ
  have htoy := Assembly.toyJointAt_of_isCriticalSHF ϑ P Z hZ
  have hcov := Assembly.flatCovarianceAt_of ϑ P Z hZ hsym
  have htransport := Assembly.kpzTransportAt_of ϑ P Z hZ hsym H hH
  obtain ⟨ν, hν, _hrot, hpair⟩ := CovarianceKernel.exists_kpz_spectralMeasure_of
    ϑ P Z hZ hsym hrev htoy hcov H hH htransport ht
  let : IsLocallyFiniteMeasure ν := hν
  have hshrink : SmallScales.ShrinkingVarianceAt P H :=
    fun _ ht φ hφ hφmass x => SmallScales.kpz_shrinking_variance_of ϑ P Z hZ hsym
      Assembly.small_scale_shf_log_normality htoy
      (Assembly.heatStartLogAt_of_isCriticalSHF ϑ P Z hZ)
      (Assembly.heatStartLogFieldAt_of_isCriticalSHF ϑ P Z hZ)
      Assembly.latticeSmoothingErrorEnergy H hH ht φ hφ hφmass x
  have hmass := CovarianceKernel.kpz_spectralMeasure_ball_asymp_of
    ϑ P Z hZ H hH hshrink ht ν hpair
  obtain ⟨A, hA, hbound⟩ := CovarianceKernel.spectralBallMass_logGrowth_of_tendsto ν hmass
  have hpoly : ∃ (B : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (ν (Metric.closedBall (0 : Plane) R)).toReal ≤ B * R ^ k := by
    refine ⟨A, 1, ?_⟩
    intro R hR
    have hlog : 1 + Real.log R ≤ R := by
      have hh := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hR)
      linarith only [hh]
    exact (hbound R hR).trans (by simpa only [pow_one] using mul_le_mul_of_nonneg_left hlog hA)
  refine ⟨ν, hν, ?_, ?_, hmass⟩
  · intro f
    have hstrong : AEStronglyMeasurable (Spectral.fourierKPZ f) ν := by
      apply (Spectral.fourierKPZSchwartz f).continuous.aestronglyMeasurable.congr
      exact Eventually.of_forall (Spectral.fourierKPZSchwartz_apply f)
    apply (memLp_two_iff_integrable_sq_norm hstrong).mpr
    have hi := Spectral.integrable_fourierKPZRealPair_of_polynomial_ball_growth ν hpoly f f
    apply hi.congr
    filter_upwards [] with ξ
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  · intro f g
    exact (integral_mul_kpz_eq_covariance ϑ P Z hZ H hH t ht f g).trans (hpair f g)

/-- All finite families of flat tested fields are stationary under spatial translations. -/
theorem criticalKPZ_stationary (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (n : ℕ) (f : Fin n → TestFn) (z : Plane) :
    IdentDistrib (fun ω i => H t 0 ω ((f i).dilate 1 z)) (fun ω i => H t 0 ω (f i)) P P := by
  have hsym := Assembly.shfSymmetriesAt ϑ P Z hZ
  have htransport := Assembly.kpzTransportAt_of ϑ P Z hZ hsym H hH
  let e := LinearIsometryEquiv.refl ℝ Plane
  have hdet : LinearMap.det (e.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
    change LinearMap.det (LinearMap.id : Plane →ₗ[ℝ] Plane) = 1
    exact LinearMap.det_id
  have heq (g : TestFn) : g.dilate 1 z = g.compAffine (-z) e := by
    apply TestFunction.ext
    intro y
    change (1 : ℝ)⁻¹ ^ 2 * g ((1 : ℝ)⁻¹ • (y - z)) = g (-z + y)
    rw [inv_one, one_pow, one_smul, one_mul]
    exact congrArg g (by abel)
  refine ⟨aemeasurable_pi_iff.mpr (fun i =>
      (memLp_kpz_two ϑ P Z hZ H hH t ht ((f i).dilate 1 z)).aemeasurable),
    aemeasurable_pi_iff.mpr (fun i =>
      (memLp_kpz_two ϑ P Z hZ H hH t ht (f i)).aemeasurable), ?_⟩
  simpa only [← heq] using (htransport n (fun _ => t) (fun _ => ht) f).2 (-z) e hdet

/-- The full stationary spectral package used by the spectral modulus and path-law convergence. -/
theorem exists_stationary_spectral_data (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) :
    ∃ ν : Measure Plane, StationarySpectralData P (H t 0) ν := by
  obtain ⟨ν, hν, hf, hiso, hmass⟩ := exists_spectral_data ϑ P Z hZ H hH t ht
  exact ⟨ν, {
    memLp := memLp_kpz_two ϑ P Z hZ H hH t ht
    mean := integral_kpz_eq_zero ϑ P Z hZ H hH t ht
    stationary := criticalKPZ_stationary ϑ P Z hZ H hH t ht
    locFin := hν
    fourier_memLp := hf
    isometry := hiso
    ballAsymp := hmass }⟩

end Critical2DKPZ.Extensions.ScaleLimit
