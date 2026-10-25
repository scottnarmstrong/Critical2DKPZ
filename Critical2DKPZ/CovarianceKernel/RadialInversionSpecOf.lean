/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialInversionSpec
public import Critical2DKPZ.CovarianceKernel.RadialInversionNonneg
public import Critical2DKPZ.CovarianceKernel.WeakCovarianceKernelExistence

/-! # The covariance representation of Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate Topology

namespace Critical2DKPZ.CovarianceKernel

universe u

/-- The spectral Bessel inversion is the nonnegative, locally square-integrable covariance kernel,
with its tested covariance representation and sharp diagonal asymptotic. -/
theorem besselInversion_spec_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hC12 : LocalSobolev.ToyJointAt ϑ P Z) (hcov : SmallScales.FlatCovarianceAt P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (_hR7 : SmallScales.KpzTransportAt P H) (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H)
    {t : ℝ} (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hrot : ∀ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 → ν.map R = ν)
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    (∀ z, 0 ≤ besselInversion ν z) ∧ ContinuousOn (besselInversion ν) {0}ᶜ ∧
      (∀ K : Set Plane, IsCompact K → MemLp (besselInversion ν) 2 (volume.restrict K)) ∧
      (∀ f g : TestFn,
        cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
          ∫ p : Plane × Plane, f p.1 * g p.2 * besselInversion ν (p.1 - p.2)) ∧
      Tendsto (fun z => besselInversion ν z / Real.log (Real.log ‖z‖⁻¹))
        (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
  have hball := kpz_spectralMeasure_ball_asymp_of ϑ P Z hZ H hH hShrinkingVarianceInput ht ν hν
  obtain ⟨A, hA, hGrowth⟩ := spectralBallMass_logGrowth_of_tendsto ν hball
  have hregular := besselInversion_regular_of_spectralMeasure
    ϑ P Z hZ H hH hShrinkingVarianceInput ht ν hν
  obtain ⟨C, hCmem, hCnonneg, _heven, _hrotation, _hbound, hCrep⟩ :=
    exists_kpz_covKernel_base_of ϑ P Z hZ hsym hrevL hC12 hcov H hH ht
  have hpair : ∀ f g : TestFn,
      (∫ z : Plane,
        Analysis.Sobolev.testFnConvolution f g z * besselInversion ν z) =
        ∫ z : Plane, Analysis.Sobolev.testFnConvolution f g z * C z := by
    intro f g
    have hB := spectralPairing_eq_besselInversion_testFnConvolution_of_logGrowth
      ν hA hGrowth hrot hregular.2.1 f g
    calc
      (∫ z : Plane, Analysis.Sobolev.testFnConvolution f g z * besselInversion ν z) =
          ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν := hB.2.symm
      _ = cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] := (hν f g).symm
      _ = ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2) := hCrep f g
      _ = ∫ z : Plane, Analysis.Sobolev.testFnConvolution f g z * C z :=
        Spectral.integral_testFnProduct_kernel_eq_integral_testFnConvolution C hCmem f g
  have hBnonnegOffZero : ∀ z : Plane, z ≠ 0 → 0 ≤ besselInversion ν z :=
    continuousOn_nonneg_of_testFnConvolution_pairing (besselInversion ν) C
      hregular.1 hregular.2.1 hCmem hCnonneg hpair
  have hBnonneg : ∀ z : Plane, 0 ≤ besselInversion ν z := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact besselInversion_nonneg_at_zero ν
    · exact hBnonnegOffZero z hz
  refine ⟨hBnonneg, hregular.1, hregular.2.1, ?_, hregular.2.2⟩
  intro f g
  have hB := spectralPairing_eq_besselInversion_testFnConvolution_of_logGrowth
    ν hA hGrowth hrot hregular.2.1 f g
  calc
    cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν := hν f g
    _ = ∫ z : Plane, Analysis.Sobolev.testFnConvolution f g z * besselInversion ν z := hB.2
    _ = ∫ p : Plane × Plane, f p.1 * g p.2 * besselInversion ν (p.1 - p.2) :=
      (Spectral.integral_testFnProduct_kernel_eq_integral_testFnConvolution
        (besselInversion ν) hregular.2.1 f g).symm

/-- The moment, symmetry, convergence and shrinking-variance assumptions imply the covariance-kernel representation and diagonal asymptotic of Theorem 1.4(ii). -/
theorem criticalKPZ_covarianceKernel_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hC12 : LocalSobolev.ToyJointAt ϑ P Z) (hcov : SmallScales.FlatCovarianceAt P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hR7 : SmallScales.KpzTransportAt P H) (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : Plane → ℝ, (∀ z, 0 ≤ C z) ∧ (∀ z w, ‖z‖ = ‖w‖ → C z = C w) ∧
      (∀ K, IsCompact K → MemLp C 2 (volume.restrict K)) ∧ ContinuousOn C {0}ᶜ ∧
      (∀ f g : TestFn, cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) ∧
      Tendsto (fun z => C z / Real.log (Real.log ‖z‖⁻¹))
        (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  obtain ⟨ν, hνloc, hνrot, hν⟩ :=
    exists_kpz_spectralMeasure_of ϑ P Z hZ hsym hrevL hC12 hcov H hH hR7 ht
  obtain ⟨hnonneg, hcont, hmem, hcovariance, hasym⟩ :=
    besselInversion_spec_of ϑ P Z hZ hsym hrevL hC12 hcov H hH hR7 hShrinkingVarianceInput ht ν hνrot hν
  refine ⟨besselInversion ν, hnonneg, ?_, hmem, hcont, hcovariance, hasym⟩
  intro z w hnorm
  exact besselInversion_eq_of_norm ν hnorm

end Critical2DKPZ.CovarianceKernel

end
