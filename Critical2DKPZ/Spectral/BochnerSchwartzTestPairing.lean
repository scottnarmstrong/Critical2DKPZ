/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartzSchwartzExtension
public import Critical2DKPZ.Spectral.RadialMeasure
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Critical2DKPZ.Spectral.SchwartzKernelIntegrability

/-! # The spectral measure represents the two-test kernel pairing -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform

set_option linter.style.haveILetI false

namespace Critical2DKPZ.Spectral

/-- Taking the real part of the Fourier transform of a real compact test and transforming back
produces its even part. -/
theorem fourier_realPart_fourier_testFn (h : TestFn) (x : Plane) :
    ((𝓕 (realSchwartzToComplex
      (complexSchwartzRealPart (𝓕 (testFnToSchwartzMap h))))) x).re =
        (h x + h (-x)) / 2 := by
  let H : SchwartzMap Plane ℂ := testFnToSchwartzMap h
  let F : SchwartzMap Plane ℂ := 𝓕 H
  let φ : SchwartzMap Plane ℝ := complexSchwartzRealPart F
  have hfreq (ξ : Plane) :
      fourierKPZ (h : Plane → ℝ) ξ = F (angularFrequencyEquiv ξ) := by
    change fourierKPZ (h : Plane → ℝ) ξ = fourierKPZSchwartz h ξ
    exact (fourierKPZSchwartz_apply h ξ).symm
  have hfreqInv (x : Plane) :
      fourierKPZ (h : Plane → ℝ) (angularFrequencyEquiv.symm x) = F x := by
    rw [hfreq, angularFrequencyEquiv.apply_symm_apply]
  have hconj (x : Plane) : conj (F x) = F (-x) := by
    calc
      conj (F x) = conj (fourierKPZ (h : Plane → ℝ)
          (angularFrequencyEquiv.symm x)) := by rw [hfreqInv]
      _ = fourierKPZ (h : Plane → ℝ) (-(angularFrequencyEquiv.symm x)) :=
        (fourierKPZ_neg_eq_conj h (angularFrequencyEquiv.symm x)).symm
      _ = fourierKPZ (h : Plane → ℝ) (angularFrequencyEquiv.symm (-x)) := by
        congr 2
        simp
      _ = F (-x) := hfreqInv (-x)
  have hinv (x : Plane) : (𝓕⁻ H) x = F (-x) := by
    rw [SchwartzMap.fourierInv_apply_eq]
    rfl
  have hpart : realSchwartzToComplex φ =
      (2 : ℂ)⁻¹ • (F + 𝓕⁻ H) := by
    ext y
    change Complex.ofReal (F y).re = (2 : ℂ)⁻¹ * (F y + (𝓕⁻ H) y)
    rw [hinv, ← hconj]
    apply Complex.ext
    · simp [Complex.mul_re]
      norm_num
      ring_nf
    · simp [Complex.mul_im]
  have hdouble (y : Plane) : (𝓕 (𝓕 H)) y = (h (-y) : ℂ) := by
    calc
      (𝓕 (𝓕 H)) y = (𝓕⁻ (𝓕 H)) (-y) := by
        rw [SchwartzMap.fourierInv_apply_eq]
        simp
      _ = H (-y) := by
        have hInv : 𝓕⁻ (𝓕 H) = H := by simp
        exact congrArg (fun q : SchwartzMap Plane ℂ => q (-y)) hInv
      _ = (h (-y) : ℂ) := by simp [H]
  have hinvdouble (y : Plane) : (𝓕 (𝓕⁻ H)) y = (h y : ℂ) := by
    have hFourierInv : 𝓕 (𝓕⁻ H) = H := by simp
    rw [hFourierInv]
    simp [H]
  have htransform : 𝓕 (realSchwartzToComplex φ) =
      (2 : ℂ)⁻¹ • (𝓕 (𝓕 H) + 𝓕 (𝓕⁻ H)) := by
    simpa only [SchwartzMap.fourierTransformCLM_apply, map_smul, map_add] using
      congrArg (SchwartzMap.fourierTransformCLM ℂ) hpart
  change ((𝓕 (realSchwartzToComplex φ)) x).re = _
  rw [htransform, smul_apply, add_apply, hdouble, hinvdouble]
  norm_num
  ring

/-- The angular-frequency Riesz measure represents the difference-kernel pairing of two compact
tests. -/
theorem fourierKPZRieszMeasure_testFn_pairing (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ ψ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      ψ p.1 * ψ p.2 * C (p.1 - p.2))
    (f g : TestFn) :
    (∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) =
      ∫ ξ : Plane, (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re ∂
        fourierKPZRieszMeasure C hC hgrowth heven hpos := by
  let μ := fourierCccRieszMeasure C hC hgrowth heven hpos
  let ν := fourierKPZRieszMeasure C hC hgrowth heven hpos
  let h : TestFn := Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g
  let φ : SchwartzMap Plane ℝ :=
    complexSchwartzRealPart (𝓕 (testFnToSchwartzMap h))
  have hμloc : IsLocallyFiniteMeasure μ :=
    fourierCccRieszMeasure_isLocallyFinite C hC hgrowth heven hpos
  letI : IsLocallyFiniteMeasure μ := hμloc
  have hνloc : IsLocallyFiniteMeasure ν :=
    fourierKPZRieszMeasure_isLocallyFinite C hC hgrowth heven hpos
  letI : IsLocallyFiniteMeasure ν := hνloc
  have hνgrowth := fourierKPZRieszMeasure_polynomial_ball_growth C hC hgrowth heven hpos
  have hpairInt : Integrable
      (fun ξ : Plane => (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re) ν :=
    integrable_fourierKPZRealPair_of_polynomial_ball_growth ν hνgrowth f g
  have hpairPoint (ξ : Plane) :
      (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re =
        φ (angularFrequencyEquiv ξ) := by
    change (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re =
      (𝓕 (testFnToSchwartzMap h) (angularFrequencyEquiv ξ)).re
    rw [← fourierKPZ_testFnConvolution f g]
    have hbridge : fourierKPZ (h : Plane → ℝ) ξ =
        (𝓕 (testFnToSchwartzMap h)) (angularFrequencyEquiv ξ) := by
      change fourierKPZ (h : Plane → ℝ) ξ = fourierKPZSchwartz h ξ
      exact (fourierKPZSchwartz_apply h ξ).symm
    exact congrArg Complex.re hbridge
  have hmap :
      (∫ ξ : Plane, (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re ∂ν) =
        ∫ η : Plane, φ η ∂μ := by
    change (∫ ξ : Plane, (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re ∂
      (μ.map angularFrequencyEquiv.symm)) = _
    calc
      _ = ∫ η : Plane,
          (fourierKPZ f (angularFrequencyEquiv.symm η) *
            conj (fourierKPZ g (angularFrequencyEquiv.symm η))).re ∂μ :=
        integral_map angularFrequencyEquiv.symm.continuous.measurable.aemeasurable
          hpairInt.aestronglyMeasurable
      _ = ∫ η : Plane, φ η ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with η
        simpa only [angularFrequencyEquiv.apply_symm_apply] using
          hpairPoint (angularFrequencyEquiv.symm η)
  have hrepresentation :=
    fourierCccRieszMeasure_integral_schwartz C hC hgrowth heven hpos φ
  have hkernelFourierInt : Integrable
      (fun x : Plane => (C x : ℂ) * (𝓕 (realSchwartzToComplex φ)) x) volume :=
    integrable_kernel_mul_schwartz C hC hgrowth (𝓕 (realSchwartzToComplex φ))
  have hkernelAsSym :
      ((∫ x : Plane, (C x : ℂ) * (𝓕 (realSchwartzToComplex φ)) x).re) =
        ∫ x : Plane, C x * ((h x + h (-x)) / 2) := by
    calc
      ((∫ x : Plane, (C x : ℂ) * (𝓕 (realSchwartzToComplex φ)) x).re) =
          ∫ x : Plane, ((C x : ℂ) * (𝓕 (realSchwartzToComplex φ)) x).re :=
        (integral_re hkernelFourierInt).symm
      _ = ∫ x : Plane, C x * ((h x + h (-x)) / 2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Complex.mul_re, fourier_realPart_fourier_testFn h x]
        simp
  have hkernelInt : Integrable (fun x : Plane => h x * C x) volume :=
    integrable_testFn_kernel C hC h
  have hkernelReflectedInt : Integrable (fun x : Plane => C x * h (-x)) volume := by
    have hReflected := integrable_testFn_kernel C hC
      (Critical2DKPZ.Analysis.Sobolev.reflectedTestFn h)
    convert hReflected using 1
    funext x
    simp [mul_comm]
  have hkernelInt' : Integrable (fun x : Plane => C x * h x) volume := by
    convert hkernelInt using 1
    funext x
    ring
  have hreflectIntegral :
      (∫ x : Plane, C x * h (-x)) = ∫ x : Plane, C (-x) * h x := by
    let R : Plane ≃ₗᵢ[ℝ] Plane := LinearIsometryEquiv.neg ℝ
    let k : Plane → ℝ := fun x => C (-x) * h x
    calc
      (∫ x : Plane, C x * h (-x)) = ∫ x : Plane, k (R x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [k, R]
      _ = ∫ x : Plane, k x :=
        (LinearIsometryEquiv.measurePreserving R).integral_comp'
          (f := R.toMeasurableEquiv) k
      _ = ∫ x : Plane, C (-x) * h x := rfl
  have hevenIntegral :
      (∫ x : Plane, C (-x) * h x) = ∫ x : Plane, C x * h x := by
    have hEq : (fun x : Plane => C (-x) * h x) =ᵐ[volume]
        (fun x : Plane => C x * h x) := by
      filter_upwards [heven] with x hx
      simpa using congrArg (fun q : ℝ => q * h x) hx
    exact integral_congr_ae hEq
  have hkernelEvenPart :
      (∫ x : Plane, C x * ((h x + h (-x)) / 2)) = ∫ x : Plane, h x * C x := by
    have hsum : (fun x : Plane => C x * ((h x + h (-x)) / 2)) =
        fun x => (1 / 2 : ℝ) * (C x * h x + C x * h (-x)) := by
      funext x
      ring
    rw [hsum, integral_const_mul, integral_add hkernelInt' hkernelReflectedInt,
      hreflectIntegral, hevenIntegral]
    have hcomm : (∫ x : Plane, C x * h x) = ∫ x : Plane, h x * C x := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [hcomm]
    ring
  calc
    (∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) =
        ∫ x : Plane, h x * C x := by
          rw [integral_testFnProduct_kernel_eq_integral_testFnConvolution C hC f g]
    _ = ∫ ξ : Plane, (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re ∂ν := by
      rw [hmap]
      rw [fourier_kernelTemperedDistribution_apply_schwartz] at hrepresentation
      exact hkernelEvenPart.symm.trans (hkernelAsSym.symm.trans hrepresentation.symm)

/-- A real even locally square-integrable positive-type kernel with polynomial integral growth has a positive spectral measure in angular frequency. -/
theorem exists_spectralMeasure_of_positiveType (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      ∫ z in Metric.closedBall 0 R, |C z| ≤ A * R ^ k)
    (heven : (fun z => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ f : TestFn, 0 ≤ ∫ p : Plane × Plane,
      f p.1 * f p.2 * C (p.1 - p.2)) :
    ∃ ν : Measure Plane, IsLocallyFiniteMeasure ν ∧
      (∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
        (ν (Metric.closedBall 0 R)).toReal ≤ A * R ^ k) ∧
      (∀ R : Plane ≃ₗᵢ[ℝ] Plane,
        (fun z => C (R z)) =ᵐ[volume] C → ν.map R = ν) ∧
      ∀ f g : TestFn,
        ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2) =
          ∫ ξ, (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re ∂ν := by
  let ν := fourierKPZRieszMeasure C hC hgrowth heven hpos
  have hνloc : IsLocallyFiniteMeasure ν :=
    fourierKPZRieszMeasure_isLocallyFinite C hC hgrowth heven hpos
  have hνgrowth := fourierKPZRieszMeasure_polynomial_ball_growth C hC hgrowth heven hpos
  refine ⟨ν, hνloc, hνgrowth, ?_, ?_⟩
  · intro R hrot
    exact fourierKPZRieszMeasure_map_linearIsometry C hC hgrowth heven hpos R hrot
  · intro f g
    exact fourierKPZRieszMeasure_testFn_pairing C hC hgrowth heven hpos f g

end Critical2DKPZ.Spectral

end
