/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialInversionPairing
public import Critical2DKPZ.CovarianceKernel.RadialInversionAsymptotic

/-! # Spectral and spatial covariance pairings -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology ComplexConjugate

namespace Critical2DKPZ.CovarianceKernel

/-- Rotation averaging identifies the real spectral pairing with the Bessel-inversion kernel on a
test-function convolution. The local `L²` premise supplies integrability of the spatial pairing. -/
theorem spectralPairing_eq_besselInversion_testFnConvolution_of_logGrowth
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R →
      spectralBallMass ν R ≤ A * (1 + Real.log R))
    (hrot : ∀ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 → ν.map R = ν)
    (hC : ∀ K : Set Plane, IsCompact K →
      MemLp (besselInversion ν) 2 (volume.restrict K))
    (f g : TestFn) :
    Integrable (fun z : Plane =>
      Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g z * besselInversion ν z) volume ∧
    (∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) =
      ∫ z, Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g z *
        besselInversion ν z := by
  let q : TestFn := Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g
  let F : Plane → ℝ := Spectral.fourierKPZRealPairSchwartz f g
  have hFpair := integrable_fourierKPZRealPair_of_logGrowth ν hA hGrowth f g
  have hF : Integrable F ν := by
    apply hFpair.congr
    filter_upwards [] with ξ
    exact (Spectral.fourierKPZRealPairSchwartz_apply f g ξ).symm
  have hFpoint (ξ : Plane) : F ξ =
      (Spectral.fourierKPZ (q : Plane → ℝ) ξ).re := by
    simp [F, q, Spectral.fourierKPZRealPairSchwartz_apply,
      Spectral.fourierKPZ_testFnConvolution]
  have hFcontinuous : Continuous F := by
    dsimp [F]
    exact (Spectral.fourierKPZRealPairSchwartz f g).continuous
  have hjointMeas : Measurable (fun p : ℝ × Plane =>
      F (Spectral.planeRotation p.1 p.2)) := by
    apply hFcontinuous.measurable.comp
    fun_prop [Spectral.planeRotation]
  have hjoint : Integrable (fun p : ℝ × Plane =>
      F (Spectral.planeRotation p.1 p.2)) (Spectral.unitAngleMeasure.prod ν) := by
    apply (integrable_prod_iff hjointMeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with θ
      let R := Spectral.planeRotationLinearIsometryEquiv θ
      have hfun : (R : Plane → Plane) = Spectral.planeRotation θ := by
        funext ξ
        exact Spectral.planeRotationLinearIsometryEquiv_apply θ ξ
      have hmap : Measure.map (R : Plane → Plane) ν = ν := by
        rw [hfun]
        exact spectralMeasure_map_planeRotation_of_detInvariant ν hrot θ
      have hpres : MeasurePreserving (R : Plane → Plane) ν ν :=
        ⟨R.continuous.measurable, hmap⟩
      have hcomp : Integrable (fun ξ : Plane => F (R ξ)) ν :=
        hpres.integrable_comp_of_integrable hF
      have heq : (fun ξ : Plane => F (Spectral.planeRotation θ ξ)) =
          (fun ξ : Plane => F (R ξ)) := by
        funext ξ
        rw [← hfun]
      exact heq ▸ hcomp
    · have hnormF : Integrable (fun ξ : Plane => ‖F ξ‖) ν := hF.norm
      have hnormEq : (fun θ : ℝ =>
          ∫ ξ : Plane, ‖F (Spectral.planeRotation θ ξ)‖ ∂ν) =
          fun _ : ℝ => ∫ ξ : Plane, ‖F ξ‖ ∂ν := by
        funext θ
        exact integral_comp_planeRotation_of_detInvariant ν hrot hnormF θ
      rw [hnormEq]
      exact integrable_const _
  have haverage : (∫ ξ, F ξ ∂ν) =
      ∫ θ : ℝ, ∫ ξ : Plane, F (Spectral.planeRotation θ ξ) ∂ν
        ∂Spectral.unitAngleMeasure := by
    have hconstant :
        (∫ θ : ℝ, (∫ ξ : Plane, F ξ ∂ν) ∂Spectral.unitAngleMeasure) =
          ∫ ξ : Plane, F ξ ∂ν := by
      rw [integral_const]
      simp only [Measure.real, Spectral.unitAngleMeasure_univ, ENNReal.toReal_one, one_smul]
    calc
      (∫ ξ : Plane, F ξ ∂ν) =
          ∫ θ : ℝ, (∫ ξ : Plane, F ξ ∂ν) ∂Spectral.unitAngleMeasure := hconstant.symm
      _ = ∫ θ : ℝ, ∫ ξ : Plane, F (Spectral.planeRotation θ ξ) ∂ν
          ∂Spectral.unitAngleMeasure := by
        exact integral_congr_ae (μ := Spectral.unitAngleMeasure)
          (Filter.Eventually.of_forall fun θ =>
            (integral_comp_planeRotation_of_detInvariant ν hrot hF θ).symm)
  let B : ℝ := ∫ x : Plane, ‖q x‖
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun x => norm_nonneg (q x)
  have hFourierInt (ξ : Plane) : Integrable (fun θ : ℝ =>
      Spectral.fourierKPZ (q : Plane → ℝ) (Spectral.planeRotation θ ξ))
      Spectral.unitAngleMeasure := by
    have hmeas : Measurable (fun θ : ℝ =>
        Spectral.fourierKPZ (q : Plane → ℝ) (Spectral.planeRotation θ ξ)) := by
      have hrotMeas : Measurable (fun θ : ℝ => Spectral.planeRotation θ ξ) := by
        fun_prop [Spectral.planeRotation]
      have heq : (fun θ : ℝ =>
          Spectral.fourierKPZ (q : Plane → ℝ) (Spectral.planeRotation θ ξ)) =
          fun θ => Spectral.fourierKPZSchwartz q (Spectral.planeRotation θ ξ) := by
        funext θ
        exact (Spectral.fourierKPZSchwartz_apply q _).symm
      rw [heq]
      exact (Spectral.fourierKPZSchwartz q).continuous.measurable.comp hrotMeas
    have hconst : Integrable (fun _ : ℝ => B) Spectral.unitAngleMeasure :=
      integrable_const _
    apply hconst.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with θ
    have hbound := Spectral.norm_fourierKPZ_le q (Spectral.planeRotation θ ξ)
    simpa [B] using hbound
  have hangle (ξ : Plane) :
      (∫ θ : ℝ, F (Spectral.planeRotation θ ξ) ∂Spectral.unitAngleMeasure) =
        ∫ x : Plane, q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) := by
    calc
      (∫ θ : ℝ, F (Spectral.planeRotation θ ξ) ∂Spectral.unitAngleMeasure) =
          ∫ θ : ℝ,
            (Spectral.fourierKPZ (q : Plane → ℝ)
              (Spectral.planeRotation θ ξ)).re ∂Spectral.unitAngleMeasure := by
        apply integral_congr_ae
        filter_upwards [] with θ
        exact hFpoint (Spectral.planeRotation θ ξ)
      _ = (∫ θ : ℝ, Spectral.fourierKPZ (q : Plane → ℝ)
          (Spectral.planeRotation θ ξ) ∂Spectral.unitAngleMeasure).re :=
        integral_re (hFourierInt ξ)
      _ = ∫ x : Plane, q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) := by
        rw [integral_fourierKPZ_planeRotation_eq_bessel]
        simp
  have hBesselProd :=
    integrable_testFn_mul_besselJ0_product_of_logGrowth ν hA hGrowth q
  have hBesselProd' : Integrable (fun p : Plane × Plane =>
      q p.1 * Spectral.besselJ0Angular (‖p.1‖ * ‖p.2‖)) (volume.prod ν) := by
    apply hBesselProd.congr
    filter_upwards [] with p
    congr 1
    ring_nf
  have hspaceν :
      (∫ ξ : Plane, ∫ x : Plane,
        q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂volume ∂ν) =
      ∫ x : Plane, ∫ ξ : Plane,
        q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂ν ∂volume :=
    (integral_integral_swap hBesselProd').symm
  have hkernelInt : Integrable (fun x : Plane => q x * besselInversion ν x) volume :=
    Spectral.integrable_testFn_kernel (besselInversion ν) hC q
  have hkernelEq : ∀ᵐ x : Plane ∂volume,
      (∫ ξ : Plane, q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂ν) =
        q x * besselInversion ν x := by
    filter_upwards [Measure.ae_ne volume (0 : Plane)] with x hx
    have hJ := integrable_besselJ0_of_logGrowth ν hA hGrowth x hx
    calc
      (∫ ξ : Plane, q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂ν) =
          q x * ∫ ξ : Plane, Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂ν :=
        integral_const_mul (q x) _
      _ = q x * besselInversion ν x := by
        congr 1
        calc
          (∫ ξ : Plane, Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂ν) =
              ∫ ξ : Plane, Spectral.besselJ0Angular (‖ξ‖ * ‖x‖) ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            congr 1
            ring
          _ = besselInversion ν x :=
            (besselInversion_eq_integral_besselJ0 ν x hJ).symm
  refine ⟨hkernelInt, ?_⟩
  calc
    (∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) =
        ∫ ξ, F ξ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact (Spectral.fourierKPZRealPairSchwartz_apply f g ξ).symm
    _ = ∫ θ : ℝ, ∫ ξ : Plane,
        F (Spectral.planeRotation θ ξ) ∂ν ∂Spectral.unitAngleMeasure := haverage
    _ = ∫ ξ : Plane, ∫ θ : ℝ,
        F (Spectral.planeRotation θ ξ) ∂Spectral.unitAngleMeasure ∂ν :=
      integral_integral_swap hjoint
    _ = ∫ ξ : Plane, ∫ x : Plane,
        q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂volume ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact hangle ξ
    _ = ∫ x : Plane, ∫ ξ : Plane,
        q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) ∂ν ∂volume := hspaceν
    _ = ∫ x : Plane, q x * besselInversion ν x ∂volume := by
      apply integral_congr_ae
      exact hkernelEq


end Critical2DKPZ.CovarianceKernel

end
