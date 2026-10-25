/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialInversion
public import Critical2DKPZ.Spectral.FourierConvention
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Critical2DKPZ.Spectral.RadialMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Integrability for the Bessel inversion pairing -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology ComplexConjugate

namespace Critical2DKPZ.CovarianceKernel

/-- The coordinate rotation used in radial averaging has determinant one. -/
theorem planeRotationLinearIsometryEquiv_det (θ : ℝ) :
    LinearMap.det
      ((Spectral.planeRotationLinearIsometryEquiv θ).toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
  let b : Module.Basis (Fin 2) ℝ Plane := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hmatrix : LinearMap.toMatrix b b (Spectral.planeRotationLinearMap θ) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, b, Spectral.planeRotationLinearMap,
        Spectral.planeRotation, EuclideanSpace.basisFun_toBasis]
  have hdetMatrix : Matrix.det
      (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [Matrix.det_fin_two_of]
    calc
      Real.cos θ * Real.cos θ - -Real.sin θ * Real.sin θ =
          Real.cos θ ^ 2 + Real.sin θ ^ 2 := by ring
      _ = 1 := by rw [add_comm, Real.sin_sq_add_cos_sq]
  have hdetMap : LinearMap.det (Spectral.planeRotationLinearMap θ) = 1 := by
    calc
      LinearMap.det (Spectral.planeRotationLinearMap θ) =
          Matrix.det (LinearMap.toMatrix b b (Spectral.planeRotationLinearMap θ)) :=
        (LinearMap.det_toMatrix b _).symm
      _ = 1 := by rw [hmatrix, hdetMatrix]
  change LinearMap.det (Spectral.planeRotationLinearMap θ) = 1
  exact hdetMap

/-- The determinant-one invariance hypothesis makes the spectral measure invariant under the
coordinate rotations used in the angular Bessel average. -/
theorem spectralMeasure_map_planeRotation_of_detInvariant (ν : Measure Plane)
    (hrot : ∀ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 → ν.map R = ν)
    (θ : ℝ) : Measure.map (Spectral.planeRotation θ) ν = ν := by
  let R := Spectral.planeRotationLinearIsometryEquiv θ
  have hfun : (Spectral.planeRotation θ : Plane → Plane) = (R : Plane → Plane) := by
    funext x
    exact (Spectral.planeRotationLinearIsometryEquiv_apply θ x).symm
  rw [hfun]
  exact hrot R (planeRotationLinearIsometryEquiv_det θ)

/-- Integrals against a rotation-invariant spectral measure are unchanged by the coordinate
rotations. -/
theorem integral_comp_planeRotation_of_detInvariant (ν : Measure Plane)
    (hrot : ∀ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 → ν.map R = ν)
    {F : Plane → ℝ} (hF : Integrable F ν) (θ : ℝ) :
    (∫ ξ, F (Spectral.planeRotation θ ξ) ∂ν) = ∫ ξ, F ξ ∂ν := by
  have hmap := spectralMeasure_map_planeRotation_of_detInvariant ν hrot θ
  have hmeas : Measurable (Spectral.planeRotation θ) := by
    let R := Spectral.planeRotationLinearIsometryEquiv θ
    have hfun : (Spectral.planeRotation θ : Plane → Plane) = (R : Plane → Plane) := by
      funext x
      exact (Spectral.planeRotationLinearIsometryEquiv_apply θ x).symm
    rw [hfun]
    exact R.continuous.measurable
  have hFmap : AEStronglyMeasurable F (Measure.map (Spectral.planeRotation θ) ν) := by
    rw [hmap]
    exact hF.aestronglyMeasurable
  calc
    (∫ ξ, F (Spectral.planeRotation θ ξ) ∂ν) =
        ∫ ξ, F ξ ∂Measure.map (Spectral.planeRotation θ) ν := by
      symm
      exact integral_map hmeas.aemeasurable hFmap
    _ = ∫ ξ, F ξ ∂ν := by rw [hmap]

/-- The angular average of a plane wave along a rotated frequency is its order-zero Bessel value. -/
theorem integral_exp_planeRotation_inner (x ξ : Plane) :
    (∫ θ : ℝ, Complex.exp
      (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))
      ∂Spectral.unitAngleMeasure) =
      Complex.ofReal (Spectral.besselJ0Angular (‖x‖ * ‖ξ‖)) := by
  let A : ℝ := x 0 * ξ 0 + x 1 * ξ 1
  let B : ℝ := -x 0 * ξ 1 + x 1 * ξ 0
  let X : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I
  let Y : ℂ := (ξ 0 : ℂ) + (ξ 1 : ℂ) * Complex.I
  have hinner (θ : ℝ) :
      inner ℝ x (Spectral.planeRotation θ ξ) = A * Real.cos θ + B * Real.sin θ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [A, B, Spectral.planeRotation, dotProduct, Fin.sum_univ_succ]
    ring
  have hAB : (A : ℂ) + (B : ℂ) * Complex.I = X * conj Y := by
    apply Complex.ext
    · simp [A, B, X, Y, Complex.mul_re]
    · simp [A, B, X, Y, Complex.mul_im]
  have hX : ‖X‖ = ‖x‖ := by
    dsimp [X]
    rw [Complex.norm_add_mul_I, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, sq_abs]
  have hY : ‖Y‖ = ‖ξ‖ := by
    dsimp [Y]
    rw [Complex.norm_add_mul_I, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_succ, sq_abs]
  have hnormAB : ‖(A : ℂ) + (B : ℂ) * Complex.I‖ = ‖x‖ * ‖ξ‖ := by
    rw [hAB, norm_mul, Complex.norm_conj, hX, hY]
  have hInt : Integrable (fun θ : ℝ => Complex.exp
      (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ))))
      Spectral.unitAngleMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (by fun_prop [Spectral.planeRotation] : Measurable _).aestronglyMeasurable
    · filter_upwards [] with θ
      have hphase :
          -(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) =
            (-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) * Complex.I := by
        ring
      rw [hphase]
      calc
        ‖Complex.exp ((-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) * Complex.I)‖ = 1 := by
          simpa only [Complex.ofReal_neg] using
            (Complex.norm_exp_ofReal_mul_I
              (-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))
        _ ≤ 1 := le_rfl
  have hcoef : (ENNReal.ofReal ((2 * Real.pi)⁻¹)).toReal = (2 * Real.pi)⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    positivity
  have hcos : (∫ θ : ℝ, Real.cos
      (inner ℝ x (Spectral.planeRotation θ ξ)) ∂Spectral.unitAngleMeasure) =
      Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) := by
    simp_rw [Spectral.unitAngleMeasure, integral_smul_measure]
    simp_rw [← intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := 2 * Real.pi)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [hcoef]
    calc
      (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.cos (inner ℝ x (Spectral.planeRotation θ ξ)) =
          Real.circleAverage (fun z : ℂ => Real.cos (A * z.re + B * z.im)) 0 1 := by
        rw [Real.circleAverage_def]
        congr 1
        apply intervalIntegral.integral_congr
        intro θ hθ
        change Real.cos (inner ℝ x (Spectral.planeRotation θ ξ)) = _
        rw [hinner θ]
        simp [circleMap]
      _ = Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) := by
        rw [Spectral.circleAverage_cos_linear_eq_besselJ0Angular, hnormAB]
        simp
  have hsin : (∫ θ : ℝ, Real.sin
      (inner ℝ x (Spectral.planeRotation θ ξ)) ∂Spectral.unitAngleMeasure) = 0 := by
    simp_rw [Spectral.unitAngleMeasure, integral_smul_measure]
    simp_rw [← intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := 2 * Real.pi)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [hcoef]
    calc
      (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.sin (inner ℝ x (Spectral.planeRotation θ ξ)) =
          Real.circleAverage (fun z : ℂ => Real.sin (A * z.re + B * z.im)) 0 1 := by
        rw [Real.circleAverage_def]
        congr 1
        apply intervalIntegral.integral_congr
        intro θ hθ
        change Real.sin (inner ℝ x (Spectral.planeRotation θ ξ)) = _
        rw [hinner θ]
        simp [circleMap]
      _ = 0 := Spectral.circleAverage_sin_linear_eq_zero A B 1
  apply Complex.ext
  · calc
      (∫ θ : ℝ, Complex.exp
          (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))
          ∂Spectral.unitAngleMeasure).re =
        ∫ θ : ℝ, (Complex.exp
          (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))).re
          ∂Spectral.unitAngleMeasure := (integral_re hInt).symm
      _ = Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) := by
        calc
          (∫ θ : ℝ, (Complex.exp
              (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))).re
              ∂Spectral.unitAngleMeasure) =
            ∫ θ : ℝ, Real.cos (inner ℝ x (Spectral.planeRotation θ ξ))
              ∂Spectral.unitAngleMeasure := by
                apply integral_congr_ae
                filter_upwards [] with θ
                have hphase :
                    -(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) =
                      (-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) * Complex.I := by
                  ring
                rw [hphase]
                simpa only [Complex.ofReal_neg, Real.cos_neg] using
                  (Complex.exp_ofReal_mul_I_re
                    (-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))
          _ = Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) := hcos
  · calc
      (∫ θ : ℝ, Complex.exp
          (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))
          ∂Spectral.unitAngleMeasure).im =
        ∫ θ : ℝ, (Complex.exp
          (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))).im
          ∂Spectral.unitAngleMeasure := (integral_im hInt).symm
      _ = 0 := by
        calc
          (∫ θ : ℝ, (Complex.exp
              (-(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))).im
              ∂Spectral.unitAngleMeasure) =
            ∫ θ : ℝ, -Real.sin (inner ℝ x (Spectral.planeRotation θ ξ))
              ∂Spectral.unitAngleMeasure := by
                apply integral_congr_ae
                filter_upwards [] with θ
                have hphase :
                    -(Complex.I * (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) =
                      (-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)) * Complex.I := by
                  ring
                rw [hphase]
                simpa only [Complex.ofReal_neg, Real.sin_neg] using
                  (Complex.exp_ofReal_mul_I_im
                    (-(inner ℝ x (Spectral.planeRotation θ ξ) : ℝ)))
          _ = 0 := by rw [integral_neg, hsin, neg_zero]

/-- The Fourier phase along rotated frequencies is integrable jointly in space and angle; its
absolute value is bounded by the compactly supported spatial test. -/
theorem integrable_fourierKPZ_planeRotation_product (q : TestFn) (ξ : Plane) :
    Integrable (fun p : Plane × ℝ =>
      Complex.exp (-(Complex.I * (inner ℝ p.1 (Spectral.planeRotation p.2 ξ) : ℝ))) *
        (q p.1 : ℂ)) (volume.prod Spectral.unitAngleMeasure) := by
  have hq : Integrable (fun x : Plane => ‖q x‖) volume := Spectral.integrable_norm_testFn q
  have hmajor : Integrable (fun p : Plane × ℝ => ‖q p.1‖)
      (volume.prod Spectral.unitAngleMeasure) := hq.comp_fst Spectral.unitAngleMeasure
  apply hmajor.mono'
  · exact (by fun_prop [Spectral.planeRotation] : Measurable _).aestronglyMeasurable
  · filter_upwards [] with p
    have hphase :
        -(Complex.I * (inner ℝ p.1 (Spectral.planeRotation p.2 ξ) : ℂ)) =
          (-(inner ℝ p.1 (Spectral.planeRotation p.2 ξ) : ℝ)) * Complex.I := by
      ring
    rw [norm_mul, hphase]
    have hexp : ‖Complex.exp
        ((-(inner ℝ p.1 (Spectral.planeRotation p.2 ξ) : ℝ)) * Complex.I)‖ = 1 := by
      simpa only [Complex.ofReal_neg] using
        (Complex.norm_exp_ofReal_mul_I
          (-(inner ℝ p.1 (Spectral.planeRotation p.2 ξ) : ℝ)))
    rw [hexp]
    simp [Complex.norm_real]

/-- Averaging the paper's Fourier transform over rotations gives the Bessel transform of the spatial
test. -/
theorem integral_fourierKPZ_planeRotation_eq_bessel (q : TestFn) (ξ : Plane) :
    (∫ θ : ℝ, Spectral.fourierKPZ (q : Plane → ℝ)
      (Spectral.planeRotation θ ξ) ∂Spectral.unitAngleMeasure) =
      Complex.ofReal (∫ x : Plane,
        q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖)) := by
  have hprod := integrable_fourierKPZ_planeRotation_product q ξ
  have hqJ : Integrable (fun x : Plane =>
      q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖)) volume := by
    apply (Spectral.integrable_norm_testFn q).mono'
    · exact ((q.continuous.mul
        (Spectral.continuous_besselJ0Angular.comp
          (continuous_norm.mul continuous_const))).aestronglyMeasurable)
    · filter_upwards [] with x
      have hJ := Spectral.abs_besselJ0Angular_le_one (‖x‖ * ‖ξ‖)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg (q x)) hJ
  calc
    (∫ θ : ℝ, Spectral.fourierKPZ (q : Plane → ℝ)
        (Spectral.planeRotation θ ξ) ∂Spectral.unitAngleMeasure) =
      ∫ θ : ℝ, ∫ x : Plane,
        Complex.exp (-(Complex.I *
          (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ))) * (q x : ℂ)
          ∂volume ∂Spectral.unitAngleMeasure := by
        apply integral_congr_ae
        filter_upwards [] with θ
        rfl
    _ = ∫ x : Plane, ∫ θ : ℝ,
        Complex.exp (-(Complex.I *
          (inner ℝ x (Spectral.planeRotation θ ξ) : ℝ))) * (q x : ℂ)
          ∂Spectral.unitAngleMeasure ∂volume := integral_integral_swap hprod.swap
    _ = ∫ x : Plane,
        (q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) : ℂ) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const, integral_exp_planeRotation_inner]
      simp [mul_comm]
    _ = ∫ x : Plane,
        ((q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖) : ℝ) : ℂ) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp
    _ = Complex.ofReal (∫ x : Plane,
        q x * Spectral.besselJ0Angular (‖x‖ * ‖ξ‖)) := integral_ofReal

/-- Logarithmic spectral ball growth makes every real Fourier test pairing integrable. The
polynomial ball-growth input required by the Schwartz-measure lemma follows from `log R ≤ R - 1`. -/
theorem integrable_fourierKPZRealPair_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R →
      spectralBallMass ν R ≤ A * (1 + Real.log R)) (f g : TestFn) :
    Integrable (fun ξ : Plane =>
      (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re) ν := by
  have hpoly : ∃ B : ℝ, ∃ k : ℕ, ∀ R : ℝ, 1 ≤ R →
      (ν (Metric.closedBall (0 : Plane) R)).toReal ≤ B * R ^ k := by
    refine ⟨A, 1, fun R hR => ?_⟩
    have hlog : Real.log R ≤ R - 1 :=
      Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hR)
    have hsum : 1 + Real.log R ≤ R := by linarith
    calc
      (ν (Metric.closedBall (0 : Plane) R)).toReal = spectralBallMass ν R := rfl
      _ ≤ A * (1 + Real.log R) := hGrowth R hR
      _ ≤ A * R := mul_le_mul_of_nonneg_left hsum hA
      _ = A * R ^ 1 := by rw [pow_one]
  exact Spectral.integrable_fourierKPZRealPair_of_polynomial_ball_growth ν hpoly f g

/-- Multiplying a compact smooth test by the locally integrable inverse square-root radius
preserves integrability. This is the spatial factor in the absolute Bessel pairing majorant. -/
theorem integrable_norm_testFn_mul_norm_inv_sqrt (q : TestFn) :
    Integrable (fun z : Plane => ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ))) volume := by
  let K : Set Plane := tsupport q
  have hK : IsCompact K := q.hasCompactSupport
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  have hsingMeas : AEStronglyMeasurable
      (fun z : Plane => ‖z‖ ^ (-(1 / 2 : ℝ))) volume := by
    exact (by fun_prop : Measurable
      (fun z : Plane => ‖z‖ ^ (-(1 / 2 : ℝ)))).aestronglyMeasurable
  have hsingOn : IntegrableOn
      (fun z : Plane => ‖z‖ ^ (-(1 / 2 : ℝ))) (Metric.ball (0 : Plane) R) volume := by
    apply integrableOn_ball_of_norm_le_rpow
      (E := Plane) (F := ℝ)
      (f := fun z : Plane => ‖z‖ ^ (-(1 / 2 : ℝ)))
      (C := 1) (α := 1 / 2) (r := R)
      (by norm_num [Plane] : 1 ≤ Module.finrank ℝ Plane)
      (by norm_num [Plane] : (1 / 2 : ℝ) < Module.finrank ℝ Plane)
    · filter_upwards [] with z
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    · exact hsingMeas
  obtain ⟨B₀, hB₀⟩ :=
    q.continuous.norm.bounded_above_of_compact_support q.hasCompactSupport.norm
  let B : ℝ := max B₀ 0
  have hBnonneg : 0 ≤ B := le_max_right _ _
  have hqbound (z : Plane) : ‖q z‖ ≤ B := by
    calc
      ‖q z‖ ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ z
      _ ≤ B := le_max_left _ _
  have hmajor : IntegrableOn
      (fun z : Plane => B * ‖z‖ ^ (-(1 / 2 : ℝ)))
      (Metric.ball (0 : Plane) R) volume := hsingOn.const_mul B
  have hweightedOn : IntegrableOn
      (fun z : Plane => ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ)))
      (Metric.ball (0 : Plane) R) volume := by
    apply hmajor.mono'
      ((q.continuous.norm.aestronglyMeasurable.mul hsingMeas).restrict)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hpow : 0 ≤ ‖z‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg z) _
    have hprod : 0 ≤ ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (norm_nonneg _) hpow
    change |‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ))| ≤ _
    rw [abs_of_nonneg hprod]
    exact mul_le_mul_of_nonneg_right (hqbound z) hpow
  have hzero : ∀ z : Plane, z ∉ Metric.ball (0 : Plane) R →
      ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ)) = 0 := by
    intro z hz
    have hznotK : z ∉ K := by
      intro hzK
      have hnorm : ‖z‖ < R := hR z hzK
      have hzball : z ∈ Metric.ball (0 : Plane) R := by
        simpa [Metric.mem_ball, dist_zero_right] using hnorm
      exact hz hzball
    have hqzero : q z = 0 := by
      by_contra hq
      have hsupport : z ∈ Function.support q := by
        simpa [Function.mem_support] using hq
      have hsub : Function.support q ⊆ tsupport q := subset_tsupport q
      exact hznotK (hsub hsupport)
    simp [hqzero]
  have heq : (fun z : Plane => ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ))) =
      (Metric.ball (0 : Plane) R).indicator
        (fun z : Plane => ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ))) := by
    funext z
    by_cases hz : z ∈ Metric.ball (0 : Plane) R
    · simp [hz]
    · simp only [Set.indicator_of_notMem hz]
      exact hzero z hz
  rw [heq]
  exact hweightedOn.integrable_indicator measurableSet_ball

/-- The angular Bessel kernel has the inverse-square-root product bound needed to integrate it
against a spectral measure with logarithmic ball growth. -/
theorem abs_besselJ0Angular_le_three_mul_inv_sqrt {a b : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) :
    |Spectral.besselJ0Angular (a * b)| ≤
      3 * a ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hab0 : 0 < a * b := mul_pos ha0 hb
  have hpows : (a * b) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow ha0.le hb.le
  by_cases hab : 1 ≤ a * b
  · have hdecay := Spectral.abs_besselJ0Angular_le_three_div_sqrt hab
    have hsqrtInv : (Real.sqrt (a * b))⁻¹ =
        (a * b) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hab0.le]
    calc
      |Spectral.besselJ0Angular (a * b)| ≤ 3 / Real.sqrt (a * b) := hdecay
      _ = 3 * (a * b) ^ (-(1 / 2 : ℝ)) := by rw [← hsqrtInv]; ring
      _ = 3 * a ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) := by rw [hpows]; ring
  · have hablt : a * b < 1 := lt_of_not_ge hab
    have hpow : 1 ≤ (a * b) ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hab0 (le_of_lt hablt) (by norm_num)
    calc
      |Spectral.besselJ0Angular (a * b)| ≤ 1 := Spectral.abs_besselJ0Angular_le_one _
      _ ≤ 3 * (a * b) ^ (-(1 / 2 : ℝ)) := by nlinarith
      _ = 3 * a ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) := by rw [hpows]; ring

/-- Absolute integrability of the Bessel kernel against a compact smooth spatial test and a
logarithmically growing spectral measure. The companion spatial integrability is
`integrable_norm_testFn_mul_norm_inv_sqrt`. -/
theorem integrable_testFn_mul_besselJ0_product_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R))
    (q : TestFn) :
    Integrable (fun p : Plane × Plane =>
      q p.1 * Spectral.besselJ0Angular (‖p.2‖ * ‖p.1‖)) (volume.prod ν) := by
  let B : Set Plane := Metric.closedBall (0 : Plane) 1
  let U : Plane → ℝ := B.indicator (fun _ => (1 : ℝ))
  let G : Plane → ℝ := fun z => ‖q z‖ * ‖z‖ ^ (-(1 / 2 : ℝ))
  let T : Plane → ℝ := spectralInverseSqrtTail
  let M : Plane × Plane → ℝ := fun p =>
    ‖q p.1‖ * U p.2 + 3 * (G p.1 * T p.2)
  have hBcompact : IsCompact B := by dsimp [B]; exact isCompact_closedBall _ _
  have hBfinite : ν B ≠ ⊤ := hBcompact.measure_ne_top
  have hBmeas : MeasurableSet B := hBcompact.measurableSet
  have hUint : Integrable U ν := by
    dsimp [U]
    exact (integrableOn_const (μ := ν) (s := B) (C := (1 : ℝ))
      (hs := hBfinite)).integrable_indicator hBmeas
  have hQint : Integrable (fun z : Plane => ‖q z‖) volume :=
    Spectral.integrable_norm_testFn q
  have hGint : Integrable G volume := by
    simpa [G] using integrable_norm_testFn_mul_norm_inv_sqrt q
  have hTint : Integrable T ν :=
    integrable_spectralInverseSqrtTail_of_logGrowth ν hA hGrowth
  have hmajor : Integrable M (volume.prod ν) := by
    dsimp [M]
    exact (hQint.mul_prod hUint).add ((hGint.mul_prod hTint).const_mul 3)
  have hU_nonneg (ξ : Plane) : 0 ≤ U ξ := by
    by_cases hξ : ξ ∈ B <;> simp [U, hξ]
  have hT_nonneg (ξ : Plane) : 0 ≤ T ξ := by
    by_cases hξ : 1 ≤ ‖ξ‖ <;> simp [T, spectralInverseSqrtTail, hξ]
  have hG_nonneg (z : Plane) : 0 ≤ G z := by
    dsimp [G]
    exact mul_nonneg (norm_nonneg (q z)) (Real.rpow_nonneg (norm_nonneg z) _)
  have hpoint (z ξ : Plane) (hz : z ≠ 0) :
      |q z * Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)| ≤ M (z, ξ) := by
    by_cases hξ : ξ ∈ B
    · have hJ := Spectral.abs_besselJ0Angular_le_one (‖ξ‖ * ‖z‖)
      have hqJ : |q z * Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)| ≤ ‖q z‖ := by
        rw [abs_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) hJ
      have htail := mul_nonneg (by norm_num : 0 ≤ (3 : ℝ))
        (mul_nonneg (hG_nonneg z) (hT_nonneg ξ))
      calc
        |q z * Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)| ≤ ‖q z‖ := hqJ
        _ ≤ ‖q z‖ * U ξ + 3 * (G z * T ξ) := by
          simp [U, hξ]
          linarith
    · have hξnorm : 1 ≤ ‖ξ‖ := by
        apply le_of_not_gt
        intro hlt
        apply hξ
        exact Metric.mem_closedBall.mpr (by
          simpa [B, Metric.mem_closedBall, dist_zero_right] using (le_of_lt hlt))
      have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hJ := abs_besselJ0Angular_le_three_mul_inv_sqrt hξnorm hzNorm
      have htailEq : T ξ = ‖ξ‖ ^ (-(1 / 2 : ℝ)) := by
        simp [T, spectralInverseSqrtTail, hξnorm, Real.sqrt_eq_rpow,
          ← Real.rpow_neg (norm_nonneg ξ)]
      have hqnonneg : 0 ≤ ‖q z‖ := norm_nonneg _
      have hFbound : |q z * Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)| ≤
          3 * (G z * T ξ) := by
        rw [abs_mul, ← Real.norm_eq_abs]
        calc
          |q z| * |Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)| ≤
              ‖q z‖ * (3 * ‖ξ‖ ^ (-(1 / 2 : ℝ)) *
                ‖z‖ ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hJ hqnonneg
          _ = 3 * (G z * T ξ) := by
            simp only [G, htailEq]
            ring
      calc
        |q z * Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)| ≤ 3 * (G z * T ξ) := hFbound
        _ = M (z, ξ) := by simp [M, U, hξ]
  have hArgmeas : Measurable (fun p : Plane × Plane => ‖p.2‖ * ‖p.1‖) := by fun_prop
  have hFmeas : Measurable (fun p : Plane × Plane =>
      q p.1 * Spectral.besselJ0Angular (‖p.2‖ * ‖p.1‖)) :=
    (q.continuous.measurable.comp measurable_fst).mul
      (Spectral.continuous_besselJ0Angular.measurable.comp hArgmeas)
  have hzeroSet : MeasurableSet {p : Plane × Plane | p.1 = 0} := by
    exact (measurableSet_singleton (0 : Plane)).preimage measurable_fst
  have hnonzeroSet : MeasurableSet {p : Plane × Plane | p.1 ≠ 0} := by
    rw [show {p : Plane × Plane | p.1 ≠ 0} =
      {p : Plane × Plane | p.1 = 0}ᶜ by ext p; simp]
    exact hzeroSet.compl
  have hprodNonzero : ∀ᵐ p : Plane × Plane ∂(volume.prod ν), p.1 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae hnonzeroSet).2
    filter_upwards [Measure.ae_ne volume (0 : Plane)] with z hz
    exact Filter.Eventually.of_forall fun _ => hz
  have hdominates : ∀ᵐ p : Plane × Plane ∂(volume.prod ν),
      ‖q p.1 * Spectral.besselJ0Angular (‖p.2‖ * ‖p.1‖)‖ ≤ M p := by
    filter_upwards [hprodNonzero] with p hp
    simpa [Real.norm_eq_abs] using hpoint p.1 p.2 hp
  have hFint : Integrable (fun p : Plane × Plane =>
      q p.1 * Spectral.besselJ0Angular (‖p.2‖ * ‖p.1‖)) (volume.prod ν) :=
    hmajor.mono' hFmeas.aestronglyMeasurable hdominates
  exact hFint

end Critical2DKPZ.CovarianceKernel

end
