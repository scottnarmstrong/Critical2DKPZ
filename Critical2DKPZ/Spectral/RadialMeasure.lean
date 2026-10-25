/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.RadialBessel
public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Critical2DKPZ.Spectral.FourierConvention
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Critical2DKPZ.Analysis.Sobolev.TranslatedPairingConvolution
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichMollify
public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-! Polar coordinates, planar rotations and Fourier identities for real test convolutions. -/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory
open scoped ENNReal NNReal FourierTransform ComplexConjugate RealInnerProductSpace

namespace Critical2DKPZ.Spectral

/-- Polar coordinates on the Euclidean plane. -/
def radialPolarPoint (r : ℝ≥0) (θ : ℝ) : Plane :=
  WithLp.toLp 2 ![(circleMap 0 (r : ℝ) θ).re, (circleMap 0 (r : ℝ) θ).im
  ]






/-- Normalized Lebesgue measure on one full turn of the angular variable. -/
def unitAngleMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    (volume.restrict (Set.Ioc 0 (2 * Real.pi)))

private theorem unitAngleMeasure_isFinite : IsFiniteMeasure unitAngleMeasure := by
  constructor
  unfold unitAngleMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply_univ]
  simp only [Real.volume_Ioc]
  finiteness

instance : IsFiniteMeasure unitAngleMeasure := unitAngleMeasure_isFinite

/-- The angular measure is a probability measure. -/
theorem unitAngleMeasure_univ : unitAngleMeasure Set.univ = 1 := by
  unfold unitAngleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  rw [Real.volume_Ioc, sub_zero]
  calc
    ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (2 * Real.pi) =
        ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ((2 * Real.pi)⁻¹) := mul_comm _ _
    _ = ENNReal.ofReal ((2 * Real.pi) * (2 * Real.pi)⁻¹) :=
      (ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)).symm
    _ = 1 := by
      have h : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := by
        field_simp
      rw [h, ENNReal.ofReal_one]





















/-- Reversing frequency conjugates the Fourier transform of a real test function. -/
theorem fourierKPZ_neg_eq_conj (f : TestFn) (ξ : Plane) :
    fourierKPZ (f : Plane → ℝ) (-ξ) = conj (fourierKPZ (f : Plane → ℝ) ξ) := by
  rw [fourierKPZ_eq_angularFourierIntegral, conj_fourierKPZ]
  unfold Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  simp only [inner_neg_left, neg_neg]

/-- The canonical convolution of two real tests has Fourier transform
`f̂ · conj(ĝ)` in the paper's angular-frequency convention. -/
theorem fourierKPZ_testFnConvolution (f g : TestFn) (ξ : Plane) :
    fourierKPZ
        (Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g : Plane → ℝ) ξ =
      fourierKPZ (f : Plane → ℝ) ξ * conj (fourierKPZ (g : Plane → ℝ) ξ) := by
  let g' : TestFn := Critical2DKPZ.Analysis.Sobolev.reflectedTestFn g
  let η : Plane := (2 * Real.pi)⁻¹ • ξ
  have hbridge (h : TestFn) : fourierKPZ (h : Plane → ℝ) ξ =
      𝓕 (fun x : Plane => (h x : ℂ)) η := by
    rw [fourierKPZ_eq_angularFourierIntegral,
      Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral_eq_fourier]
  have hconv := Critical2DKPZ.Analysis.Sobolev.Rellich.fourier_ofReal_convolution
    (d := 2) f g' f.contDiff g'.contDiff f.hasCompactSupport g'.hasCompactSupport η
  have htransform : fourierKPZ
      (Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g : Plane → ℝ) ξ =
      𝓕 (fun x : Plane => (f x : ℂ)) η * 𝓕 (fun x : Plane => (g' x : ℂ)) η := by
    rw [fourierKPZ_eq_angularFourierIntegral,
      Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral_eq_fourier]
    simpa only [Critical2DKPZ.Analysis.Sobolev.testFnConvolution_apply,
      MeasureTheory.convolution_lsmul, smul_eq_mul, g',
      Critical2DKPZ.Analysis.Sobolev.reflectedTestFn_apply, neg_sub] using hconv
  calc
    fourierKPZ (Critical2DKPZ.Analysis.Sobolev.testFnConvolution f g : Plane → ℝ) ξ =
        𝓕 (fun x : Plane => (f x : ℂ)) η * 𝓕 (fun x : Plane => (g' x : ℂ)) η := htransform
    _ = fourierKPZ (f : Plane → ℝ) ξ *
        fourierKPZ (g' : Plane → ℝ) ξ := by rw [← hbridge f, ← hbridge g']
    _ = fourierKPZ (f : Plane → ℝ) ξ *
        conj (fourierKPZ (g : Plane → ℝ) ξ) := by
      have hreflect : fourierKPZ
          (Critical2DKPZ.Analysis.Sobolev.reflectedTestFn g : Plane → ℝ) ξ =
            fourierKPZ (g : Plane → ℝ) (-ξ) := by
        have h := fourierKPZ_comp_linearIsometryEquiv g
          (LinearIsometryEquiv.neg ℝ) ξ
        change fourierKPZ (fun x : Plane => g (-x)) ξ = _
        simpa [LinearIsometryEquiv.coe_neg] using h
      rw [show g' = Critical2DKPZ.Analysis.Sobolev.reflectedTestFn g from rfl,
        hreflect, fourierKPZ_neg_eq_conj]

















/-- Rotation of the Euclidean plane by angle θ. -/
def planeRotation (θ : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![x 0 * Real.cos θ - x 1 * Real.sin θ,
    x 0 * Real.sin θ + x 1 * Real.cos θ]


def planeRotationLinearMap (θ : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun := planeRotation θ
  map_add' x y := by
    ext i
    fin_cases i <;> simp [planeRotation] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [planeRotation] <;> ring

theorem inner_planeRotation_map (θ : ℝ) (x y : Plane) :
    inner ℝ (planeRotation θ x) (planeRotation θ y) = inner ℝ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  have hformula :
      (y 0 * Real.cos θ - y 1 * Real.sin θ) *
          (x 0 * Real.cos θ - x 1 * Real.sin θ) +
        (y 0 * Real.sin θ + y 1 * Real.cos θ) *
          (x 0 * Real.sin θ + x 1 * Real.cos θ) =
        y 0 * x 0 + y 1 * x 1 := by
    calc
      _ = y 0 * x 0 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) +
          y 1 * x 1 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq θ]; ring
  simpa [planeRotation, dotProduct, Fin.sum_univ_succ] using hformula

/-- Planar rotation as a linear isometry equivalence. -/
noncomputable def planeRotationLinearIsometryEquiv (θ : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  ((planeRotationLinearMap θ).isometryOfInner (inner_planeRotation_map θ)).toLinearIsometryEquiv rfl

@[simp] theorem planeRotationLinearIsometryEquiv_apply (θ : ℝ) (x : Plane) :
    planeRotationLinearIsometryEquiv θ x = planeRotation θ x := rfl






end Critical2DKPZ.Spectral

end
