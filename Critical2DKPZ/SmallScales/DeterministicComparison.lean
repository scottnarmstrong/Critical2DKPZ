/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.TestJensen
public import Critical2DKPZ.SmallScales.HeatTilt
public import Critical2DKPZ.Definitions.TestFnDilate
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Deterministic point-matched heat-log comparison -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SmallScales

/-- The test-function dilation change of variables, valid for the total Bochner integral. -/
theorem integral_testFn_dilate_mul (φ : TestFn) {ε : ℝ} (hε : 0 < ε) (x : Plane)
    (F : Plane → ℝ) :
    (∫ y, φ.dilate ε x y * F y) = ∫ z, φ z * F (x + ε • z) := by
  have hd : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have hs := Measure.integral_comp_smul volume
    (fun v => φ.dilate ε x (x + v) * F (x + v)) ε
  have hsub : ∀ z : Plane, φ.dilate ε x (x + ε • z) = ε⁻¹ ^ 2 * φ z := by
    intro z
    simp [TestFn.dilate, smul_smul, inv_mul_cancel₀ hε.ne']
  simp only [hd, inv_pow, hsub] at hs
  simp_rw [mul_assoc] at hs
  have ht := integral_add_left_eq_self (μ := volume) (fun y => φ.dilate ε x y * F y) x
  rw [integral_const_mul, ht] at hs
  simp only [abs_of_nonneg (inv_nonneg.2 (sq_nonneg ε)), smul_eq_mul] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 hε.ne')) hs).symm

/-- Integrability is preserved by the dilation change of variables. -/
theorem integrable_testFn_dilate_mul (φ : TestFn) {ε : ℝ} (hε : 0 < ε) (x : Plane)
    (F : Plane → ℝ) (hF : Integrable (fun z => φ z * F (x + ε • z))) :
    Integrable (fun y => φ.dilate ε x y * F y) := by
  have h := ((hF.comp_smul (inv_ne_zero hε.ne')).comp_add_right (-x)).const_mul (ε⁻¹ ^ 2)
  convert h using 1
  funext y
  rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  simp [TestFn.dilate, sub_eq_add_neg, mul_assoc]

/-- For a nonnegative unit-mass test function, the averaged heat logarithm exceeds its value at the rescaled barycentre minus half the centered second test moment, assuming the required integrability. -/
theorem heatLog_average_sub_lower_bound (μ : Measure Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ₁ : ∫ y, φ y = 1) (x : Plane) {ε : ℝ} (hε : 0 < ε)
    (hi : ∀ y : Plane, Integrable (fun u => heatKernel (ε ^ 2) (u - y)) μ)
    (hp : ∀ y : Plane, 0 < ∫ u, heatKernel (ε ^ 2) (u - y) ∂μ)
    (hfirst : Integrable (fun u : Plane =>
      heatKernel (ε ^ 2) (u - (x + ε • barycentre φ)) • u) μ)
    (hlog : Integrable (fun z => φ z *
      (Real.log (∫ u, heatKernel (ε ^ 2) (u - (x + ε • z)) ∂μ) -
        Real.log (∫ u, heatKernel (ε ^ 2) (u - (x + ε • barycentre φ)) ∂μ)))) :
    Integrable (fun y => φ.dilate ε x y *
      Real.log (∫ u, heatKernel (ε ^ 2) (u - y) ∂μ)) ∧
    -(∫ z, φ z * ‖z - barycentre φ‖ ^ 2) / 2 ≤
      (∫ y, φ.dilate ε x y * Real.log (∫ u, heatKernel (ε ^ 2) (u - y) ∂μ)) -
        Real.log (∫ u, heatKernel (ε ^ 2) (u - (x + ε • barycentre φ)) ∂μ) := by
  let b := x + ε • barycentre φ
  let Q := heatTilt μ (ε ^ 2) b
  have : IsProbabilityMeasure Q := isProbabilityMeasure_heatTilt μ (sq_pos_of_pos hε)
    b (hi b) (hp b)
  have hQ : Integrable (fun u : Plane => u) Q :=
    integrable_id_heatTilt μ (sq_pos_of_pos hε) b (hp b) hfirst
  have hexp : ∀ z : Plane, Integrable (fun u => Real.exp
      (inner ℝ ((x + ε • z) - b) (u - b) / ε ^ 2)) Q := by
    intro z
    exact integrable_exp_heatTilt μ (sq_pos_of_pos hε) b (x + ε • z) (hp b) (hi _)
  have hlogQ : Integrable (fun z => φ z *
      heatRatioLog Q (ε ^ 2) b (x + ε • z)) := by
    simpa only [Q, heatRatioLog_heatTilt μ (sq_pos_of_pos hε) b _ (hp b) (hp _)] using hlog
  have h := heatRatioLog_testFn_average_lower_bound Q φ hφ hφ₁ x hε hQ hexp hlogQ
  change -(∫ z, φ z * ‖z - barycentre φ‖ ^ 2) / 2 ≤
    ∫ z, φ z * heatRatioLog Q (ε ^ 2) b (x + ε • z) at h
  simp only [Q, heatRatioLog_heatTilt μ (sq_pos_of_pos hε) b _ (hp b) (hp _)] at h
  let F : Plane → ℝ := fun y => Real.log (∫ u, heatKernel (ε ^ 2) (u - y) ∂μ)
  have hdiff : Integrable (fun y => φ.dilate ε x y * (F y - F b)) :=
    integrable_testFn_dilate_mul φ hε x _ hlog
  have hconst : Integrable (fun y => φ.dilate ε x y * F b) :=
    ((φ.dilate ε x).continuous.integrable_of_hasCompactSupport
      (φ.dilate ε x).hasCompactSupport).mul_const _
  have hF : Integrable (fun y => φ.dilate ε x y * F y) := by
    convert hdiff.add hconst using 1
    funext y
    simp only [Pi.add_apply]
    ring
  refine ⟨hF, ?_⟩
  have hmass : (∫ y, φ.dilate ε x y) = 1 := by
    simpa only [mul_one, hφ₁] using integral_testFn_dilate_mul φ hε x (fun _ => 1)
  have heq : (∫ y, φ.dilate ε x y * (F y - F b)) =
      (∫ y, φ.dilate ε x y * F y) - F b := by
    simp_rw [mul_sub]
    rw [integral_sub hF hconst, integral_mul_const, hmass, one_mul]
  rw [← heq, integral_testFn_dilate_mul φ hε]
  exact h

/-- An integrable mean-zero random variable bounded below by `-B` has absolute first moment at most `2B`. -/
theorem integral_abs_le_of_mean_zero_of_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {B : ℝ}
    (hX : Integrable X P) (hmean : (∫ ω, X ω ∂P) = 0) (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂P, -B ≤ X ω) :
    Integrable (fun ω => |X ω|) P ∧ (∫ ω, |X ω| ∂P) ≤ 2 * B := by
  refine ⟨hX.abs, ?_⟩
  have hi : Integrable (fun ω => X ω + 2 * B) P := hX.add (integrable_const _)
  have hle : ∀ᵐ ω ∂P, |X ω| ≤ X ω + 2 * B := by
    filter_upwards [hbound] with ω hω
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h := integral_mono_ae hX.abs hi hle
  rw [integral_add hX (integrable_const _), hmean, integral_const] at h
  simpa using h

end Critical2DKPZ.SmallScales
