/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzTranslate
public import Critical2DKPZ.Spectral.BochnerSchwartzSquareCone
public import Critical2DKPZ.Definitions.TestFnDilate
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Normalized Schwartz dilations and their angular Fourier transform -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Normalized dilation on real Schwartz space, on its nonzero-scale domain. -/
def shapeDilate (a : ℝ) (ha : a ≠ 0) (ψ : SchwartzMap Plane ℝ) : SchwartzMap Plane ℝ :=
  a⁻¹ ^ 2 • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (inverseScaleEquiv a ha) ψ

@[simp] theorem shapeDilate_apply (a : ℝ) (ha : a ≠ 0)
    (ψ : SchwartzMap Plane ℝ) (x : Plane) :
    shapeDilate a ha ψ x = a⁻¹ ^ 2 * ψ (a⁻¹ • x) := rfl

/-- Normalization cancels the planar Jacobian in the paper's Fourier convention. -/
theorem fourierKPZ_normalized_dilation (f : Plane → ℝ) {a : ℝ} (ha : 0 < a) (ξ : Plane) :
    Spectral.fourierKPZ (fun x => a⁻¹ ^ 2 * f (a⁻¹ • x)) ξ =
      Spectral.fourierKPZ f (a • ξ) := by
  let G : Plane → ℂ := fun z =>
    Complex.exp (-(Complex.I * (inner ℝ z (a • ξ) : ℝ))) * (f z : ℂ)
  have hphase (x : Plane) : inner ℝ (a⁻¹ • x) (a • ξ) = inner ℝ x ξ := by
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    field_simp
  calc
    _ = a⁻¹ ^ 2 • ∫ x : Plane, G (a⁻¹ • x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [Spectral.fourierKPZ, G]
      rw [hphase]
      push_cast
      ring
    _ = a⁻¹ ^ 2 • ((a⁻¹ ^ 2)⁻¹ • ∫ x : Plane, G x) := by
      rw [Measure.integral_comp_smul]
      simp only [Plane, finrank_euclideanSpace, Fintype.card_fin,
        abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (a⁻¹)))]
    _ = ∫ x : Plane, G x := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 (inv_ne_zero ha.ne')), one_smul]

/-- Angular Fourier scaling for the normalized real Schwartz dilation. -/
theorem fourierKPZ_shapeDilate (ψ : SchwartzMap Plane ℝ) {a : ℝ} (ha : 0 < a)
    (ξ : Plane) :
    Spectral.fourierKPZ (shapeDilate a ha.ne' ψ) ξ = Spectral.fourierKPZ ψ (a • ξ) :=
  fourierKPZ_normalized_dilation ψ ha ξ

/-- Dilation is linear in the shape. -/
theorem shapeDilate_sub (a : ℝ) (ha : a ≠ 0) (ψ χ : SchwartzMap Plane ℝ) :
    shapeDilate a ha (ψ - χ) = shapeDilate a ha ψ - shapeDilate a ha χ := by
  ext y
  simp only [shapeDilate_apply, sub_apply, mul_sub]

/-- Successive normalized dilations multiply their spatial scales. -/
theorem shapeDilate_comp (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (ψ : SchwartzMap Plane ℝ) :
    shapeDilate a ha (shapeDilate b hb ψ) = shapeDilate (b * a) (mul_ne_zero hb ha) ψ := by
  ext y
  simp only [shapeDilate_apply, smul_smul, mul_inv_rev, mul_pow, mul_assoc, mul_comm]

/-- The chosen band kernel uses exactly the normalized Schwartz dilation. -/
theorem shapeDilate_zeta (a : ℝ) (ha : a ≠ 0) : shapeDilate a ha zeta = zetaScaled a 0 := by
  ext y
  simp only [shapeDilate_apply, zetaScaled_apply, sub_zero]

/-- Normalized dilation of a compact test agrees with `TestFn.dilate`. -/
theorem shapeDilate_test (a : ℝ) (ha : a ≠ 0) (x : Plane) (φ : TestFn) :
    translateSchwartz x (shapeDilate a ha (Spectral.testFnToRealSchwartz φ)) =
      Spectral.testFnToRealSchwartz (φ.dilate a x) := by
  ext y
  rfl

end Critical2DKPZ.Extensions.ScaleLimit
