/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.SchurTest
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# Schur's test with auxiliary singular weights

The auxiliary weights used to control swapping resolvents may be infinite on
a null set. Positivity and finiteness are required only almost everywhere in
the input space, and no integral is converted to a real number.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The cancellation used in the weighted Cauchy--Schwarz argument. -/
theorem ennreal_weight_cancel {k w f : ℝ≥0∞} (hw0 : w ≠ 0) (hwtop : w ≠ ⊤) :
    (k * w) * (f / w) = k * f := by
  rw [div_eq_mul_inv]
  calc k * w * (f * w⁻¹) = (k * f) * (w * w⁻¹) := by ac_rfl
    _ = k * f := by rw [ENNReal.mul_inv_cancel hw0 hwtop, mul_one]

/-- A finite positive weight cancels from a weighted square in the nonnegative extended reals. -/
theorem ennreal_weight_sq_cancel {k w f : ℝ≥0∞} (hw0 : w ≠ 0) (hwtop : w ≠ ⊤) :
    (k * w) * (f / w) ^ 2 = k * (f ^ 2 / w) := by
  rw [div_eq_mul_inv, mul_pow, div_eq_mul_inv]
  calc k * w * (f ^ 2 * w⁻¹ ^ 2) = (k * (f ^ 2 * w⁻¹)) * (w * w⁻¹) := by
          simp only [pow_two]
          ac_rfl
    _ = k * (f ^ 2 * w⁻¹) := by rw [ENNReal.mul_inv_cancel hw0 hwtop, mul_one]

/-- Weighted Schur test for possibly singular positive auxiliary weights. -/
theorem lintegral_kernel_sq_le_weighted_schur {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {K : X → Y → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {v : X → ℝ≥0∞} {w : Y → ℝ≥0∞}
    (hv : Measurable v) (hw : Measurable w)
    (hwfinite : ∀ᵐ y ∂ν, w y ≠ 0 ∧ w y ≠ ⊤) {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y * w y ∂ν ≤ A * v x)
    (hcol : ∀ y, ∫⁻ x, K x y * v x ∂μ ≤ B * w y)
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ) ≤ A * B * ∫⁻ y, f y ^ 2 ∂ν := by
  have hkx (x : X) : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
  have hpoint (x : X) : (∫⁻ y, K x y * f y ∂ν) ^ 2 ≤
      (A * v x) * ∫⁻ y, K x y * (f y ^ 2 / w y) ∂ν := by
    have he1 : (∫⁻ y, (K x y * w y) * (f y / w y) ∂ν) = ∫⁻ y, K x y * f y ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hwfinite] with y hy
      exact ennreal_weight_cancel hy.1 hy.2
    have he2 : (∫⁻ y, (K x y * w y) * (f y / w y) ^ 2 ∂ν) =
        ∫⁻ y, K x y * (f y ^ 2 / w y) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hwfinite] with y hy
      exact ennreal_weight_sq_cancel hy.1 hy.2
    have hc := lintegral_mul_sq_le ν ((hkx x).mul hw) (hf.div hw)
    simp only [Pi.mul_apply, Pi.div_apply] at hc
    rw [he1, he2] at hc
    exact hc.trans (mul_le_mul' (hrow x) le_rfl)
  have hF : Measurable (fun p : X × Y => v p.1 * (K p.1 p.2 * (f p.2 ^ 2 / w p.2))) :=
    (hv.comp measurable_fst).mul (hK.mul (((hf.comp measurable_snd).pow_const 2).div (hw.comp measurable_snd)))
  calc
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ)
        ≤ ∫⁻ x, A * (v x * ∫⁻ y, K x y * (f y ^ 2 / w y) ∂ν) ∂μ := by
          apply lintegral_mono
          intro x
          simpa only [mul_assoc] using hpoint x
    _ = A * ∫⁻ x, v x * ∫⁻ y, K x y * (f y ^ 2 / w y) ∂ν ∂μ :=
      lintegral_const_mul' A _ hA
    _ = A * ∫⁻ x, ∫⁻ y, v x * (K x y * (f y ^ 2 / w y)) ∂ν ∂μ := by
      congr 1
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ ((hkx x).mul ((hf.pow_const 2).div hw))).symm
    _ = A * ∫⁻ y, ∫⁻ x, v x * (K x y * (f y ^ 2 / w y)) ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hF.aemeasurable]
    _ ≤ A * ∫⁻ y, B * f y ^ 2 ∂ν := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [hwfinite] with y hy
      have hky : Measurable (fun x => K x y * v x) :=
        (hK.comp (measurable_id.prodMk measurable_const)).mul hv
      calc (∫⁻ x, v x * (K x y * (f y ^ 2 / w y)) ∂μ)
          = (∫⁻ x, K x y * v x ∂μ) * (f y ^ 2 / w y) := by
            rw [← lintegral_mul_const _ hky]
            apply lintegral_congr
            intro x
            ac_rfl
        _ ≤ (B * w y) * (f y ^ 2 / w y) := mul_le_mul' (hcol y) le_rfl
        _ = B * f y ^ 2 := ennreal_weight_cancel hy.1 hy.2
    _ = A * B * ∫⁻ y, f y ^ 2 ∂ν := by
      rw [lintegral_const_mul' B _ hB, mul_assoc]

end Critical2DKPZ.DeltaBose
