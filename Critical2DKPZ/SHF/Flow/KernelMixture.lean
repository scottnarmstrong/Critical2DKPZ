/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.WeightedSchur
import Mathlib.MeasureTheory.Measure.Prod

/-! # Squared L² bounds for positive mixtures

Weighted Cauchy–Schwarz in the mixture parameter followed by Tonelli integrates
pointwise operator-norm bounds. This keeps endpoint-time singularities in an
integrable scalar majorant rather than squaring them before time integration.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The squared L² norm of a nonnegative kernel mixture is bounded by its integrated component bounds. -/
theorem lintegral_mixture_sq_le {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    (ν : Measure S) (μ : Measure X) [SFinite ν] [SFinite μ]
    {H : S → X → ℝ≥0∞} (hH : Measurable (Function.uncurry H))
    {a : S → ℝ≥0∞} (ha : Measurable a)
    (ha0 : ∀ᵐ s ∂ν, a s ≠ 0 ∧ a s ≠ ⊤) {N : ℝ≥0∞}
    (hbound : ∀ᵐ s ∂ν, (∫⁻ x, H s x ^ 2 ∂μ) ≤ a s ^ 2 * N) :
    (∫⁻ x, (∫⁻ s, H s x ∂ν) ^ 2 ∂μ) ≤ (∫⁻ s, a s ∂ν) ^ 2 * N := by
  let A := ∫⁻ s, a s ∂ν
  have hslice (x : X) : Measurable (fun s => H s x) :=
    hH.comp (measurable_id.prodMk measurable_const)
  have hpoint (x : X) : (∫⁻ s, H s x ∂ν) ^ 2 ≤ A * ∫⁻ s, H s x ^ 2 / a s ∂ν := by
    calc
      (∫⁻ s, H s x ∂ν) ^ 2 = (∫⁻ s, a s * (H s x / a s) ∂ν) ^ 2 := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards [ha0] with s hs
        simpa only [one_mul] using (ennreal_weight_cancel (k := 1) (f := H s x) hs.1 hs.2).symm
      _ ≤ A * ∫⁻ s, a s * (H s x / a s) ^ 2 ∂ν :=
        lintegral_mul_sq_le ν ha ((hslice x).div ha)
      _ = A * ∫⁻ s, H s x ^ 2 / a s ∂ν := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards [ha0] with s hs
        simpa only [one_mul] using ennreal_weight_sq_cancel (k := 1) (f := H s x) hs.1 hs.2
  have hJ : Measurable (fun p : X × S => H p.2 p.1 ^ 2 / a p.2) :=
    ((hH.comp measurable_swap).pow_const 2).div (ha.comp measurable_snd)
  calc
    (∫⁻ x, (∫⁻ s, H s x ∂ν) ^ 2 ∂μ) ≤ ∫⁻ x, A * ∫⁻ s, H s x ^ 2 / a s ∂ν ∂μ :=
      lintegral_mono hpoint
    _ = A * ∫⁻ x, ∫⁻ s, H s x ^ 2 / a s ∂ν ∂μ :=
      lintegral_const_mul A hJ.lintegral_prod_right'
    _ = A * ∫⁻ s, ∫⁻ x, H s x ^ 2 / a s ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hJ.aemeasurable]
    _ = A * ∫⁻ s, (∫⁻ x, H s x ^ 2 ∂μ) / a s ∂ν := by
      congr 1
      apply lintegral_congr
      intro s
      simp only [div_eq_mul_inv]
      exact lintegral_mul_const _ ((hH.comp (measurable_const.prodMk measurable_id)).pow_const 2)
    _ ≤ A * ∫⁻ s, (a s ^ 2 * N) / a s ∂ν := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [hbound] with s hs
      simp only [div_eq_mul_inv]
      exact mul_le_mul' hs le_rfl
    _ = A * ∫⁻ s, a s * N ∂ν := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ha0] with s hs
      rw [div_eq_mul_inv, pow_two]
      calc
        a s * a s * N * (a s)⁻¹ = (a s * N) * (a s * (a s)⁻¹) := by ac_rfl
        _ = a s * N := by rw [ENNReal.mul_inv_cancel hs.1 hs.2, mul_one]
    _ = A * (A * N) := by rw [lintegral_mul_const N ha]
    _ = _ := by simp only [A, pow_two, mul_assoc]

end Critical2DKPZ.SHF.Flow

end
