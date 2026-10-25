/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Squared L2 bounds for sums of positive kernels -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_two, ENNReal.rpow_one] using
    ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)

/-- Add two positive kernel bounds before any real-valued conversion. -/
theorem kernelSum_l2_sq_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {K L : X → Y → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (_hL : Measurable (Function.uncurry L))
    {A B : ℝ≥0∞} {f : Y → ℝ≥0∞} (hf : Measurable f)
    (hKA : (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ) ≤ A * ∫⁻ y, f y ^ 2 ∂ν)
    (hLB : (∫⁻ x, (∫⁻ y, L x y * f y ∂ν) ^ 2 ∂μ) ≤ B * ∫⁻ y, f y ^ 2 ∂ν) :
    (∫⁻ x, (∫⁻ y, (K x y + L x y) * f y ∂ν) ^ 2 ∂μ) ≤
      (2 * (A + B)) * ∫⁻ y, f y ^ 2 ∂ν := by
  have hKf (x : X) : Measurable (fun y => K x y * f y) :=
    (hK.comp (measurable_const.prodMk measurable_id)).mul hf
  have hAK := measurable_kernelAction ν hK hf
  have hpoint (x : X) : (∫⁻ y, (K x y + L x y) * f y ∂ν) ^ 2 ≤
      2 * ((∫⁻ y, K x y * f y ∂ν) ^ 2 + (∫⁻ y, L x y * f y ∂ν) ^ 2) := by
    simp_rw [add_mul]
    rw [lintegral_add_left (hKf x)]
    exact ennreal_add_sq_le _ _
  calc
    _ ≤ ∫⁻ x, 2 * ((∫⁻ y, K x y * f y ∂ν) ^ 2 +
        (∫⁻ y, L x y * f y ∂ν) ^ 2) ∂μ := lintegral_mono hpoint
    _ = 2 * ((∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ) +
        ∫⁻ x, (∫⁻ y, L x y * f y ∂ν) ^ 2 ∂μ) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hAK.pow_const 2)]
    _ ≤ 2 * (A * (∫⁻ y, f y ^ 2 ∂ν) + B * ∫⁻ y, f y ^ 2 ∂ν) :=
      mul_le_mul' le_rfl (add_le_add hKA hLB)
    _ = _ := by rw [← add_mul, mul_assoc]

end Critical2DKPZ.SHF.Flow

end
