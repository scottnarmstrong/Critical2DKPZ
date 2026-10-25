/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Schur estimates for nonnegative kernels

We use squared lower-integral norms, so the estimates apply before finiteness
of the kernel operator has been established. In particular, there is no
conversion of a possibly infinite integral to a real number.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Cauchy--Schwarz for a nonnegative function against a nonnegative density. -/
theorem lintegral_mul_sq_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {k f : Y → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ y, k y * f y ∂ν) ^ 2 ≤
      (∫⁻ y, k y ∂ν) * ∫⁻ y, k y * f y ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.withDensity k)
    Real.HolderConjugate.two_two measurable_const.aemeasurable hf.aemeasurable
    (f := fun _ => 1)
  have hs := pow_le_pow_left' h 2
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, mul_pow,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hs
  norm_num at hs
  simpa only [lintegral_withDensity_eq_lintegral_mul ν hk hf,
    lintegral_withDensity_eq_lintegral_mul ν hk (hf.pow_const 2),
    Pi.mul_apply] using hs

/-- Transfer a squared kernel-action bound through pointwise domination. -/
theorem lintegral_kernel_sq_dominate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {K L : X → Y → ℝ≥0∞} {C D : ℝ≥0∞}
    (hC : C ≠ ⊤) (hKL : ∀ x y, K x y ≤ C * L x y) (f : Y → ℝ≥0∞)
    (hL : (∫⁻ x, (∫⁻ y, L x y * f y ∂ν) ^ 2 ∂μ) ≤ D * ∫⁻ y, f y ^ 2 ∂ν) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ) ≤
      C ^ 2 * D * ∫⁻ y, f y ^ 2 ∂ν := by
  have hx (x : X) : (∫⁻ y, K x y * f y ∂ν) ≤ C * ∫⁻ y, L x y * f y ∂ν := by
    calc
      (∫⁻ y, K x y * f y ∂ν) ≤ ∫⁻ y, C * (L x y * f y) ∂ν := by
        apply lintegral_mono
        intro y
        simpa only [mul_assoc] using mul_le_mul' (hKL x y) (le_refl (f y))
      _ = C * ∫⁻ y, L x y * f y ∂ν := lintegral_const_mul' C _ hC
  calc (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ)
      ≤ ∫⁻ x, C ^ 2 * (∫⁻ y, L x y * f y ∂ν) ^ 2 ∂μ := by
        apply lintegral_mono
        intro x
        simpa only [mul_pow] using pow_le_pow_left' (hx x) 2
    _ = C ^ 2 * ∫⁻ x, (∫⁻ y, L x y * f y ∂ν) ^ 2 ∂μ :=
      lintegral_const_mul' _ _ (by finiteness)
    _ ≤ C ^ 2 * (D * ∫⁻ y, f y ^ 2 ∂ν) := mul_le_mul' le_rfl hL
    _ = C ^ 2 * D * ∫⁻ y, f y ^ 2 ∂ν := (mul_assoc _ _ _).symm

/-- Schur's test, in squared `L²` form, including kernels with extended values. -/
theorem lintegral_kernel_sq_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {A B : ℝ≥0∞} (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ) ≤
      A * B * ∫⁻ y, f y ^ 2 ∂ν := by
  have hx (x : X) : Measurable (K x) :=
    hK.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable (fun p : X × Y => K p.1 p.2 * f p.2 ^ 2) :=
    hK.mul ((hf.comp measurable_snd).pow_const 2)
  calc
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ 2 ∂μ)
        ≤ ∫⁻ x, A * ∫⁻ y, K x y * f y ^ 2 ∂ν ∂μ := by
          apply lintegral_mono
          intro x
          exact (lintegral_mul_sq_le ν (hx x) hf).trans
            (mul_le_mul' (hrow x) le_rfl)
    _ = A * ∫⁻ x, ∫⁻ y, K x y * f y ^ 2 ∂ν ∂μ :=
      lintegral_const_mul A hF.lintegral_prod_right'
    _ = A * ∫⁻ y, ∫⁻ x, K x y * f y ^ 2 ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hF.aemeasurable]
    _ ≤ A * ∫⁻ y, B * f y ^ 2 ∂ν := by
      gcongr with y
      have hy : Measurable (fun x => K x y) :=
        hK.comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const _ hy]
      exact mul_le_mul' (hcol y) le_rfl
    _ = A * B * ∫⁻ y, f y ^ 2 ∂ν := by
      rw [lintegral_const_mul B (hf.pow_const 2), mul_assoc]

end Critical2DKPZ.DeltaBose
