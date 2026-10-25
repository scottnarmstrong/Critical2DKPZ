/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Tech
public import Critical2DKPZ.SHF.DeltaBose.WeightedSchur
import Mathlib.Tactic

/-! # Positive Schur estimates with power weights -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The power-weighted Hölder estimate for one row. Auxiliary weights may be
infinite on a null set; only their almost-everywhere positivity and finiteness
are used in cancellation. -/
theorem lintegral_kernel_rpow_le_weighted_row {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) {p : ℝ} (hp : 1 < p) {k w f : Y → ℝ≥0∞}
    (hk : Measurable k) (hw : Measurable w) (hf : Measurable f)
    (hwfinite : ∀ᵐ y ∂ν, w y ≠ 0 ∧ w y ≠ ⊤) :
    (∫⁻ y, k y * f y ∂ν) ^ p ≤
      (∫⁻ y, k y * w y ∂ν) ^ (p - 1) *
        ∫⁻ y, k y * (f y ^ p / w y ^ (p - 1)) ∂ν := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  let ρ : Measure Y := ν.withDensity (k * w)
  have he1 : (∫⁻ y, f y / w y ∂ρ) = ∫⁻ y, k y * f y ∂ν := by
    dsimp only [ρ]
    rw [lintegral_withDensity_eq_lintegral_mul ν (f := k * w)
      (g := fun y => f y / w y) (hk.mul hw) (hf.div hw)]
    apply lintegral_congr_ae
    filter_upwards [hwfinite] with y hy
    exact ennreal_weight_cancel hy.1 hy.2
  have he2 : (∫⁻ y, (f y / w y) ^ p ∂ρ) =
      ∫⁻ y, k y * (f y ^ p / w y ^ (p - 1)) ∂ν := by
    dsimp only [ρ]
    rw [lintegral_withDensity_eq_lintegral_mul ν (f := k * w)
      (g := fun y => (f y / w y) ^ p) (hk.mul hw) ((hf.div hw).pow_const p)]
    apply lintegral_congr_ae
    filter_upwards [hwfinite] with y hy
    have hpow : w y ^ p = w y ^ (p - 1) * w y := by
      calc
        _ = w y ^ ((p - 1) + 1) := by congr 1; ring
        _ = _ := by rw [ENNReal.rpow_add_of_nonneg _ _ hpm.le zero_le_one, ENNReal.rpow_one]
    change (k y * w y) * (f y / w y) ^ p = _
    rw [ENNReal.div_rpow_of_nonneg _ _ hp0.le, hpow, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inr hy.2) (Or.inr hy.1), div_eq_mul_inv]
    calc
      (k y * w y) * (f y ^ p * ((w y ^ (p - 1))⁻¹ * (w y)⁻¹)) =
          (k y * (f y ^ p * (w y ^ (p - 1))⁻¹)) * (w y * (w y)⁻¹) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hy.1 hy.2, mul_one]
  have hemass : (∫⁻ y, (1 : ℝ≥0∞) ^ q ∂ρ) = ∫⁻ y, k y * w y ∂ν := by
    simp only [ENNReal.one_rpow]
    dsimp only [ρ]
    rw [lintegral_withDensity_eq_lintegral_mul ν (f := k * w)
      (g := fun _ => 1) (hk.mul hw) measurable_const]
    simp only [Pi.mul_apply, mul_one]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ hpq (g := fun _ => 1)
    (hf.div hw).aemeasurable (measurable_const.aemeasurable)
  simp only [Pi.mul_apply, Pi.div_apply, mul_one] at hh
  rw [he1, he2, hemass] at hh
  have hpower := ENNReal.rpow_le_rpow hh hp0.le
  have hqp : (1 / q : ℝ) * p = p - 1 := by dsimp [q]; field_simp
  calc
    _ ≤ ((∫⁻ y, k y * (f y ^ p / w y ^ (p - 1)) ∂ν) ^ (1 / p : ℝ) *
      (∫⁻ y, k y * w y ∂ν) ^ (1 / q : ℝ)) ^ p := hpower
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
        one_div_mul_cancel hp0.ne', ENNReal.rpow_one, ← ENNReal.rpow_mul, hqp,
        mul_comm]

/-- Schur's test on `Lᵖ` with a singular power weight. The row uses `w`
and the column uses its conjugate power `w ^ (p - 1)`. -/
theorem lintegral_kernel_rpow_le_power_schur {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {p : ℝ} (hp : 1 < p)
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {v : X → ℝ≥0∞} {w : Y → ℝ≥0∞} (hv : Measurable v) (hw : Measurable w)
    (hwfinite : ∀ᵐ y ∂ν, w y ≠ 0 ∧ w y ≠ ⊤) {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y * w y ∂ν ≤ A * v x)
    (hcol : ∀ y, ∫⁻ x, K x y * v x ^ (p - 1) ∂μ ≤ B * w y ^ (p - 1))
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ p ∂μ) ≤
      A ^ (p - 1) * B * ∫⁻ y, f y ^ p ∂ν := by
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hkx (x : X) : Measurable (K x) := hK.comp (measurable_const.prodMk measurable_id)
  let F : Y → ℝ≥0∞ := fun y => f y ^ p / w y ^ (p - 1)
  have hF : Measurable F := (hf.pow_const p).div (hw.pow_const _)
  have hpoint (x : X) : (∫⁻ y, K x y * f y ∂ν) ^ p ≤
      A ^ (p - 1) * (v x ^ (p - 1) * ∫⁻ y, K x y * F y ∂ν) := by
    have h := lintegral_kernel_rpow_le_weighted_row ν hp (hkx x) hw hf hwfinite
    calc
      _ ≤ (∫⁻ y, K x y * w y ∂ν) ^ (p - 1) * ∫⁻ y, K x y * F y ∂ν := h
      _ ≤ (A * v x) ^ (p - 1) * ∫⁻ y, K x y * F y ∂ν :=
        mul_le_mul' (ENNReal.rpow_le_rpow (hrow x) hpm.le) le_rfl
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hpm.le, mul_assoc]
  have hProd : Measurable (fun z : X × Y =>
      v z.1 ^ (p - 1) * (K z.1 z.2 * F z.2)) :=
    ((hv.comp measurable_fst).pow_const _).mul (hK.mul (hF.comp measurable_snd))
  calc
    _ ≤ ∫⁻ x, A ^ (p - 1) * (v x ^ (p - 1) * ∫⁻ y, K x y * F y ∂ν) ∂μ :=
      lintegral_mono hpoint
    _ = A ^ (p - 1) * ∫⁻ x, v x ^ (p - 1) * ∫⁻ y, K x y * F y ∂ν ∂μ :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpm.le hA)
    _ = A ^ (p - 1) * ∫⁻ x, ∫⁻ y, v x ^ (p - 1) * (K x y * F y) ∂ν ∂μ := by
      congr 1
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ ((hkx x).mul hF)).symm
    _ = A ^ (p - 1) * ∫⁻ y, ∫⁻ x, v x ^ (p - 1) * (K x y * F y) ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hProd.aemeasurable]
    _ ≤ A ^ (p - 1) * ∫⁻ y, B * f y ^ p ∂ν := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [hwfinite] with y hy
      have hky : Measurable (fun x => K x y * v x ^ (p - 1)) :=
        (hK.comp (measurable_id.prodMk measurable_const)).mul (hv.pow_const _)
      calc
        (∫⁻ x, v x ^ (p - 1) * (K x y * F y) ∂μ) =
            (∫⁻ x, K x y * v x ^ (p - 1) ∂μ) * F y := by
          rw [← lintegral_mul_const _ hky]
          apply lintegral_congr
          intro x
          ac_rfl
        _ ≤ (B * w y ^ (p - 1)) * F y := mul_le_mul' (hcol y) le_rfl
        _ = B * f y ^ p := ennreal_weight_cancel
          ((ENNReal.rpow_eq_zero_iff_of_pos hpm).not.mpr hy.1)
          (ENNReal.rpow_ne_top_of_nonneg hpm.le hy.2)
    _ = _ := by rw [lintegral_const_mul' _ _ hB, mul_assoc]

end Critical2DKPZ.SHF.Tsai

end
