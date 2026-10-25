/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedDuality
public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelAction
import Mathlib.Tactic

/-! # Weighted `Lᵖ` bounds and integrability of the literal kernel action -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A finite conjugated positive form bound gives integrable kernel rows on
weighted `Lᵖ` data and controls the norm of their literal real integral action. -/
theorem WeightedFormBound.integrable_and_eLpNorm_configurationKernelAction_le {n : ℕ}
    {p : ℝ} (hp : 1 < p) {wX wY : Configuration n → ℝ}
    (hwX : Measurable wX)
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hKF : WeightedFormBound volume volume (fun x => -wX x) wY p (p / (p - 1)) K c)
    {F : Configuration n → ℝ} (hf : Measurable F)
    (hF : MemLp (fun y => Real.exp (wY y) * F y) (ENNReal.ofReal p)) :
    (∀ᵐ x : Configuration n, Integrable (fun y => (K x y).toReal * F y)) ∧
      eLpNorm (fun x => Real.exp (wX x) * configurationKernelAction K F x) (ENNReal.ofReal p) ≤
        c * eLpNorm (fun y => Real.exp (wY y) * F y) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpz : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  let B : Configuration n → ℝ≥0∞ := fun x => ∫⁻ y, K x y * ‖F y‖ₑ
  let WX : Configuration n → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (wX x))
  let N : ℝ≥0∞ := (∫⁻ y, (‖F y‖ₑ * ENNReal.ofReal (Real.exp (wY y))) ^ p) ^ (1 / p : ℝ)
  have hB : Measurable B := measurable_kernelAction volume hK hf.enorm
  have hWX : Measurable WX := hwX.exp.ennreal_ofReal
  have hcancel (x : Configuration n) : WX x * ENNReal.ofReal (Real.exp (-wX x)) = 1 := by
    dsimp [WX]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one]
  have hpair : ∀ q : Configuration n → ℝ≥0∞, Measurable q →
      (∫⁻ x, q x * (B x * WX x)) ≤
        c * N * (∫⁻ x, q x ^ (p / (p - 1))) ^ (1 / (p / (p - 1)) : ℝ) := by
    intro q hq
    have h := hKF (fun y => ‖F y‖ₑ) (fun x => q x * WX x) hf.enorm (hq.mul hWX)
    change (∫⁻ x, q x * WX x * B x) ≤ c * N *
      (∫⁻ x, ((q x * WX x) * ENNReal.ofReal (Real.exp (-wX x))) ^ (p / (p - 1))) ^
        (1 / (p / (p - 1)) : ℝ) at h
    have he (x : Configuration n) : q x * WX x * ENNReal.ofReal (Real.exp (-wX x)) = q x := by
      rw [mul_assoc, hcancel, mul_one]
    have hLeft : (∫⁻ x, q x * (B x * WX x)) = ∫⁻ x, q x * WX x * B x :=
      lintegral_congr (fun _ => by ac_rfl)
    rw [hLeft]
    simpa only [he] using h
  have hdual := lintegral_rpow_root_le_of_dual volume hp (hB.mul hWX) hpair
  have hInputNorm (y : Configuration n) :
      ‖Real.exp (wY y) * F y‖ₑ = ‖F y‖ₑ * ENNReal.ofReal (Real.exp (wY y)) := by
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_comm _ _
  have hN : N = eLpNorm (fun y => Real.exp (wY y) * F y) (ENNReal.ofReal p) := by
    symm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpz ENNReal.ofReal_ne_top hF.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofReal hp0.le]
    simp_rw [hInputNorm]
    rfl
  rw [hN] at hdual
  have hRootFinite : (∫⁻ x, (B x * WX x) ^ p) ^ (1 / p : ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (ne_of_lt hF.eLpNorm_lt_top)) hdual
  have hIntegralFinite : (∫⁻ x, (B x * WX x) ^ p) ≠ ⊤ := by
    intro htop
    apply hRootFinite
    rw [htop, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0)]
  have hBfinite : ∀ᵐ x : Configuration n, B x ≠ ⊤ := by
    filter_upwards [ae_lt_top ((hB.mul hWX).pow_const p) hIntegralFinite] with x hx
    intro htop
    have hW0 : WX x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    change (B x * WX x) ^ p < ⊤ at hx
    rw [htop, ENNReal.top_mul hW0, ENNReal.top_rpow_of_pos hp0] at hx
    exact lt_irrefl _ hx
  have hRowNorm (x : Configuration n) : (∫⁻ y, ‖(K x y).toReal * F y‖ₑ) ≤ B x := by
    apply lintegral_mono
    intro y
    change ‖(K x y).toReal * F y‖ₑ ≤ K x y * ‖F y‖ₑ
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul' ENNReal.ofReal_toReal_le le_rfl
  have hRows : ∀ᵐ x : Configuration n, Integrable (fun y => (K x y).toReal * F y) := by
    filter_upwards [hBfinite] with x hx
    refine ⟨?_, hasFiniteIntegral_iff_enorm.mpr ((hRowNorm x).trans_lt (lt_top_iff_ne_top.mpr hx))⟩
    exact ((hK.comp (measurable_const.prodMk measurable_id)).ennreal_toReal.aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  refine ⟨hRows, ?_⟩
  have hAction := aestronglyMeasurable_configurationKernelAction hK hf.aestronglyMeasurable
  have hWeightedAction : AEStronglyMeasurable
      (fun x => Real.exp (wX x) * configurationKernelAction K F x) volume :=
    hwX.exp.aestronglyMeasurable.mul hAction
  have hDom (x : Configuration n) :
      ‖Real.exp (wX x) * configurationKernelAction K F x‖ₑ ≤ B x * WX x := by
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ WX x * B x := mul_le_mul' le_rfl (enorm_configurationKernelAction_le K F x)
      _ = _ := mul_comm _ _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpz ENNReal.ofReal_ne_top hWeightedAction]
  simp only [ENNReal.toReal_ofReal hp0.le]
  apply le_trans _ hdual
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hp0.le)
  exact lintegral_mono (fun x => ENNReal.rpow_le_rpow (hDom x) hp0.le)

end Critical2DKPZ.SHF.Tsai

end
