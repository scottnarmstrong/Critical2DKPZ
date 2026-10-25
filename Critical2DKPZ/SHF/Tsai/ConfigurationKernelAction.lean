/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms
import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual `L²` action of a bounded configuration kernel

A positive form bound controls the positive action on the norm of arbitrary
`L²` data. The real kernel action is dominated by this positive action. This
retains the literal integral when passing to bounded operators.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The right-to-left real integral action of a positive configuration kernel. -/
def configurationKernelAction {n : ℕ} (K : Configuration n → Configuration n → ℝ≥0∞)
    (F : Configuration n → ℝ) (x : Configuration n) : ℝ :=
  ∫ y, (K x y).toReal * F y

/-- The squared positive action bound also applies to norms of a.e.-measurable real data. -/
theorem configurationKernel_enormAction_sq_le {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hKF : FormBound volume volume K c) {F : Configuration n → ℝ}
    (hF : AEStronglyMeasurable F volume) :
    (∫⁻ x, (∫⁻ y, K x y * ‖F y‖ₑ) ^ (2 : ℝ)) ≤ c ^ 2 * ∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) := by
  let v : Configuration n → ℝ≥0∞ := hF.enorm.mk (fun y => ‖F y‖ₑ)
  have hv : Measurable v := hF.enorm.measurable_mk
  have heq : (fun y => ‖F y‖ₑ) =ᵐ[volume] v := hF.enorm.ae_eq_mk
  have hact (x : Configuration n) : (∫⁻ y, K x y * ‖F y‖ₑ) = ∫⁻ y, K x y * v y := by
    apply lintegral_congr_ae
    filter_upwards [heq] with y hy
    rw [hy]
  have hnorm : (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ)) = ∫⁻ y, v y ^ (2 : ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [heq] with y hy
    rw [hy]
  simp_rw [hact, hnorm]
  exact (formBound_iff_l2_sq_le volume volume hK c).1 hKF v hv

/-- The kernel action is almost everywhere strongly measurable for almost everywhere strongly measurable inputs, with value zero at nonintegrable rows. -/
theorem aestronglyMeasurable_configurationKernelAction {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {F : Configuration n → ℝ} (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (configurationKernelAction K F) volume :=
  ((hK.ennreal_toReal.aestronglyMeasurable).mul hF.comp_snd).integral_prod_right'

/-- The norm of the real action is dominated by the positive kernel action on the input norm. -/
theorem enorm_configurationKernelAction_le {n : ℕ}
    (K : Configuration n → Configuration n → ℝ≥0∞) (F : Configuration n → ℝ) (x : Configuration n) :
    ‖configurationKernelAction K F x‖ₑ ≤ ∫⁻ y, K x y * ‖F y‖ₑ := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro y
  change ‖(K x y).toReal * F y‖ₑ ≤ K x y * ‖F y‖ₑ
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul' ENNReal.ofReal_toReal_le le_rfl

/-- The finite positive form constant controls the `L²` seminorm of the literal real action. -/
theorem eLpNorm_configurationKernelAction_le {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hKF : FormBound volume volume K c) {F : Configuration n → ℝ} (hF : MemLp F 2) :
    eLpNorm (configurationKernelAction K F) 2 ≤ c * eLpNorm F 2 := by
  have hm := aestronglyMeasurable_configurationKernelAction hK hF.aestronglyMeasurable
  have hsq := configurationKernel_enormAction_sq_le hK hKF hF.aestronglyMeasurable
  have hbound : (∫⁻ x, ‖configurationKernelAction K F x‖ₑ ^ (2 : ℝ)) ≤
      c ^ 2 * ∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ) := by
    apply le_trans _ hsq
    apply lintegral_mono
    intro x
    exact ENNReal.monotone_rpow_of_nonneg (by norm_num) (enorm_configurationKernelAction_le K F x)
  have hroot : (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = eLpNorm F 2 := by
    simpa only [ENNReal.toReal_ofNat] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hF.aestronglyMeasurable).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hm]
  simp only [ENNReal.toReal_ofNat]
  have h := ENNReal.monotone_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hbound
  dsimp only at h
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_natCast_mul] at h
  norm_num at h
  simp only [ENNReal.rpow_two] at hroot
  rw [hroot] at h
  simpa only [ENNReal.rpow_two] using h

/-- A finite positive form bound makes the actual action an `L²` function. -/
theorem memLp_configurationKernelAction {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    {F : Configuration n → ℝ} (hF : MemLp F 2) : MemLp (configurationKernelAction K F) 2 := by
  exact (eLpNorm_configurationKernelAction_le hK hKF hF).trans_lt
    (ENNReal.mul_lt_top hc.lt_top hF.eLpNorm_lt_top)

/-- Almost every row of the real action is absolutely integrable for `L²` input.
This companion justifies the integral used in `configurationKernelAction`. -/
theorem ae_integrable_configurationKernelAction {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    {F : Configuration n → ℝ} (hF : MemLp F 2) :
    ∀ᵐ x : Configuration n, Integrable (fun y => (K x y).toReal * F y) := by
  let H (x : Configuration n) := ∫⁻ y, K x y * ‖F y‖ₑ
  have hHm : AEMeasurable H volume :=
    (hK.aemeasurable.mul hF.aestronglyMeasurable.enorm.comp_snd).lintegral_prod_right'
  have hFfin : (∫⁻ y, ‖F y‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa only [ENNReal.toReal_ofNat] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hF.eLpNorm_lt_top
  have hIfin : (∫⁻ x, H x ^ (2 : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hc) hFfin.ne)
      (configurationKernel_enormAction_sq_le hK hKF hF.aestronglyMeasurable)
  have hfinite := ae_lt_top' (hHm.pow_const (2 : ℝ)) hIfin
  filter_upwards [hfinite] with x hx
  have hHfin : H x ≠ ⊤ :=
    (ENNReal.pow_ne_top_iff.1 (by simpa only [ENNReal.rpow_two] using hx.ne)).resolve_right
      (by norm_num : (2 : ℕ) ≠ 0)
  have hm : AEStronglyMeasurable (fun y => (K x y).toReal * F y) volume :=
    ((Measurable.comp (g := Function.uncurry K) (f := fun y => (x, y)) hK
      (measurable_const.prodMk measurable_id)).ennreal_toReal.aestronglyMeasurable).mul
        hF.aestronglyMeasurable
  refine ⟨hm, hasFiniteIntegral_iff_enorm.2 ?_⟩
  apply lt_of_le_of_lt _ hHfin.lt_top
  apply lintegral_mono
  intro y
  change ‖(K x y).toReal * F y‖ₑ ≤ K x y * ‖F y‖ₑ
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul' ENNReal.ofReal_toReal_le le_rfl

/-- Changing the input on a volume-null set preserves every real row integral. -/
theorem configurationKernelAction_congr_ae {n : ℕ}
    (K : Configuration n → Configuration n → ℝ≥0∞) {F G : Configuration n → ℝ}
    (h : F =ᵐ[volume] G) : configurationKernelAction K F = configurationKernelAction K G := by
  funext x
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- Additivity of the actual action on `L²` data, almost everywhere in its output coordinate. -/
theorem configurationKernelAction_add_ae {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    {F G : Configuration n → ℝ} (hF : MemLp F 2) (hG : MemLp G 2) :
    configurationKernelAction K (F + G) =ᵐ[volume]
      configurationKernelAction K F + configurationKernelAction K G := by
  filter_upwards [ae_integrable_configurationKernelAction hK hc hKF hF,
    ae_integrable_configurationKernelAction hK hc hKF hG] with x hx hx'
  simp only [configurationKernelAction, Pi.add_apply, mul_add]
  exact integral_add hx hx'

/-- Scalar multiplication commutes with the actual row integral. -/
theorem configurationKernelAction_smul {n : ℕ}
    (K : Configuration n → Configuration n → ℝ≥0∞) (F : Configuration n → ℝ) (a : ℝ) :
    configurationKernelAction K (a • F) = a • configurationKernelAction K F := by
  funext x
  simp only [configurationKernelAction, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

end Critical2DKPZ.SHF.Tsai

end
