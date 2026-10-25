/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.VolumeScaling
public import Critical2DKPZ.SHF.DeltaBose.CausalComposition
public import Critical2DKPZ.SHF.Flow.TimeTriangle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Scalar half-power bounds for the heat-potential Schur weight -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The universal scalar majorant occurring after heat convolution. -/
noncomputable def halfTimeResolventIntegrand (s : ℝ) : ℝ := s ^ (-(1 / 2 : ℝ)) / (1 + s)

/-- The half-power singularity at zero and the three-halves tail are integrable. -/
theorem integrableOn_halfTimeResolventIntegrand : IntegrableOn halfTimeResolventIntegrand (Ioi 0) := by
  have hm : Measurable halfTimeResolventIntegrand := by
    unfold halfTimeResolventIntegrand
    exact (measurable_id.pow_const _).div (measurable_const.add measurable_id)
  have hnear : IntegrableOn halfTimeResolventIntegrand (Ioc 0 1) := by
    apply (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (r := -(1 / 2 : ℝ)) (by norm_num)).1.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hn : 0 ≤ halfTimeResolventIntegrand s :=
      div_nonneg (Real.rpow_nonneg hs.1.le _) (by linarith only [hs.1])
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact div_le_self (Real.rpow_nonneg hs.1.le _) (by linarith only [hs.1])
  have htail : IntegrableOn halfTimeResolventIntegrand (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num)
      (show (0 : ℝ) < 1 by norm_num)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans zero_lt_one hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold halfTimeResolventIntegrand; positivity)]
    calc halfTimeResolventIntegrand s ≤ s ^ (-(1 / 2 : ℝ)) / s :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hs0.le _) hs0 (by linarith)
      _ = s ^ (-(3 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one s, ← Real.rpow_add hs0]
        norm_num
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hnear.union htail

/-- A fixed finite universal constant, independent of all particle and moment parameters. -/
noncomputable def halfTimeResolventConstant : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, ENNReal.ofReal (halfTimeResolventIntegrand s)

/-- The scalar half-time resolvent constant is strictly positive. -/
theorem halfTimeResolventConstant_pos : 0 < halfTimeResolventConstant := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (halfTimeResolventIntegrand s)) := by
    unfold halfTimeResolventIntegrand
    fun_prop
  have hsupport : Set.Ioo (1 : ℝ) 2 ⊆
      Function.support (fun s : ℝ => ENNReal.ofReal (halfTimeResolventIntegrand s)) ∩ Set.Ioi 0 := by
    intro s hs
    constructor
    · rw [Function.mem_support]
      apply ne_of_gt
      apply ENNReal.ofReal_pos.mpr
      unfold halfTimeResolventIntegrand
      apply div_pos
      · exact Real.rpow_pos_of_pos (lt_trans (by norm_num) hs.1) _
      · exact add_pos (by norm_num) (lt_trans (by norm_num) hs.1)
    · exact lt_trans (by norm_num) hs.1
  rw [halfTimeResolventConstant]
  apply (setLIntegral_pos_iff hm).2
  exact lt_of_lt_of_le (by
    rw [Real.volume_Ioo]
    norm_num) (measure_mono hsupport)

/-- The universal half-time resolvent constant is finite. -/
theorem halfTimeResolventConstant_ne_top : halfTimeResolventConstant ≠ ⊤ := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] halfTimeResolventIntegrand := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact div_nonneg (Real.rpow_nonneg hs.le _) (by linarith only [show 0 < s from hs])
  change (∫⁻ s in Ioi 0, ENNReal.ofReal (halfTimeResolventIntegrand s)) ≠ ⊤
  rw [← ofReal_integral_eq_lintegral_ofReal integrableOn_halfTimeResolventIntegrand hn]
  exact ENNReal.ofReal_ne_top

/-- Positive dilation on a half-line, without any integrability assumption. -/
theorem lintegral_Ioi_mul {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioi 0, F s) = ENNReal.ofReal a * ∫⁻ u in Ioi 0, F (a * u) := by
  have h := lintegral_comp_smul_pos ha ((Ioi (0 : ℝ)).indicator F)
  have he : (fun u : ℝ => (Ioi (0 : ℝ)).indicator F (a • u)) =
      (Ioi 0).indicator (fun u => F (a * u)) := by
    funext u
    simp only [smul_eq_mul, indicator, mem_Ioi, mul_pos_iff_of_pos_left ha]
  rw [he, lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi] at h
  simp only [Module.finrank_self, pow_one] at h
  have hi : ENNReal.ofReal a * ENNReal.ofReal a⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one]
  calc (∫⁻ s in Ioi 0, F s) = (ENNReal.ofReal a * ENNReal.ofReal a⁻¹) * ∫⁻ s in Ioi 0, F s := by
          rw [hi, one_mul]
    _ = _ := by rw [mul_assoc, ← h]

/-- Exact scalar homogeneity after the half-time heat convolution estimate. -/
theorem lintegral_halfTime_div_add {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (-(1 / 2 : ℝ)) / (t + s))) =
      ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * halfTimeResolventConstant := by
  rw [lintegral_Ioi_mul ht]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold halfTimeResolventConstant
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [← ENNReal.ofReal_mul ht.le,
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos ht _).le, halfTimeResolventIntegrand,
    Real.mul_rpow ht.le hu.le]
  congr 1
  field_simp





end Critical2DKPZ.DeltaBose
