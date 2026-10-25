/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedPowerPotential
import Mathlib.Tactic

/-! # The singular origin in the conjugated Schur potential -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The canonical heat potential diverges at the origin. Time dilation by
four would otherwise contradict its strict positivity and finiteness. -/
theorem heatPotential_zero_eq_top : heatPotential (0 : Plane) = ⊤ := by
  have hfour : (4 : ℝ) ^ (-(1 : ℝ) / 2) = 1 / 2 := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg, ← Real.sqrt_eq_rpow]
    all_goals norm_num
  have hscale : powerHeatPotential 1 (0 : Plane) =
      ENNReal.ofReal (1 / 2 : ℝ) * powerHeatPotential 1 (0 : Plane) := by
    unfold powerHeatPotential
    conv_lhs => rw [lintegral_Ioi_mul (show (0 : ℝ) < 4 by norm_num)]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    simp only [heatKernel_at_zero]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht.le,
      hfour]
    field_simp
  rw [powerHeatPotential_one] at hscale
  by_contra htop
  have hz : heatPotential (0 : Plane) ≠ 0 := ne_of_gt (heatPotential_pos _)
  have hbad : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
    (ENNReal.mul_le_mul_iff_left hz htop).mp (by simpa only [one_mul] using hscale.le)
  norm_num at hbad

/-- The radial comparison holds also at the singular origin, as an inequality
between nonnegative extended-real quantities. -/
theorem powerHeatPotential_le_heatPotential_rpow {b : ℝ} (hb : 0 < b) (x : Plane) :
    powerHeatPotential b x ≤
      (powerHeatConstant b / powerHeatConstant 1 ^ b) * heatPotential x ^ b := by
  by_cases hx : x = 0
  · subst x
    have hc0 : powerHeatConstant 1 ^ b ≠ 0 :=
      (ENNReal.rpow_eq_zero_iff_of_pos hb).not.mpr (ne_of_gt (powerHeatConstant_pos 1))
    have hct : powerHeatConstant 1 ^ b ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hb.le (powerHeatConstant_ne_top (by norm_num) (by norm_num))
    have hcancel : (powerHeatConstant b / powerHeatConstant 1 ^ b) *
        powerHeatConstant 1 ^ b = powerHeatConstant b := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hc0 hct, mul_one]
    have hD0 : powerHeatConstant b / powerHeatConstant 1 ^ b ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hcancel
      exact (ne_of_gt (powerHeatConstant_pos b)) hcancel.symm
    rw [heatPotential_zero_eq_top, ENNReal.top_rpow_of_pos hb, ENNReal.mul_top hD0]
    exact le_top
  · exact (powerHeatPotential_eq_heatPotential_rpow hb hx).le

end Critical2DKPZ.SHF.Tsai

end
