/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedPotentialOrigin
public import Critical2DKPZ.SHF.DeltaBose.PotentialRows
import Mathlib.Tactic

/-! # Time integration of fractional Gaussian potential rows -/

@[expose] public noncomputable section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Exact doubled-time change of variables for a fractional potential. -/
theorem lintegral_rpow_heatKernel_double_eq (b : ℝ) (x : Plane) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-b / 2)) *
      ENNReal.ofReal (heatKernel (2 * t) x)) =
      ENNReal.ofReal ((2 * (2 : ℝ) ^ (-b / 2))⁻¹) * powerHeatPotential b x := by
  let H : ℝ≥0∞ := ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-b / 2)) *
    ENNReal.ofReal (heatKernel (2 * t) x)
  have he : powerHeatPotential b x = ENNReal.ofReal (2 * (2 : ℝ) ^ (-b / 2)) * H := by
    unfold powerHeatPotential
    conv_lhs => rw [lintegral_Ioi_mul (show (0 : ℝ) < 2 by norm_num)]
    change _ = ENNReal.ofReal (2 * (2 : ℝ) ^ (-b / 2)) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-b / 2)) * ENNReal.ofReal (heatKernel (2 * t) x)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (-b / 2)),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le]
    congr 1
    ring
  have hc : 0 < 2 * (2 : ℝ) ^ (-b / 2) := by positivity
  have hi : ENNReal.ofReal ((2 * (2 : ℝ) ^ (-b / 2))⁻¹) *
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-b / 2)) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_pos.mpr hc).le, inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  change H = _
  rw [he, ← mul_assoc, hi, one_mul]

/-- Finite scalar factor in the time-integrated fractional potential row. -/
def fractionalPotentialRowConstant (b : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((2 * Real.pi)⁻¹) * halfTimeResolventConstant) ^ b *
    ENNReal.ofReal ((2 * (2 : ℝ) ^ (-b / 2))⁻¹) *
      (powerHeatConstant b / powerHeatConstant 1 ^ b)

/-- Time integration of the fractional Gaussian row preserves its spatial
power weight, including at the singular origin. -/
theorem lintegral_fractionalPotentialRowBound_heatKernel_le {b : ℝ} (hb : 0 < b) (x : Plane) :
    (∫⁻ t in Ioi 0, heatPotentialRowBound t ^ b *
      ENNReal.ofReal (heatKernel (2 * t) x)) ≤
      fractionalPotentialRowConstant b * heatPotential x ^ b := by
  let C₀ : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi)⁻¹) * halfTimeResolventConstant
  have hCt : C₀ ^ b ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hb.le
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top halfTimeResolventConstant_ne_top)
  have he {t : ℝ} (ht : 0 < t) : heatPotentialRowBound t ^ b =
      C₀ ^ b * ENNReal.ofReal (t ^ (-b / 2)) := by
    have hbase : heatPotentialRowBound t =
        C₀ * ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
      unfold heatPotentialRowBound C₀
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
      ac_rfl
    rw [hbase, ENNReal.mul_rpow_of_nonneg _ _ hb.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) hb.le,
      ← Real.rpow_mul ht.le, show (-(1 / 2 : ℝ)) * b = -b / 2 by ring]
  calc
    _ = C₀ ^ b * (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-b / 2)) *
        ENNReal.ofReal (heatKernel (2 * t) x)) := by
      rw [← lintegral_const_mul' _ _ hCt]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [he ht, mul_assoc]
    _ = (C₀ ^ b * ENNReal.ofReal ((2 * (2 : ℝ) ^ (-b / 2))⁻¹)) *
        powerHeatPotential b x := by rw [lintegral_rpow_heatKernel_double_eq, mul_assoc]
    _ ≤ (C₀ ^ b * ENNReal.ofReal ((2 * (2 : ℝ) ^ (-b / 2))⁻¹)) *
        ((powerHeatConstant b / powerHeatConstant 1 ^ b) * heatPotential x ^ b) :=
      mul_le_mul' le_rfl (powerHeatPotential_le_heatPotential_rpow hb x)
    _ = _ := by dsimp [fractionalPotentialRowConstant, C₀]; ac_rfl

/-- The integrated fractional row factor is finite throughout the range
used by the `Lᵖ` power-weighted Schur test. -/
theorem fractionalPotentialRowConstant_ne_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    fractionalPotentialRowConstant b ≠ ⊤ := by
  have hc0 : powerHeatConstant 1 ^ b ≠ 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos hb).not.mpr (ne_of_gt (powerHeatConstant_pos 1))
  unfold fractionalPotentialRowConstant
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hb.le
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top halfTimeResolventConstant_ne_top))
      ENNReal.ofReal_ne_top
  · rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top (powerHeatConstant_ne_top hb (by linarith))
      (ENNReal.inv_ne_top.mpr hc0)

end Critical2DKPZ.SHF.Tsai

end
