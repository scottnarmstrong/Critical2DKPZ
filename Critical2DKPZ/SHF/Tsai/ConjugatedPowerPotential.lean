/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.HeatPotential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Radial power potentials for the conjugated swapping Schur test -/

@[expose] public noncomputable section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Radial unit-distance heat profile with a general potential exponent. -/
def powerHeatProfile (b t : ℝ) : ℝ :=
  t ^ (-b / 2) * (2 * Real.pi * t)⁻¹ * Real.exp (-1 / (2 * t))

/-- A general radial heat potential has finite mass at unit distance when
its spatial singularity exponent is strictly between zero and two. -/
theorem integrableOn_powerHeatProfile {b : ℝ} (hb : 0 < b) (hb2 : b < 2) :
    IntegrableOn (powerHeatProfile b) (Ioi 0) := by
  have hm : Measurable (powerHeatProfile b) := by unfold powerHeatProfile; fun_prop
  have hn : IntegrableOn (powerHeatProfile b) (Ioc 0 1) := by
    have hi : IntegrableOn (fun t : ℝ => t ^ (-b / 2)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -b / 2)).1
    apply (hi.const_mul Real.pi⁻¹).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have he : Real.exp (-1 / (2 * t)) ≤ 2 * t := by
      have h := (Real.mul_exp_neg_le_exp_neg_one (1 / (2 * t))).trans
        (Real.exp_le_one_iff.mpr (by norm_num : -(1 : ℝ) ≤ 0))
      have hden : 0 < 2 * t := by positivity
      have heq : Real.exp (-1 / (2 * t)) = Real.exp (-(1 / (2 * t))) := by congr 1; ring
      rw [heq]
      apply (div_le_one hden).mp
      simpa only [div_eq_mul_inv, mul_comm, one_mul] using h
    have hnonneg : 0 ≤ powerHeatProfile b t := by unfold powerHeatProfile; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      powerHeatProfile b t ≤ t ^ (-b / 2) * (2 * Real.pi * t)⁻¹ * (2 * t) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Real.pi⁻¹ * t ^ (-b / 2) := by field_simp [ht0.ne']
  have ht : IntegrableOn (powerHeatProfile b) (Ioi 1) := by
    have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -b / 2 - 1 < -1)
      (show (0 : ℝ) < 1 by norm_num)
    apply (hi.const_mul (2 * Real.pi)⁻¹).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hnonneg : 0 ≤ powerHeatProfile b t := by unfold powerHeatProfile; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      powerHeatProfile b t ≤ t ^ (-b / 2) * (2 * Real.pi * t)⁻¹ := by
        apply mul_le_of_le_one_right (by positivity)
        apply Real.exp_le_one_iff.mpr
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      _ = (2 * Real.pi)⁻¹ * t ^ (-b / 2 - 1) := by
        rw [Real.rpow_sub ht0, Real.rpow_one]
        field_simp
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hn.union ht

/-- The unit-distance constant for a spatial power potential. -/
def powerHeatConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (powerHeatProfile b t)

/-- Gaussian mixture realizing a radial spatial power. -/
def powerHeatPotential (b : ℝ) (x : Plane) : ℝ≥0∞ :=
  ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-b / 2) * heatKernel t x)

/-- Exact scaling of the radial integrand at a nonzero spatial point. -/
theorem powerHeatPotential_integrand_scale (b : ℝ) {x : Plane} (hx : x ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    ‖x‖ ^ 2 * ((‖x‖ ^ 2 * t) ^ (-b / 2) * heatKernel (‖x‖ ^ 2 * t) x) =
      (‖x‖ ^ 2) ^ (-b / 2) * powerHeatProfile b t := by
  have hr : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have he : -‖x‖ ^ 2 / (2 * (‖x‖ ^ 2 * t)) = -1 / (2 * t) := by
    field_simp
  unfold heatKernel powerHeatProfile
  rw [he, Real.mul_rpow hr.le ht.le]
  field_simp [ne_of_gt hr]

/-- Exact radial homogeneity, obtained by the positive time dilation
`t = ‖x‖² u`; no integrability assumption is needed for this identity. -/
theorem powerHeatPotential_eq_norm_sq_rpow (b : ℝ) {x : Plane} (hx : x ≠ 0) :
    powerHeatPotential b x = ENNReal.ofReal ((‖x‖ ^ 2) ^ (-b / 2)) * powerHeatConstant b := by
  have hr : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  unfold powerHeatPotential
  rw [lintegral_Ioi_mul hr, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    (∫⁻ t in Ioi 0, ENNReal.ofReal (‖x‖ ^ 2) *
        ENNReal.ofReal ((‖x‖ ^ 2 * t) ^ (-b / 2) * heatKernel (‖x‖ ^ 2 * t) x)) =
        ∫⁻ t in Ioi 0, ENNReal.ofReal ((‖x‖ ^ 2) ^ (-b / 2)) *
          ENNReal.ofReal (powerHeatProfile b t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← ENNReal.ofReal_mul hr.le, powerHeatPotential_integrand_scale b hx ht,
        ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The unit-distance potential constant is finite in the Riesz range. -/
theorem powerHeatConstant_ne_top {b : ℝ} (hb : 0 < b) (hb2 : b < 2) :
    powerHeatConstant b ≠ ⊤ := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] powerHeatProfile b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    unfold powerHeatProfile
    positivity
  unfold powerHeatConstant
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_powerHeatProfile hb hb2) hn]
  exact ENNReal.ofReal_ne_top

/-- The radial unit-distance potential constant is strictly positive. -/
theorem powerHeatConstant_pos (b : ℝ) : 0 < powerHeatConstant b := by
  have hm : Measurable (fun t => ENNReal.ofReal (powerHeatProfile b t)) := by
    unfold powerHeatProfile
    fun_prop
  have hs : Ioo (1 : ℝ) 2 ⊆
      Function.support (fun t => ENNReal.ofReal (powerHeatProfile b t)) ∩ Ioi 0 := by
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    refine ⟨?_, ht0⟩
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    unfold powerHeatProfile
    positivity
  have hi : 0 < volume (Ioo (1 : ℝ) 2) := by rw [Real.volume_Ioo]; norm_num
  exact (setLIntegral_pos_iff hm).mpr (hi.trans_le (measure_mono hs))

/-- The canonical Schur potential is the exponent-one member of the radial family. -/
theorem powerHeatPotential_one (x : Plane) : powerHeatPotential 1 x = heatPotential x := by
  unfold powerHeatPotential heatPotential heatPotentialIntegrand
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  norm_num

/-- Away from the origin, every radial power potential is a fixed multiple
of the corresponding power of the canonical Schur potential. -/
theorem powerHeatPotential_eq_heatPotential_rpow {b : ℝ} (hb : 0 < b)
    {x : Plane} (hx : x ≠ 0) :
    powerHeatPotential b x =
      (powerHeatConstant b / powerHeatConstant 1 ^ b) * heatPotential x ^ b := by
  have hr : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hc0 : powerHeatConstant 1 ^ b ≠ 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos hb).not.mpr (ne_of_gt (powerHeatConstant_pos 1))
  have hct : powerHeatConstant 1 ^ b ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hb.le (powerHeatConstant_ne_top (by norm_num) (by norm_num))
  have hpow : heatPotential x ^ b =
      ENNReal.ofReal ((‖x‖ ^ 2) ^ (-b / 2)) * powerHeatConstant 1 ^ b := by
    rw [← powerHeatPotential_one x, powerHeatPotential_eq_norm_sq_rpow 1 hx,
      ENNReal.mul_rpow_of_nonneg _ _ hb.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hr.le _) hb.le,
      ← Real.rpow_mul hr.le]
    rw [show (-(1 : ℝ) / 2) * b = -b / 2 by ring]
  have hcancel : (powerHeatConstant b / powerHeatConstant 1 ^ b) *
      powerHeatConstant 1 ^ b = powerHeatConstant b := by
    rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hc0 hct, mul_one]
  rw [powerHeatPotential_eq_norm_sq_rpow b hx, hpow]
  calc
    _ = ENNReal.ofReal ((‖x‖ ^ 2) ^ (-b / 2)) *
        ((powerHeatConstant b / powerHeatConstant 1 ^ b) * powerHeatConstant 1 ^ b) := by
      rw [hcancel]
    _ = _ := by ac_rfl

end Critical2DKPZ.SHF.Tsai

end
