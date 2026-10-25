/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.VolumeScaling
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! # The finite endpoint-time beta factor

The two incoming square-root singularities are integrated together before
squaring an operator estimate. Their normalized product is integrable, and its
integral is independent of the total available endpoint time.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The beta-integral profile `u ^ (-1 / 2) * (1 - u) ^ (-1 / 2)`. -/
def endpointBetaProfile (u : ℝ) : ℝ :=
  u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ))

/-- The endpoint beta profile is integrable on the open unit interval. -/
theorem integrableOn_endpointBetaProfile : IntegrableOn endpointBetaProfile (Ioo 0 1) := by
  let p : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ))
  have hp : IntervalIntegrable p volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hq : IntervalIntegrable (fun u => p (1 - u)) volume 0 1 := by
    simpa only [sub_zero, sub_self] using (hp.comp_sub_left 1).symm
  have hp' := hp.1.mono_set (Ioo_subset_Ioc_self : Ioo (0 : ℝ) 1 ⊆ Ioc 0 1)
  have hq' := hq.1.mono_set (Ioo_subset_Ioc_self : Ioo (0 : ℝ) 1 ⊆ Ioc 0 1)
  let C : ℝ := (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hC : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hm : Measurable endpointBetaProfile :=
    (measurable_id.pow_const _).mul ((measurable_const.sub measurable_id).pow_const _)
  apply ((hp'.add hq').const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hu0 := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
  have hv0 := Real.rpow_nonneg (sub_pos.mpr hu.2).le (-(1 / 2 : ℝ))
  change ‖p u * p (1 - u)‖ ≤ C * (p u + p (1 - u))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0 hv0)]
  by_cases h : u ≤ 1 / 2
  · have hb : (1 - u) ^ (-(1 / 2 : ℝ)) ≤ C :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
    calc
      p u * p (1 - u) ≤ p u * C := mul_le_mul_of_nonneg_left hb hu0
      _ ≤ C * (p u + p (1 - u)) := by dsimp only [p] at *; nlinarith only [hC, hv0]
  · have hb : u ^ (-(1 / 2 : ℝ)) ≤ C :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_lt (lt_of_not_ge h)) (by norm_num)
    calc
      p u * p (1 - u) ≤ C * p (1 - u) := mul_le_mul_of_nonneg_right hb hv0
      _ ≤ C * (p u + p (1 - u)) := by dsimp only [p] at *; nlinarith only [hC, hu0]

/-- The integral of the endpoint beta profile over the open unit interval. -/
def endpointBetaConstant : ℝ≥0∞ :=
  ∫⁻ u in Ioo 0 1, ENNReal.ofReal (endpointBetaProfile u)

/-- The endpoint beta integral is finite. -/
theorem endpointBetaConstant_ne_top : endpointBetaConstant ≠ ⊤ := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] endpointBetaProfile := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (sub_pos.mpr hu.2).le _)
  rw [endpointBetaConstant, ← ofReal_integral_eq_lintegral_ofReal integrableOn_endpointBetaProfile hn]
  exact ENNReal.ofReal_ne_top

/-- The endpoint beta integral is independent of the total positive time. -/
theorem lintegral_endpoint_half_powers {t : ℝ} (ht : 0 < t) :
    (∫⁻ r in Ioo 0 t, ENNReal.ofReal
      (r ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-(1 / 2 : ℝ)))) = endpointBetaConstant := by
  have hscale := lintegral_Ioo_mul ht 0 1 (fun r => ENNReal.ofReal
    (r ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-(1 / 2 : ℝ))))
  simp only [mul_zero, mul_one] at hscale
  rw [hscale]
  have htPow : t ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) = t⁻¹ := by
    rw [← Real.rpow_add ht]
    norm_num only [show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]
  have he (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      (t * u) ^ (-(1 / 2 : ℝ)) * (t - t * u) ^ (-(1 / 2 : ℝ)) =
        t⁻¹ * endpointBetaProfile u := by
    rw [show t - t * u = t * (1 - u) by ring,
      Real.mul_rpow ht.le hu.1.le, Real.mul_rpow ht.le (sub_pos.mpr hu.2).le]
    calc
      _ = (t ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))) * endpointBetaProfile u := by
        unfold endpointBetaProfile
        ring
      _ = _ := by rw [htPow]
  calc
    ENNReal.ofReal t * (∫⁻ u in Ioo 0 1, ENNReal.ofReal
        ((t * u) ^ (-(1 / 2 : ℝ)) * (t - t * u) ^ (-(1 / 2 : ℝ)))) =
        ENNReal.ofReal t * ∫⁻ u in Ioo 0 1,
          ENNReal.ofReal t⁻¹ * ENNReal.ofReal (endpointBetaProfile u) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      rw [he u hu, ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    _ = ENNReal.ofReal t * (ENNReal.ofReal t⁻¹ * endpointBetaConstant) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ = endpointBetaConstant := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one, one_mul]

end Critical2DKPZ.SHF.Flow

end
