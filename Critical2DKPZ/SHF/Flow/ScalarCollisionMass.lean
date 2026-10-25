/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! The Laplace transform bounds short-time collision mass by choosing the damping rate at the reciprocal time scale. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Flow

/-- The scalar collision density is integrable on finite positive-time intervals and satisfies its Laplace bound. -/
theorem integral_scalarDensity_Ioo_le_laplace {θ rate v : ℝ}
    (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    IntegrableOn (scalarDensity θ) (Ioo 0 v) ∧
      (∫ s in Ioo 0 v, scalarDensity θ s) ≤ Real.exp (rate * v) / (Real.log rate - θ) := by
  let F := fun s => Real.exp (-(rate * s)) * scalarDensity θ s
  have hF : IntegrableOn F (Ioi 0) := integrable_scalarDensity_laplace hrate hθ
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 v) :
      scalarDensity θ s ≤ Real.exp (rate * v) * F s := by
    have harg : 0 ≤ rate * (v - s) := mul_nonneg hrate.le (sub_nonneg.mpr hs.2.le)
    calc
      scalarDensity θ s ≤ Real.exp (rate * (v - s)) * scalarDensity θ s :=
        le_mul_of_one_le_left (scalarDensity_pos θ hs.1).le (Real.one_le_exp harg)
      _ = Real.exp (rate * v) * F s := by
        dsimp only [F]
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hsub : Ioo (0 : ℝ) v ⊆ Ioi 0 := Ioo_subset_Ioi_self
  have hbound := (hF.mono_set hsub).const_mul (Real.exp (rate * v))
  have hms : Measurable (scalarDensity θ) := by
    change Measurable (fun s : ℝ => scalarDensity θ s)
    exact measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hj : IntegrableOn (scalarDensity θ) (Ioo 0 v) := by
    apply hbound.mono' hms.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (scalarDensity_pos θ hs.1)]
    exact hpoint s hs
  refine ⟨hj, ?_⟩
  calc
    (∫ s in Ioo 0 v, scalarDensity θ s) ≤ ∫ s in Ioo 0 v, Real.exp (rate * v) * F s := by
      apply integral_mono_ae hj hbound
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint s hs
    _ = Real.exp (rate * v) * ∫ s in Ioo 0 v, F s := integral_const_mul _ _
    _ ≤ Real.exp (rate * v) * ∫ s in Ioi 0, F s := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply setIntegral_mono_set hF _ (Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (Real.exp_nonneg _) (scalarDensity_pos θ hs).le
    _ = _ := by
      rw [show (∫ s in Ioi 0, F s) = (Real.log rate - θ)⁻¹ from
        integral_scalarDensity_laplace hrate hθ]
      rfl

/-- The integrated collision density has the uniform inverse-logarithmic small-time bound. -/
theorem exists_integral_scalarDensity_Ioo_le_log (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ v : ℝ, θ ≤ B → 0 < v → v ≤ 1 / 2 →
      IntegrableOn (scalarDensity θ) (Ioo 0 v) ∧
        (∫ s in Ioo 0 v, scalarDensity θ s) ≤ C / (1 + Real.log v⁻¹) := by
  let H := Real.exp (B + 1) / 2 + 1
  let C := Real.exp H * (2 + |B|)
  refine ⟨C, by dsimp [C]; positivity, fun θ v hθ hv hvhalf => ?_⟩
  let rate := Real.exp (B + 1) + v⁻¹
  have hrate : 0 < rate := add_pos (Real.exp_pos _) (inv_pos.mpr hv)
  have hlogB : B + 1 ≤ Real.log rate := by
    have h := Real.log_le_log (Real.exp_pos (B + 1))
      (le_add_of_nonneg_right (inv_nonneg.mpr hv.le) : Real.exp (B + 1) ≤ rate)
    simpa only [Real.log_exp] using h
  have hlogv : Real.log v⁻¹ ≤ Real.log rate :=
    Real.log_le_log (inv_pos.mpr hv) (le_add_of_nonneg_left (Real.exp_nonneg _) : v⁻¹ ≤ rate)
  have hd1 : 1 ≤ Real.log rate - θ := by linarith only [hlogB, hθ]
  have hd : 0 < Real.log rate - θ := lt_of_lt_of_le zero_lt_one hd1
  have hL : 0 ≤ Real.log v⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_neg hv (lt_of_le_of_lt hvhalf (by norm_num))).le
  have hL1 : 0 < 1 + Real.log v⁻¹ := by linarith only [hL]
  have hden : 1 + Real.log v⁻¹ ≤ (2 + |B|) * (Real.log rate - θ) := by
    have hLbound : Real.log v⁻¹ ≤ (Real.log rate - θ) + |B| := by
      linarith only [hlogv, hθ, le_abs_self B]
    have hm := mul_le_mul_of_nonneg_left hd1 (abs_nonneg B)
    nlinarith only [hLbound, hd1, hm]
  obtain ⟨hj, hbound⟩ := integral_scalarDensity_Ioo_le_laplace hrate (sub_pos.mp hd)
  refine ⟨hj, hbound.trans ?_⟩
  have hratev : rate * v ≤ H := by
    dsimp only [rate, H]
    rw [add_mul, inv_mul_cancel₀ hv.ne']
    have hm := mul_le_mul_of_nonneg_left hvhalf (Real.exp_nonneg (B + 1))
    linarith only [hm]
  calc
    Real.exp (rate * v) / (Real.log rate - θ) ≤ Real.exp H / (Real.log rate - θ) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hratev) hd.le
    _ ≤ C / (1 + Real.log v⁻¹) := by
      apply (div_le_div_iff₀ hd hL1).2
      have hm := mul_le_mul_of_nonneg_left hden (Real.exp_nonneg H)
      dsimp only [C]
      nlinarith only [hm]

end Critical2DKPZ.SHF.Flow

end
