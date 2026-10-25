/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# The exact Laplace transform of the scalar collision density

Gamma integration in the time variable and Fubini give the logarithmic
resolvent `(log rate - θ)⁻¹`. This supplies the small damped collision factor
in the diagram-chain estimates.
-/

public section

open MeasureTheory Set

namespace Critical2DKPZ.DeltaBose

/-- A fixed Gamma-index slice of the double Laplace integral is integrable. -/
theorem integrable_scalar_mellin (θ : ℝ) {rate u : ℝ} (hrate : 0 < rate) (hu : 0 < u) :
    IntegrableOn (fun t => Real.exp (-(rate * t)) * scalarIntegrand θ t u) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := u - 1)
    (by linarith) zero_lt_one hrate).const_mul (Real.exp (θ * u) / Real.Gamma u)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [scalarIntegrand, Real.rpow_one, neg_mul]
  ring

/-- Gamma integration cancels the reciprocal Gamma factor exactly. -/
theorem integral_scalar_mellin (θ : ℝ) {rate u : ℝ} (hrate : 0 < rate) (hu : 0 < u) :
    (∫ t in Ioi 0, Real.exp (-(rate * t)) * scalarIntegrand θ t u) =
      Real.exp ((θ - Real.log rate) * u) := by
  calc (∫ t in Ioi 0, Real.exp (-(rate * t)) * scalarIntegrand θ t u)
      = (Real.exp (θ * u) / Real.Gamma u) *
          ∫ t in Ioi 0, t ^ (u - 1) * Real.exp (-(rate * t)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        unfold scalarIntegrand
        ring
    _ = (Real.exp (θ * u) / Real.Gamma u) * ((1 / rate) ^ u * Real.Gamma u) := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hu hrate]
    _ = Real.exp (θ * u) * Real.exp (-(Real.log rate * u)) := by
      rw [one_div, Real.inv_rpow hrate.le, Real.rpow_def_of_pos hrate, Real.exp_neg]
      field_simp
    _ = Real.exp ((θ - Real.log rate) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Absolute integrability of the positive double Laplace integral above its critical rate. -/
theorem integrable_scalar_laplace_prod {θ rate : ℝ} (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(rate * p.2)) * scalarIntegrand θ p.2 p.1)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : ℝ × ℝ => Real.exp (-(rate * p.2)) * scalarIntegrand θ p.2 p.1) := by
    have hs := measurable_scalarIntegrand.comp
      (show Measurable (fun p : ℝ × ℝ => ((θ, p.2), p.1)) by fun_prop)
    exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.exp (-(rate * p.2)))).mul hs
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact integrable_scalar_mellin θ hrate hu
  · apply (integrableOn_exp_mul_Ioi (sub_neg.mpr hθ) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [← integral_scalar_mellin θ hrate hu]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos]
    exact mul_pos (Real.exp_pos _) (div_pos (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _))
      (Real.Gamma_pos_of_pos hu))

/-- The damped scalar collision density is absolutely integrable. -/
theorem integrable_scalarDensity_laplace {θ rate : ℝ} (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    IntegrableOn (fun t => Real.exp (-(rate * t)) * scalarDensity θ t) (Ioi 0) := by
  have h := (integrable_scalar_laplace_prod hrate hθ).integral_prod_right
  apply h.congr
  filter_upwards [] with t
  exact integral_const_mul _ _

/-- The exact scalar collision resolvent. -/
theorem integral_scalarDensity_laplace {θ rate : ℝ} (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    (∫ t in Ioi 0, Real.exp (-(rate * t)) * scalarDensity θ t) = (Real.log rate - θ)⁻¹ := by
  calc (∫ t in Ioi 0, Real.exp (-(rate * t)) * scalarDensity θ t)
      = ∫ t in Ioi 0, ∫ u in Ioi 0, Real.exp (-(rate * t)) * scalarIntegrand θ t u := by
        simp only [scalarDensity, integral_const_mul]
    _ = ∫ u in Ioi 0, ∫ t in Ioi 0, Real.exp (-(rate * t)) * scalarIntegrand θ t u :=
      (integral_integral_swap (integrable_scalar_laplace_prod hrate hθ)).symm
    _ = ∫ u in Ioi 0, Real.exp ((θ - Real.log rate) * u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact integral_scalar_mellin θ hrate hu
    _ = (Real.log rate - θ)⁻¹ := by
      rw [integral_exp_mul_Ioi (sub_neg.mpr hθ) 0]
      simp only [mul_zero, Real.exp_zero, neg_div, one_div]
      rw [← inv_neg, neg_sub]

/-- The collision density has finite mass on every bounded interval of
positive times, with an explicit exponential bound. -/
theorem lintegral_scalarDensity_Ioo_le {θ h : ℝ} :
    (∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal (scalarDensity θ t)) ≤
      ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * h)) := by
  let rate : ℝ := Real.exp (θ + 1)
  have hrate : 0 < rate := Real.exp_pos _
  have hlog : Real.log rate = θ + 1 := by
    dsimp [rate]
    rw [Real.log_exp]
  have hθ : θ < Real.log rate := by rw [hlog]; linarith
  have hbase : IntegrableOn
      (fun t : ℝ => Real.exp (-(rate * t)) * scalarDensity θ t) (Ioi 0) :=
    integrable_scalarDensity_laplace hrate hθ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => Real.exp (-(rate * t)) * scalarDensity θ t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (scalarDensity_pos θ ht).le
  have hLap :
      (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t)) = 1 := by
    calc
      (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t))
          = ENNReal.ofReal
              (∫ t in Ioi (0 : ℝ), Real.exp (-(rate * t)) * scalarDensity θ t) :=
                (ofReal_integral_eq_lintegral_ofReal hbase hnonneg).symm
      _ = ENNReal.ofReal ((Real.log rate - θ)⁻¹) := by
            rw [integral_scalarDensity_laplace hrate hθ]
      _ = 1 := by rw [hlog]; norm_num
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) h) :
      ENNReal.ofReal (scalarDensity θ t) ≤
        ENNReal.ofReal (Real.exp (rate * h)) *
          ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t) := by
    have htpos : 0 < t := ht.1
    have hle : Real.exp (rate * t) ≤ Real.exp (rate * h) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le hrate.le)
    have hrest : 0 ≤ Real.exp (-(rate * t)) * scalarDensity θ t :=
      mul_nonneg (Real.exp_pos _).le (scalarDensity_pos θ htpos).le
    have hreal : scalarDensity θ t ≤
        Real.exp (rate * h) * (Real.exp (-(rate * t)) * scalarDensity θ t) := by
      have hexp : Real.exp (rate * t) * Real.exp (-(rate * t)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        scalarDensity θ t = Real.exp (rate * t) *
            (Real.exp (-(rate * t)) * scalarDensity θ t) := by
              rw [← mul_assoc, hexp, one_mul]
        _ ≤ Real.exp (rate * h) *
            (Real.exp (-(rate * t)) * scalarDensity θ t) := mul_le_mul_of_nonneg_right hle hrest
    calc
      ENNReal.ofReal (scalarDensity θ t) ≤
          ENNReal.ofReal (Real.exp (rate * h) *
            (Real.exp (-(rate * t)) * scalarDensity θ t)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (Real.exp (rate * h)) *
            ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t) := by
              rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc
    (∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal (scalarDensity θ t))
        ≤ ∫⁻ t in Ioo (0 : ℝ) h,
            ENNReal.ofReal (Real.exp (rate * h)) *
              ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact hpoint t ht
    _ = ENNReal.ofReal (Real.exp (rate * h)) *
          ∫⁻ t in Ioo (0 : ℝ) h,
            ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (rate * h)) *
          ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(rate * t)) * scalarDensity θ t) := by
          gcongr
          exact Ioo_subset_Ioi_self
    _ = ENNReal.ofReal (Real.exp (rate * h)) := by rw [hLap, mul_one]
    _ = ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * h)) := by simp [rate]

end Critical2DKPZ.DeltaBose
