/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Primitive
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivative of the scalar primitive in the critical parameter

The exact scalar scaling relation transfers the time fundamental theorem of calculus
to the critical parameter: `∂_θ ∫₀ᵗ j_θ = t j_θ(t)`. This identifies the marked renewal
limit without differentiating a singular Gamma integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The scalar renewal primitive equals its interval integral. -/
theorem scalarRenewalPrimitive_eq_intervalIntegral (θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    scalarRenewalPrimitive θ t = ∫ u in 0..t, DeltaBose.scalarDensity θ u :=
  (intervalIntegral.integral_of_le ht).symm

/-- Rescaling time in the scalar renewal primitive shifts its critical parameter. -/
theorem scalarRenewalPrimitive_scale (θ : ℝ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    scalarRenewalPrimitive (θ + Real.log a) t = scalarRenewalPrimitive θ (a * t) := by
  rw [scalarRenewalPrimitive_eq_intervalIntegral _ ht,
    scalarRenewalPrimitive_eq_intervalIntegral _ (mul_nonneg ha.le ht)]
  calc
    _ = ∫ u in 0..t, a * DeltaBose.scalarDensity θ (a * u) := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le ht]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact (DeltaBose.scalarDensity_scale θ ha hu.1).symm
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      simpa only [smul_eq_mul, mul_zero] using
        intervalIntegral.smul_integral_comp_mul_left (DeltaBose.scalarDensity θ) a (a := 0) (b := t)

/-- The time derivative of the scalar renewal primitive is the scalar density. -/
theorem hasDerivAt_scalarRenewalPrimitive_time (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarRenewalPrimitive θ) (DeltaBose.scalarDensity θ t) t := by
  have hi : IntervalIntegrable (DeltaBose.scalarDensity θ) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr (integrableOn_scalarDensity_Ioc θ t)
  have hm : Measurable (DeltaBose.scalarDensity θ) :=
    DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hc : ContinuousAt (DeltaBose.scalarDensity θ) t := by
    have h := DeltaBose.continuousOn_scalarDensity.continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds (show (0 : ℝ) < (θ, t).2 from ht))
    exact h.comp (continuous_const.prodMk continuous_id).continuousAt
  have h := intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with u hu
  exact scalarRenewalPrimitive_eq_intervalIntegral θ hu.le

/-- The scalar primitive's critical-parameter derivative is the local scalar density times time. -/
theorem hasDerivAt_scalarRenewalPrimitive_parameter (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun v => scalarRenewalPrimitive v t) (t * DeltaBose.scalarDensity θ t) θ := by
  have he := (((hasDerivAt_id θ).sub_const θ).exp).mul_const t
  simp only [id_eq, sub_self, Real.exp_zero, mul_one, one_mul] at he
  have htime : HasDerivAt (scalarRenewalPrimitive θ) (DeltaBose.scalarDensity θ t)
      (Real.exp (θ - θ) * t) := by
    simpa only [sub_self, Real.exp_zero, one_mul] using!
      hasDerivAt_scalarRenewalPrimitive_time θ ht
  have h := htime.comp θ he
  rw [mul_comm] at h
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro v
  have hs := scalarRenewalPrimitive_scale θ (Real.exp_pos (v - θ)) ht.le
  rw [Real.log_exp, add_sub_cancel] at hs
  exact hs

end Critical2DKPZ.Renewal

end
