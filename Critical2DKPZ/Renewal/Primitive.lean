/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.HorizonCutoff
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The cumulative scalar renewal density

The singular scalar density is integrable at time zero. Its positive, continuous
primitive is the coefficient of `log N` in the free second moment.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The scalar renewal mass accumulated up to a macroscopic time. -/
def scalarRenewalPrimitive (θ t : ℝ) : ℝ := ∫ u in Ioc 0 t, DeltaBose.scalarDensity θ u

/-- The scalar renewal density is integrable from zero to every positive finite horizon. -/
theorem integrableOn_scalarDensity_Ioc (θ t : ℝ) :
    IntegrableOn (DeltaBose.scalarDensity θ) (Ioc 0 t) := by
  let a := Real.exp (θ + 1)
  have ha : 0 < a := Real.exp_pos _
  have hθ : θ < Real.log a := by rw [Real.log_exp]; linarith
  have hi := ((integrableOn_damped_scalarDensity θ ha hθ).mono_set
    (show Ioc 0 t ⊆ Ioi 0 from fun _ h => h.1)).const_mul (Real.exp (a * t))
  apply hi.mono' ((DeltaBose.measurable_scalarDensity.comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  change ‖DeltaBose.scalarDensity θ u‖ ≤
    Real.exp (a * t) * (Real.exp (-(a * u)) * DeltaBose.scalarDensity θ u)
  rw [Real.norm_eq_abs, abs_of_pos (DeltaBose.scalarDensity_pos θ hu.1)]
  have he : 1 ≤ Real.exp (a * t) * Real.exp (-(a * u)) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    nlinarith only [ha, hu.2]
  have hj := (DeltaBose.scalarDensity_pos θ hu.1).le
  calc
    _ ≤ (Real.exp (a * t) * Real.exp (-(a * u))) * DeltaBose.scalarDensity θ u :=
      le_mul_of_one_le_left hj he
    _ = _ := by ring

/-- The scalar renewal primitive is strictly positive at every positive time. -/
theorem scalarRenewalPrimitive_pos (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < scalarRenewalPrimitive θ t := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact (DeltaBose.scalarDensity_pos θ hu.1).le)
    (integrableOn_scalarDensity_Ioc θ t)).mpr
  have hs : Function.support (DeltaBose.scalarDensity θ) ∩ Ioc 0 t = Ioc 0 t :=
    inter_eq_right.mpr fun u hu => (DeltaBose.scalarDensity_pos θ hu.1).ne'
  rw [hs, Real.volume_Ioc, sub_zero, ENNReal.ofReal_pos]
  exact ht

/-- The scalar renewal primitive is continuous at every positive time. -/
theorem continuousAt_scalarRenewalPrimitive (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (scalarRenewalPrimitive θ) t := by
  have hi : IntegrableOn (DeltaBose.scalarDensity θ) (Icc 0 (t + 1)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr (integrableOn_scalarDensity_Ioc θ (t + 1))
  exact ((intervalIntegral.continuousOn_primitive hi) t ⟨ht.le, le_add_of_nonneg_right zero_le_one⟩).continuousAt
    (Icc_mem_nhds ht (lt_add_one t))

end Critical2DKPZ.Renewal

end
