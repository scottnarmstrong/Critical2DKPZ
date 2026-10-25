/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ScalarLaplace
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The exponentially tilted scalar renewal law

The Euler-shifted scalar density becomes a probability density after exponential
tilting above its critical abscissa. Its compactification has explicit moments.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ.Renewal

/-- The exponentially damped positive-time scalar density, normalized to unit mass when the damping exceeds the critical abscissa. -/
def tiltedScalarDensity (θ a t : ℝ) : ℝ :=
  (Real.log a - θ) * (Real.exp (-(a * t)) * DeltaBose.scalarDensity θ t)

/-- The tilted scalar renewal density is measurable. -/
theorem measurable_tiltedScalarDensity (θ a : ℝ) : Measurable (tiltedScalarDensity θ a) := by
  unfold tiltedScalarDensity
  exact measurable_const.mul ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-(a * t)))).mul
    (DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)))

/-- The tilted scalar renewal density is strictly positive. -/
theorem tiltedScalarDensity_pos {θ a t : ℝ} (hθ : θ < Real.log a) (ht : 0 < t) :
    0 < tiltedScalarDensity θ a t :=
  mul_pos (sub_pos.mpr hθ) (mul_pos (Real.exp_pos _) (DeltaBose.scalarDensity_pos θ ht))

/-- The tilted scalar renewal density is integrable on positive times. -/
theorem integrableOn_tiltedScalarDensity (θ : ℝ) {a : ℝ} (ha : 0 < a) (hθ : θ < Real.log a) :
    IntegrableOn (tiltedScalarDensity θ a) (Ioi 0) :=
  (integrableOn_damped_scalarDensity θ ha hθ).const_mul _

/-- The normalized tilted scalar renewal density has total integral one. -/
theorem integral_tiltedScalarDensity (θ : ℝ) {a : ℝ} (ha : 0 < a) (hθ : θ < Real.log a) :
    (∫ t in Ioi 0, tiltedScalarDensity θ a t) = 1 := by
  unfold tiltedScalarDensity
  rw [integral_const_mul, integral_damped_scalarDensity θ ha hθ]
  exact mul_one_div_cancel (sub_pos.mpr hθ).ne'

/-- The scalar renewal law under exponential tilting, supported on strictly positive times. -/
def scalarRenewalLaw (θ : ℝ) (a : {a : ℝ // 0 < a}) (hθ : θ < Real.log a) :
    ProbabilityMeasure ℝ :=
  ⟨(volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (tiltedScalarDensity θ a t)),
    ⟨by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
        ← ofReal_integral_eq_lintegral_ofReal (integrableOn_tiltedScalarDensity θ a.2 hθ)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact (tiltedScalarDensity_pos hθ ht).le),
        integral_tiltedScalarDensity θ a.2 hθ, ENNReal.ofReal_one]⟩⟩

/-- The density defining the scalar renewal law is measurable. -/
theorem measurable_scalarRenewalLaw_density (θ : ℝ) (a : {a : ℝ // 0 < a}) :
    Measurable (fun t => ENNReal.ofReal (tiltedScalarDensity θ a t)) :=
  (measurable_tiltedScalarDensity θ a).ennreal_ofReal

instance scalarRenewalLaw_noAtoms (θ : ℝ) (a : {a : ℝ // 0 < a}) (hθ : θ < Real.log a) :
    NullSingletonClass (scalarRenewalLaw θ a hθ : Measure ℝ) := by
  change NullSingletonClass ((volume.restrict (Ioi 0)).withDensity _)
  infer_instance

/-- Integration against the scalar renewal law equals integration against its density on positive times. -/
theorem integral_scalarRenewalLaw (θ : ℝ) (a : {a : ℝ // 0 < a})
    (hθ : θ < Real.log a) (f : ℝ → ℝ) :
    (∫ t, f t ∂(scalarRenewalLaw θ a hθ : Measure ℝ)) =
      ∫ t in Ioi 0, tiltedScalarDensity θ a t * f t := by
  rw [scalarRenewalLaw, ProbabilityMeasure.coe_mk,
    integral_withDensity_eq_integral_toReal_smul (measurable_scalarRenewalLaw_density θ a)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (tiltedScalarDensity_pos hθ ht).le, smul_eq_mul]

/-- Exponential compactification of the nonnegative time axis. -/
def compactifyTime (t : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-max t 0), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _))⟩

/-- The time compactification is continuous. -/
theorem continuous_compactifyTime : Continuous compactifyTime := by
  unfold compactifyTime
  fun_prop

/-- The real coordinate of a compactified nonnegative time is its negative exponential. -/
theorem compactifyTime_coe {t : ℝ} (ht : 0 ≤ t) :
    (compactifyTime t : ℝ) = Real.exp (-t) := by
  simp only [compactifyTime, max_eq_left ht]

/-- The tilted scalar renewal law after compactification. -/
def compactScalarRenewalLaw (θ : ℝ) (a : {a : ℝ // 0 < a}) (hθ : θ < Real.log a) :
    ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  (scalarRenewalLaw θ a hθ).map compactifyTime


/-- Compactified moments are the normalized scalar Laplace transform. -/
theorem integral_pow_compactScalarRenewalLaw (θ : ℝ) (a : {a : ℝ // 0 < a})
    (hθ : θ < Real.log a) (k : ℕ) :
    (∫ x : Icc (0 : ℝ) 1, (x : ℝ) ^ k ∂(compactScalarRenewalLaw θ a hθ : Measure _)) =
      (Real.log a - θ) / (Real.log (a + k) - θ) := by
  rw [compactScalarRenewalLaw, ProbabilityMeasure.toMeasure_map,
    integral_map continuous_compactifyTime.measurable.aemeasurable (by fun_prop),
    integral_scalarRenewalLaw]
  have ha' : 0 < (a : ℝ) + k := add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg _)
  have hθ' : θ < Real.log ((a : ℝ) + k) :=
    hθ.trans_le (Real.log_le_log a.2 (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  calc
    _ = (Real.log a - θ) * ∫ t in Ioi 0,
        Real.exp (-(((a : ℝ) + k) * t)) * DeltaBose.scalarDensity θ t := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change tiltedScalarDensity θ a t * (compactifyTime t : ℝ) ^ k =
        (Real.log a - θ) * (Real.exp (-(((a : ℝ) + k) * t)) * DeltaBose.scalarDensity θ t)
      rw [compactifyTime_coe ht.le, ← Real.exp_nat_mul]
      unfold tiltedScalarDensity
      have he : Real.exp (-(a * t)) * Real.exp ((k : ℝ) * -t) =
          Real.exp (-(((a : ℝ) + k) * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.log a - θ) * (Real.exp (-(a * t)) * Real.exp ((k : ℝ) * -t)) *
            DeltaBose.scalarDensity θ t := by ring
        _ = _ := by rw [he]; ring
    _ = _ := by
      rw [integral_damped_scalarDensity θ ha' hθ']
      ring

end Critical2DKPZ.Renewal

end
