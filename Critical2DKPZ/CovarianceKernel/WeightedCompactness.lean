/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.Envelope
public import Critical2DKPZ.CovarianceKernel.WeakLpCompactness
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! A polynomial weight makes the logarithmic covariance envelope square-integrable. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.CovarianceKernel

/-- A positive polynomial weight that puts the bounded-at-infinity covariance envelope in `L²`. -/
def covarianceDecayWeight (z : Plane) : ℝ := (1 + ‖z‖) ^ (-(2 : ℝ))

/-- The decay weight `(1 + ‖z‖) ^ (-2)` is positive. -/
theorem covarianceDecayWeight_pos (z : Plane) : 0 < covarianceDecayWeight z := by
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The decay weight `(1 + ‖z‖) ^ (-2)` is at most `1`. -/
theorem covarianceDecayWeight_le_one (z : Plane) : covarianceDecayWeight z ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by have hz := norm_nonneg z; linarith) (by norm_num)

/-- The envelope times the polynomial weight is square-integrable on the whole plane. -/
theorem integrable_sq_covarianceLogEnvelope_mul_decayWeight :
    Integrable (fun z : Plane => (covarianceDecayWeight z * covarianceLogEnvelope z) ^ 2)
      volume := by
  let F : Plane → ℝ := fun z => (covarianceDecayWeight z * covarianceLogEnvelope z) ^ 2
  have hF : AEStronglyMeasurable F volume := by
    have hm : Measurable F := by
      simpa only [F] using (by fun_prop [covarianceDecayWeight, covarianceLogEnvelope] :
        Measurable (fun z : Plane =>
          (covarianceDecayWeight z * covarianceLogEnvelope z) ^ 2))
    exact hm.aestronglyMeasurable
  have hlocal : IntegrableOn F (Metric.ball (0 : Plane) 1) volume := by
    have hEnv := integrableOn_covarianceLogEnvelope_sq_ball (show (0 : ℝ) < 1 by norm_num)
    have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) 1),
        ‖F z‖ ≤ covarianceLogEnvelope z ^ 2 := by
      filter_upwards [] with z
      have hw := covarianceDecayWeight_pos z
      have hw1 := covarianceDecayWeight_le_one z
      have he := covarianceLogEnvelope_pos z
      dsimp [F]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (mul_nonneg hw.le he.le) he.le).2
        (mul_le_of_le_one_left he.le hw1)
    exact hEnv.mono' hF.restrict hbound
  have hdecay : Integrable (fun z : Plane => (1 + ‖z‖) ^ (-(4 : ℝ))) volume := by
    apply integrable_one_add_norm
    norm_num [Plane]
  have houtside : IntegrableOn F (Metric.ball (0 : Plane) 1)ᶜ volume := by
    have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) 1)ᶜ,
        ‖F z‖ ≤ (1 + ‖z‖) ^ (-(4 : ℝ)) := by
      filter_upwards [ae_restrict_mem (measurableSet_ball.compl)] with z hz
      have hzNorm : 1 ≤ ‖z‖ := by
        simpa [Metric.mem_ball, dist_zero_right, not_lt] using hz
      have hEnv := covarianceLogEnvelope_eq_one_of_one_le_norm z hzNorm
      have hwSq : covarianceDecayWeight z ^ 2 = (1 + ‖z‖) ^ (-(4 : ℝ)) := by
        have hbase : 0 ≤ 1 + ‖z‖ := by positivity
        rw [covarianceDecayWeight, ← Real.rpow_natCast, ← Real.rpow_mul hbase]
        norm_num
      dsimp [F]
      rw [abs_of_nonneg (sq_nonneg _), hEnv, mul_one, ← hwSq]
    exact hdecay.integrableOn.mono' hF.restrict hbound
  have hunion := hlocal.union houtside
  have hcover : Metric.ball (0 : Plane) 1 ∪ (Metric.ball (0 : Plane) 1)ᶜ = Set.univ :=
    Set.union_compl_self (Metric.ball (0 : Plane) 1)
  rw [hcover, IntegrableOn, Measure.restrict_univ] at hunion
  exact hunion

/-- The logarithmic covariance envelope multiplied by the decay weight is square-integrable. -/
theorem covarianceDecayWeight_mul_covarianceLogEnvelope_memLp_two :
    MemLp (fun z : Plane => covarianceDecayWeight z * covarianceLogEnvelope z) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by fun_prop [covarianceDecayWeight,
    covarianceLogEnvelope])).2
  simpa only [Pi.mul_apply] using integrable_sq_covarianceLogEnvelope_mul_decayWeight

end Critical2DKPZ.CovarianceKernel

end
