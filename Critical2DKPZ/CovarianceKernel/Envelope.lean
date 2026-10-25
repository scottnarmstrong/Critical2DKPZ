/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Local square-integrability of the envelope -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.CovarianceKernel

/-- The logarithmic profile in the covariance estimate. -/
def covarianceLogEnvelope (z : Plane) : ℝ :=
  1 + Real.log (1 + max 0 (Real.log ‖z‖⁻¹))

/-- The covariance envelope is everywhere positive. -/
theorem covarianceLogEnvelope_pos (z : Plane) : 0 < covarianceLogEnvelope z := by
  unfold covarianceLogEnvelope
  have hmax : 0 ≤ max 0 (Real.log ‖z‖⁻¹) := le_max_left _ _
  have hlog : 0 ≤ Real.log (1 + max 0 (Real.log ‖z‖⁻¹)) :=
    Real.log_nonneg (by linarith)
  linarith

/-- Near the origin the square of the covariance bound envelope is bounded by an integrable inverse power. -/
theorem covarianceLogEnvelope_sq_le_inv_of_norm_le_one
    (z : Plane) (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    covarianceLogEnvelope z ^ 2 ≤ 9 * ‖z‖⁻¹ := by
  let u : ℝ := ‖z‖⁻¹
  have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hu : 1 ≤ u := by
    dsimp [u]
    exact (one_le_inv₀ hrpos).2 hz
  have huNonneg : 0 ≤ u := le_trans (by norm_num) hu
  have hloguNonneg : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlogu : Real.log u ≤ 2 * Real.sqrt u := by
    calc
      Real.log u ≤ u ^ (1 / (2 : ℝ)) / (1 / (2 : ℝ)) :=
        Real.log_le_rpow_div huNonneg (by norm_num)
      _ = 2 * Real.sqrt u := by rw [Real.sqrt_eq_rpow]; norm_num; ring
  have hlogNested : Real.log (1 + Real.log u) ≤ Real.log u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 : ℝ) + Real.log u by linarith)
    linarith
  have hprof : covarianceLogEnvelope z = 1 + Real.log (1 + Real.log u) := by
    change 1 + Real.log (1 + max 0 (Real.log u)) = _
    rw [max_eq_right hloguNonneg]
  have hprofNonneg : 0 ≤ covarianceLogEnvelope z := by
    rw [hprof]
    have hlog : 0 ≤ Real.log (1 + Real.log u) :=
      Real.log_nonneg (by linarith)
    linarith
  have hsqrt : 1 ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt huNonneg]
  have hprofUpper : covarianceLogEnvelope z ≤ 3 * Real.sqrt u := by
    rw [hprof]
    linarith
  have hsq := (sq_le_sq₀ hprofNonneg (by positivity : 0 ≤ 3 * Real.sqrt u)).2 hprofUpper
  calc
    covarianceLogEnvelope z ^ 2 ≤ (3 * Real.sqrt u) ^ 2 := hsq
    _ = 9 * ‖z‖⁻¹ := by
      rw [mul_pow, Real.sq_sqrt huNonneg]
      norm_num [u]

/-- The covariance bound envelope is constant outside the unit ball. -/
theorem covarianceLogEnvelope_eq_one_of_one_le_norm
    (z : Plane) (hz : 1 ≤ ‖z‖) : covarianceLogEnvelope z = 1 := by
  have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  rw [covarianceLogEnvelope, Real.log_inv,
    max_eq_left (neg_nonpos.mpr hlog)]
  simp

/-- The square of the covariance bound envelope is integrable on every bounded ball. -/
theorem integrableOn_covarianceLogEnvelope_sq_ball {R : ℝ} (_hR : 0 < R) :
    IntegrableOn (fun z : Plane => covarianceLogEnvelope z ^ 2)
      (Metric.ball 0 R) volume := by
  let C : ℝ := max 9 R
  have hC9 : 9 ≤ C := le_max_left _ _
  have hCR : R ≤ C := le_max_right _ _
  have hmeas : AEStronglyMeasurable
      (fun z : Plane => covarianceLogEnvelope z ^ 2) volume := by
    exact (by fun_prop [covarianceLogEnvelope] :
      Measurable (fun z : Plane => covarianceLogEnvelope z ^ 2)).aestronglyMeasurable
  have hdecay : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) R),
      ‖covarianceLogEnvelope z ^ 2‖ ≤ C * ‖z‖ ^ (-(1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : Plane))]
      with z hzball hz0
    have hzNorm : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hzball
    have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (covarianceLogEnvelope z)),
      Real.rpow_neg_one]
    by_cases hzle : ‖z‖ ≤ 1
    · have hlocal := covarianceLogEnvelope_sq_le_inv_of_norm_le_one z hzle hz0
      calc
        covarianceLogEnvelope z ^ 2 ≤ 9 * ‖z‖⁻¹ := hlocal
        _ ≤ C * ‖z‖⁻¹ := by
          exact mul_le_mul_of_nonneg_right hC9 (inv_nonneg.mpr (norm_nonneg _))
    · have honeNorm : 1 ≤ ‖z‖ := le_of_not_ge hzle
      have hprofile := covarianceLogEnvelope_eq_one_of_one_le_norm z honeNorm
      have hrleC : ‖z‖ ≤ C := le_trans hzNorm.le hCR
      have hratio : 1 ≤ C / ‖z‖ := (one_le_div₀ hrpos).2 hrleC
      simpa [hprofile, div_eq_mul_inv] using hratio
  exact integrableOn_ball_of_norm_le_rpow
    (by norm_num [Plane] : 1 ≤ Module.finrank ℝ Plane)
    (by norm_num [Plane] : (1 : ℝ) < Module.finrank ℝ Plane)
    hdecay hmeas

/-- The covariance bound envelope belongs to local `L²`, uniformly on each compact set. -/
theorem covarianceLogEnvelope_memLp_two_on_compact (K : Set Plane) (hK : IsCompact K) :
    MemLp covarianceLogEnvelope 2 (volume.restrict K) := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_lt
  have hsubset : K ⊆ Metric.ball (0 : Plane) R := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact hR z hz
  have hsqOn : IntegrableOn (fun z : Plane => covarianceLogEnvelope z ^ 2) K volume :=
    (integrableOn_covarianceLogEnvelope_sq_ball hRpos).mono_set hsubset
  have hmeas : Measurable covarianceLogEnvelope := by
    fun_prop [covarianceLogEnvelope]
  have hstrong : AEStronglyMeasurable covarianceLogEnvelope (volume.restrict K) :=
    hmeas.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hstrong).2 hsqOn.integrable

end Critical2DKPZ.CovarianceKernel

end
