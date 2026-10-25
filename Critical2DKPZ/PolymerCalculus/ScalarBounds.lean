/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.GaussianityDefect
public import Critical2DKPZ.GaussianConvexity.Derivative
public import Critical2DKPZ.GaussianConvexity.LogMGFBasic
public import Critical2DKPZ.GaussianConvexity.ScalarDomainBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Convexity of the normalized log-MGF yields variance, negative-moment and covariance bounds, with convexity for the sum of the observables in the covariance bound. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open Critical2DKPZ.GaussianConvexity

namespace Critical2DKPZ.PolymerCalculus

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F G : Ω → ℝ}

/-- Convexity of the normalized log-MGF gives `Var(F) ≤ 2(log E exp(F) - E[F])` without centering. -/
theorem variance_le_log_moment_sub_mean_of_convex
    (hconv : ConvexOn ℝ (integrableExpSet F μ) (logMGFRatio μ F))
    (h0 : 0 ∈ interior (integrableExpSet F μ)) (h1 : 1 ∈ integrableExpSet F μ) :
    Var[F; μ] ≤ 2 * (Real.log (mgf F μ 1) - ∫ x, F x ∂μ) := by
  have h := supporting_line_at_zero_on hconv (interior_subset h0)
    (hasDerivAt_logMGFRatio_zero μ F h0) h1
  have he : logMGFRatio μ F 1 = Real.log (mgf F μ 1) := by
    simpa only [one_mul] using mul_logMGFRatio μ F 1
  have he0 : logMGFRatio μ F 0 = ∫ x, F x ∂μ := by simp [logMGFRatio]
  rw [he0, he, mul_one] at h
  linarith only [h]

/-- Nonnegativity of the Gaussianity defect for a normalized log-mass. -/
theorem gaussianityDefect_nonneg_of_convex
    (hconv : ConvexOn ℝ (integrableExpSet F μ) (logMGFRatio μ F))
    (h0 : 0 ∈ interior (integrableExpSet F μ)) (h1 : 1 ∈ integrableExpSet F μ)
    (hnorm : mgf F μ 1 = 1) : 0 ≤ gaussianityDefect μ F := by
  have h := variance_le_log_moment_sub_mean_of_convex hconv h0 h1
  rw [hnorm, Real.log_one] at h
  unfold gaussianityDefect
  linarith only [h]

/-- The sharp variance bound for a normalized log-mass. -/
theorem variance_le_neg_two_mean_of_convex
    (hconv : ConvexOn ℝ (integrableExpSet F μ) (logMGFRatio μ F))
    (h0 : 0 ∈ interior (integrableExpSet F μ)) (h1 : 1 ∈ integrableExpSet F μ)
    (hnorm : mgf F μ 1 = 1) : Var[F; μ] ≤ -2 * ∫ x, F x ∂μ := by
  have h := gaussianityDefect_nonneg_of_convex hconv h0 h1 hnorm
  unfold gaussianityDefect at h
  linarith only [h]

/-- The midpoint inequality at orders zero, one and two controls the mean. -/
theorem neg_two_mean_le_log_second_moment_of_convex
    (hconv : ConvexOn ℝ (integrableExpSet F μ) (logMGFRatio μ F))
    (h2 : 2 ∈ integrableExpSet F μ) (hnorm : mgf F μ 1 = 1) :
    -2 * (∫ x, F x ∂μ) ≤ Real.log (mgf F μ 2) := by
  have he1 : logMGFRatio μ F 1 = 0 := by
    have h := mul_logMGFRatio μ F 1
    simpa only [one_mul, hnorm, Real.log_one] using h
  have he2 : logMGFRatio μ F 2 = Real.log (mgf F μ 2) / 2 := by
    simp only [logMGFRatio, OfNat.ofNat_ne_zero, ite_false]
    rw [div_eq_inv_mul]
    rfl
  have h := neg_zero_le_two_on_of_one_eq_zero hconv (by simp [integrableExpSet] : (0 : ℝ) ∈ integrableExpSet F μ) h2 he1
  have he0 : logMGFRatio μ F 0 = ∫ x, F x ∂μ := by simp [logMGFRatio]
  rw [he0, he2] at h
  linarith only [h]

/-- Negative orders reverse the supporting-line inequality and yield the quadratic bound. -/
theorem log_negative_moment_le_of_convex
    (hconv : ConvexOn ℝ (integrableExpSet F μ) (logMGFRatio μ F))
    (h0 : 0 ∈ interior (integrableExpSet F μ)) {p : ℝ} (hp : 0 ≤ p)
    (hm : -p ∈ integrableExpSet F μ) :
    Real.log (mgf F μ (-p)) ≤
      -p * (∫ x, F x ∂μ) + p ^ 2 / 2 * Var[F; μ] := by
  have h := supporting_line_at_zero_on hconv (interior_subset h0)
    (hasDerivAt_logMGFRatio_zero μ F h0) hm
  have hm := mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hp)
  rw [mul_logMGFRatio] at hm
  simp only [logMGFRatio, ite_true] at hm
  calc
    _ ≤ -p * ((∫ x, F x ∂μ) + Var[F; μ] / 2 * -p) := hm
    _ = _ := by ring

/-- For a unit-mean exponential, the Gaussianity defect is at most `log (E exp(2F) / E exp(-F))`. -/
theorem gaussianityDefect_le_log_ratio_of_convex
    (hconv : ConvexOn ℝ (integrableExpSet F μ) (logMGFRatio μ F))
    (h0 : 0 ∈ interior (integrableExpSet F μ)) (h2 : 2 ∈ integrableExpSet F μ)
    (hm : -1 ∈ integrableExpSet F μ) (hnorm : mgf F μ 1 = 1) :
    gaussianityDefect μ F ≤ Real.log (mgf F μ 2 / mgf F μ (-1)) := by
  have hn := log_negative_moment_le_of_convex hconv h0 (p := 1) (by norm_num) hm
  have hp := neg_two_mean_le_log_second_moment_of_convex hconv h2 hnorm
  rw [Real.log_div (ne_of_gt (mgf_pos h2)) (ne_of_gt (mgf_pos hm))]
  unfold gaussianityDefect
  norm_num only [neg_mul, one_mul, one_pow] at hn
  linarith only [hn, hp]

/-- Convexity of the normalized log-MGF of `F + G` bounds their covariance by `log E exp(F+G) + Δ(F) + Δ(G)`. -/
theorem covariance_le_log_joint_moment_add_defects_of_convex
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hconv : ConvexOn ℝ (integrableExpSet (F + G) μ) (logMGFRatio μ (F + G)))
    (h0 : 0 ∈ interior (integrableExpSet (F + G) μ))
    (h1 : 1 ∈ integrableExpSet (F + G) μ) :
    cov[F, G; μ] ≤ Real.log (mgf (F + G) μ 1) +
      gaussianityDefect μ F + gaussianityDefect μ G := by
  have h := variance_le_log_moment_sub_mean_of_convex hconv h0 h1
  rw [variance_add hF hG, integral_add' (hF.integrable (by norm_num))
    (hG.integrable (by norm_num))] at h
  unfold gaussianityDefect
  linarith only [h]

end Critical2DKPZ.PolymerCalculus
