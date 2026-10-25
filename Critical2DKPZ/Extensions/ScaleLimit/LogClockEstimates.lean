/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LogIntegrability

/-!
# Uniform expansion of the double logarithm

The expansion is restricted to the compact difference support and small widths.
The singularity at zero is handled by almost-everywhere integral estimates.
-/

public section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A tangent-line bound for the logarithm, in difference form. -/
theorem log_sub_log_le_sub_div {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.log u - Real.log v ≤ (u - v) / v := by
  calc
    _ = Real.log (u / v) := (Real.log_div hu.ne' hv.ne').symm
    _ ≤ u / v - 1 := Real.log_le_sub_one_of_pos (div_pos hu hv)
    _ = (u - v) / v := by field_simp

/-- Logarithms have a uniform relative Lipschitz bound away from zero. -/
theorem abs_log_add_sub_log_le {A x : ℝ} (hA : 0 < A) (hx : A / 2 ≤ A + x) :
    |Real.log (A + x) - Real.log A| ≤ 2 * |x| / A := by
  have hhalf : 0 < A / 2 := half_pos hA
  have hden : 0 < A + x := hhalf.trans_le hx
  have hup := log_sub_log_le_sub_div hden hA
  have hlo := log_sub_log_le_sub_div hA hden
  have hu : Real.log (A + x) - Real.log A ≤ 2 * |x| / A := by
    calc
      _ ≤ x / A := by simpa only [add_sub_cancel_left] using hup
      _ ≤ |x| / A := div_le_div_of_nonneg_right (le_abs_self x) hA.le
      _ ≤ 2 * |x| / A := div_le_div_of_nonneg_right (by linarith [abs_nonneg x]) hA.le
  have hl : Real.log A - Real.log (A + x) ≤ 2 * |x| / A := by
    calc
      _ ≤ (-x) / (A + x) := by
        convert hlo using 1
        congr 1
        ring
      _ ≤ |x| / (A + x) := div_le_div_of_nonneg_right (neg_le_abs x) hden.le
      _ ≤ |x| / (A / 2) := div_le_div_of_nonneg_left (abs_nonneg x) hhalf hx
      _ = 2 * |x| / A := by field_simp
  exact abs_le.mpr ⟨by linarith only [hl], hu⟩

/-- The pointwise expansion is controlled by the integrable positive logarithm. -/
theorem loglog_pointwise_bound {a K : ℝ} (ha : 0 < a)
    (hsmall : 2 * max 0 (Real.log K) + 2 ≤ Real.log a⁻¹)
    {w : Plane} (hw : w ≠ 0) (hwK : ‖w‖ ≤ K) :
    |Real.log (Real.log (a * ‖w‖)⁻¹) - Real.log (Real.log a⁻¹)| ≤
      2 * (max 0 (Real.log K) + max 0 (Real.log ‖w‖⁻¹)) / Real.log a⁻¹ := by
  let A := Real.log a⁻¹
  let B := max 0 (Real.log K)
  let x := Real.log ‖w‖⁻¹
  have hB : 0 ≤ B := le_max_left _ _
  have hA : 0 < A := by dsimp [A]; linarith only [hsmall, hB]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hlow : -B ≤ x := by
    have hh := (Real.log_le_log hwpos hwK).trans (le_max_right 0 (Real.log K))
    dsimp [x, B]
    rw [Real.log_inv]
    exact neg_le_neg hh
  have hx : A / 2 ≤ A + x := by
    change 2 * B + 2 ≤ A at hsmall
    linarith only [hsmall, hlow]
  have hnorm : |x| ≤ B + max 0 x := by
    apply abs_le.mpr
    constructor
    · linarith only [hlow, le_max_left (0 : ℝ) x]
    · exact (le_max_right (0 : ℝ) x).trans (le_add_of_nonneg_left hB)
  have hexpand : Real.log (a * ‖w‖)⁻¹ = A + x := by
    dsimp [A, x]
    rw [Real.log_inv, Real.log_mul ha.ne' hwpos.ne', Real.log_inv, Real.log_inv, neg_add]
  rw [hexpand]
  exact (abs_log_add_sub_log_le hA hx).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num)) hA.le)

/-- The small-width double logarithm is integrable on the fixed support ball. -/
theorem integrableOn_loglog_of_small {a K : ℝ} (ha : 0 < a)
    (hsmall : 2 * max 0 (Real.log K) + 2 ≤ Real.log a⁻¹) :
    IntegrableOn (fun w : Plane => Real.log (Real.log (a * ‖w‖)⁻¹))
      (Metric.ball 0 K) volume := by
  let A := Real.log a⁻¹
  let B := max 0 (Real.log K)
  have hB : 0 ≤ B := le_max_left _ _
  have hA : 0 < A := by dsimp [A]; linarith only [hsmall, hB]
  have hc : IntegrableOn (fun _ : Plane => B) (Metric.ball 0 K) volume :=
    integrableOn_const (by finiteness)
  have hmajor : IntegrableOn (fun w : Plane =>
      (2 / A) * (B + max 0 (Real.log ‖w‖⁻¹))) (Metric.ball 0 K) volume :=
    (hc.add (integrableOn_posLog_inv_norm_ball K)).const_mul _
  have hmeas : AEStronglyMeasurable (fun w : Plane =>
      Real.log (Real.log (a * ‖w‖)⁻¹) - Real.log A)
      (volume.restrict (Metric.ball 0 K)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have herror : IntegrableOn (fun w : Plane =>
      Real.log (Real.log (a * ‖w‖)⁻¹) - Real.log A) (Metric.ball 0 K) volume := by
    apply hmajor.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : Plane))] with w hw hw0
    have hn : ‖w‖ ≤ K := (mem_ball_zero_iff.mp hw).le
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      using loglog_pointwise_bound ha hsmall hw0 hn
  have hconst : IntegrableOn (fun _ : Plane => Real.log A) (Metric.ball 0 K) volume :=
    integrableOn_const (by finiteness)
  exact (herror.add hconst).congr (Eventually.of_forall fun _ => sub_add_cancel _ _)

end Critical2DKPZ.Extensions.ScaleLimit
