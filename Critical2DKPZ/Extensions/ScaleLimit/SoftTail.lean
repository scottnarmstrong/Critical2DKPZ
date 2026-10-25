/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.NormField
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # A Lipschitz truncation for the maximal tail estimate

The positive part of `2|x|-t` vanishes below `t/2` and majorizes the part of
`|x|` above a bounded offset. Unlike a sharp indicator truncation, it preserves
continuity in probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The continuous tail above half of the threshold. -/
def softTail (t x : ℝ) : ℝ := max 0 (2 * ‖x‖ - t)

/-- The tail is nonnegative. -/
theorem softTail_nonneg (t x : ℝ) : 0 ≤ softTail t x := le_max_left _ _

/-- The tail and a bounded offset majorize the original norm. -/
theorem norm_le_add_softTail (t x : ℝ) : ‖x‖ ≤ t + softTail t x := by
  have h := le_max_right 0 (2 * ‖x‖ - t)
  have hn := norm_nonneg x
  change ‖x‖ ≤ t + max 0 (2 * ‖x‖ - t)
  linarith only [h, hn]

/-- For nonnegative thresholds the tail is bounded by twice the original norm. -/
theorem softTail_le_two_norm {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : softTail t x ≤ 2 * ‖x‖ := by
  apply max_le
  · positivity
  · exact sub_le_self _ ht


/-- The truncation is two-Lipschitz, uniformly in the threshold. -/
theorem softTail_lipschitz (t : ℝ) : LipschitzWith 2 (softTail t) := by
  have hlin : LipschitzWith 2 (fun x : ℝ => 2 * ‖x‖ - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(2 * ‖x‖ - t) - (2 * ‖y‖ - t)| ≤ 2 * |x - y|
    rw [show (2 * ‖x‖ - t) - (2 * ‖y‖ - t) = 2 * (‖x‖ - ‖y‖) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by norm_num)
  exact hlin.const_max 0

/-- The continuous tail is bounded by the square-tail moment. -/
theorem softTail_le_sq_tail {t : ℝ} (ht : 0 < t) (x : ℝ) :
    softTail t x ≤ (4 / t) * (x ^ 2 * {u : ℝ | t / 2 < |u|}.indicator 1 x) := by
  classical
  by_cases hx : t / 2 < |x|
  · rw [indicator_of_mem (show x ∈ {u : ℝ | t / 2 < |u|} from hx), Pi.one_apply, mul_one]
    apply (softTail_le_two_norm ht.le x).trans
    rw [Real.norm_eq_abs, div_mul_eq_mul_div]
    apply (le_div_iff₀ ht).mpr
    have hm := mul_le_mul_of_nonneg_left hx.le (abs_nonneg x)
    nlinarith only [hm, sq_abs x]
  · have hz : softTail t x = 0 := by
      apply max_eq_left
      rw [Real.norm_eq_abs]
      linarith only [le_of_not_gt hx]
    rw [hz, indicator_of_notMem (show x ∉ {u : ℝ | t / 2 < |u|} from hx), mul_zero, mul_zero]

end Critical2DKPZ.Extensions.ScaleLimit

end
