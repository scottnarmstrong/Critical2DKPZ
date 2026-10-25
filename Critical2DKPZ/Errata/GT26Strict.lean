/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.GT26
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A signed heat-reset sum

The four terms in the GT26 heat-reset expansion have signs `+,+,-,-` and reset times `r,0,r/4,r/4`, and their sum can exceed the proposed majorant for positive `r < s`. -/

@[expose] public section

namespace Critical2DKPZ.Errata

/-- The proposed absolute-value bound fails for every pair of successive positive integration times. -/
theorem gt26_signed_majorant_strict_counterexample {s r : ℝ}
    (_hs : 0 < s) (hr : 0 < r) (hrs : r < s) :
    ¬ |1 / (s - r) + 1 / s - 1 / (s - r / 4) - 1 / (s - r / 4)| ≤
      1 / s + (1 - 2) / (s - r) := by
  have hi : 1 / s < 1 / (s - r) :=
    one_div_lt_one_div_of_lt (sub_pos.mpr hrs) (sub_lt_self s hr)
  have hn : 1 / s + (1 - 2) / (s - r) < 0 := by
    calc
      _ = 1 / s - 1 / (s - r) := by ring
      _ < 0 := sub_neg.mpr hi
  exact not_le_of_gt (lt_of_lt_of_le hn (abs_nonneg _))

/-- The absolute value of the four-term sum is bounded by the stated positive difference. -/
theorem gt26_signed_majorant_strict_corrected {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s) :
    0 ≤ 1 / (s - r) + 1 / s - 1 / (s - r / 4) - 1 / (s - r / 4) ∧
      |1 / (s - r) + 1 / s - 1 / (s - r / 4) - 1 / (s - r / 4)| ≤
        1 / (s - r) - 1 / s := by
  have he : 1 / (s - r) + 1 / s - 1 / (s - r / 4) - 1 / (s - r / 4) =
      r * (2 * s + r) / (s * (s - r) * (4 * s - r)) := by
    calc
      _ = 1 / (s - r) + 1 / s - 2 / (s - r / 4) := by ring
      _ = _ := gt26_corrected_signed_sum hs hrs
  have hnonneg : 0 ≤ 1 / (s - r) + 1 / s - 1 / (s - r / 4) - 1 / (s - r / 4) := by
    rw [he]
    exact le_of_lt (div_pos (mul_pos hr (by linarith))
      (mul_pos (mul_pos hs (sub_pos.mpr hrs)) (by linarith)))
  have hden : 0 < s - r / 4 := by linarith
  have hi : 1 / s ≤ 1 / (s - r / 4) :=
    one_div_le_one_div_of_le hden (by linarith)
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  linarith only [hi]

/-- The previous-time heat reset has negative mean at the origin for every pair of successive positive times. -/
theorem gt26_previous_reset_strict_counterexample {s t : ℝ}
    (hs : 0 < s) (hst : s < t) :
    (∫ y : Plane, heatKernel s y * heatKernel (t - s) ((0 : Plane) - y)) -
      heatKernel s (0 : Plane) < 0 := by
  rw [integral_heatKernel_mul_sub hs (sub_pos.mpr hst),
    show s + (t - s) = t by ring]
  have ht : 0 < t := lt_trans hs hst
  apply sub_neg.mpr
  simp only [heatKernel, norm_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2
    (mul_lt_mul_of_pos_left hst (by positivity))

/-- The current-time heat reset has zero mean at every spatial point for successive positive times. -/
theorem gt26_current_reset_strict_corrected {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (x : Plane) :
    (∫ y : Plane, heatKernel s y * heatKernel (t - s) (x - y)) - heatKernel t x = 0 := by
  rw [integral_heatKernel_mul_sub hs (sub_pos.mpr hst),
    show s + (t - s) = t by ring, sub_self]

end Critical2DKPZ.Errata
