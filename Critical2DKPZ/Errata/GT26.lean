/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.DeltaBose.TwoParticle

/-! # Signed sums and heat resets

These scalar examples concern the signed heat-reset expansion in GT26. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Errata

/-- At `s = 1` and `r = 1/2`, the signed sum is positive while the proposed absolute-value majorant is negative. -/
theorem gt26_wrong_majorant_counterexample :
    (1 / (1 : ℝ) - 1 / (1 - 1 / 2) < 0) ∧
      0 < 1 / (1 - (1 / 2 : ℝ)) + 1 / 1 - 2 / (1 - (1 / 2 : ℝ) / 4) := by
  norm_num

/-- The four-term signed sum has the stated rational expression when its denominators are nonzero. -/
theorem gt26_corrected_signed_sum {s r : ℝ} (hs : 0 < s) (hrs : r < s) :
    1 / (s - r) + 1 / s - 2 / (s - r / 4) =
      r * (2 * s + r) / (s * (s - r) * (4 * s - r)) := by
  have h₁ : s - r ≠ 0 := (sub_pos.mpr hrs).ne'
  have h₂ : s - r / 4 ≠ 0 := by linarith
  have h₃ : 4 * s - r ≠ 0 := by linarith
  have h₄ : s * 4 - r ≠ 0 := by linarith
  field_simp [hs.ne', h₁, h₂, h₃, h₄]
  ring

/-- Heat propagation from time `1/16` over duration `3/16` differs from the previous-time reset at the origin. -/
theorem gt26_previous_time_reset_counterexample :
    (∫ y : Plane, heatKernel (1 / 16) y * heatKernel (3 / 16) ((0 : Plane) - y)) -
      heatKernel (1 / 16) (0 : Plane) ≠ 0 := by
  rw [integral_heatKernel_mul_sub (by norm_num : (0 : ℝ) < 1 / 16)
    (by norm_num : (0 : ℝ) < 3 / 16)]
  apply sub_ne_zero.mpr
  apply ne_of_lt
  simp only [heatKernel, norm_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one]
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (by nlinarith [Real.pi_pos])

end Critical2DKPZ.Errata

end
