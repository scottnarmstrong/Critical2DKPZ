/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A domain obstruction for the covariance clock

The normalized clock alone does not force positive widths to approach zero:
the real logarithm takes the same value at opposite arguments. This example
shows why the shrinking-width hypothesis is needed when applying the
covariance asymptotic.
-/

public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Growing widths have exactly the same totalized clock as shrinking widths. -/
theorem normalized_loglog_inv_exp_exp (L s : ℝ) (hL : L ≠ 0) :
    L⁻¹ * Real.log (Real.log (Real.exp (Real.exp (L * s)))⁻¹) = s := by
  rw [Real.log_inv, Real.log_exp, Real.log_neg_eq_log, Real.log_exp,
    ← mul_assoc, inv_mul_cancel₀ hL, one_mul]

/-- The width in the counterexample is always larger than one. -/
theorem one_lt_exp_exp_clock (L s : ℝ) :
    1 < Real.exp (Real.exp (L * s)) :=
  Real.one_lt_exp_iff.mpr (Real.exp_pos (L * s))

/-- The normalized-clock limit holds along the positive-real index. -/
theorem tendsto_normalized_loglog_growing_width (s : ℝ) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (Real.exp (Real.exp ((L : ℝ) * s)))⁻¹))
      atTop (𝓝 s) := by
  have hclock : (fun L : Set.Ioi (0 : ℝ) =>
      (L : ℝ)⁻¹ * Real.log (Real.log (Real.exp (Real.exp ((L : ℝ) * s)))⁻¹)) =
      fun _ => s := by
    funext L
    exact normalized_loglog_inv_exp_exp L s (ne_of_gt L.property)
  rw [hclock]
  exact tendsto_const_nhds

/-- Despite its prescribed clock, this positive width does not approach zero. -/
theorem not_tendsto_growing_width_zero (s : ℝ) :
    ¬ Tendsto (fun L : Set.Ioi (0 : ℝ) => Real.exp (Real.exp ((L : ℝ) * s)))
      atTop (𝓝 0) := by
  intro h
  have hbound : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto h (Eventually.of_forall fun L => (one_lt_exp_exp_clock L s).le)
  exact (not_le_of_gt zero_lt_one) hbound

end Critical2DKPZ.Extensions.ScaleLimit
