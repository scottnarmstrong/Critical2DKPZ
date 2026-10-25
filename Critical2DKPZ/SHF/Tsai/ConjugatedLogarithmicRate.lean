/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Logarithmic rate comparisons for conjugated collision diagrams -/

@[expose] public section

namespace Critical2DKPZ.SHF.Tsai

/-- A sufficiently large common shift gives both a unit collision resolvent
denominator and the logarithmic gain in the prescribed diagram estimate. -/
theorem conjugated_collision_log_rate_bounds {θ g c rate lam : ℝ}
    (hc : g + Real.exp (2 * max θ 0 + 1) ≤ c) (hrate : c + 3 ≤ rate) (hlam : rate ≤ lam) :
    0 < Real.log (rate - c - 1) ∧
      1 ≤ Real.log (lam - g) - θ ∧
      Real.log (rate - c - 1) / 2 ≤ Real.log (lam - g) - θ := by
  have hE : 0 < Real.exp (2 * max θ 0 + 1) := Real.exp_pos _
  have hArg : 2 ≤ rate - c - 1 := by linarith only [hrate]
  have hArgPos : 0 < rate - c - 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hArg
  have hL : 0 < Real.log (rate - c - 1) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hArg)
  have hLower : Real.exp (2 * max θ 0 + 1) ≤ lam - g := by linarith only [hc, hrate, hlam]
  have hlog : 2 * max θ 0 + 1 ≤ Real.log (lam - g) := by
    calc
      _ = Real.log (Real.exp (2 * max θ 0 + 1)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log hE hLower
  have hCompArg : rate - c - 1 ≤ lam - g := by linarith only [hc, hlam, hE]
  have hCompLog : Real.log (rate - c - 1) ≤ Real.log (lam - g) :=
    Real.log_le_log hArgPos hCompArg
  have hθ : θ ≤ max θ 0 := le_max_left _ _
  have hzero : 0 ≤ max θ 0 := le_max_right _ _
  refine ⟨hL, ?_, ?_⟩
  · linarith only [hlog, hθ, hzero]
  · linarith only [hlog, hCompLog, hθ]

end Critical2DKPZ.SHF.Tsai

end
