/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Bounded logarithms of positive terminal approximations -/

@[expose] public noncomputable section

open scoped BoundedContinuousFunction

namespace Critical2DKPZ.NonGaussian

/-- Adding a positive constant to a nonnegative bounded continuous terminal
makes its logarithm a bounded continuous initial profile. -/
def logPositiveTerminal (g : Plane →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y) (ε : ℝ) (hε : 0 < ε) : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.log (g y + ε), (g.continuous.add continuous_const).log
      (fun y => ne_of_gt (add_pos_of_nonneg_of_pos (hg y) hε))⟩
    (2 * (|Real.log ε| + |Real.log (‖g‖ + ε)|)) (by
      have hBound (y : Plane) : |Real.log (g y + ε)| ≤ |Real.log ε| + |Real.log (‖g‖ + ε)| := by
        have hy : g y ≤ ‖g‖ := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm y)
        have hLo : Real.log ε ≤ Real.log (g y + ε) := Real.log_le_log hε (by linarith only [hg y])
        have hHi : Real.log (g y + ε) ≤ Real.log (‖g‖ + ε) :=
          Real.log_le_log (add_pos_of_nonneg_of_pos (hg y) hε) (add_le_add hy le_rfl)
        rw [abs_le]
        constructor
        · have h := neg_abs_le (Real.log ε)
          have h0 := abs_nonneg (Real.log (‖g‖ + ε))
          linarith only [hLo, h, h0]
        · have h := le_abs_self (Real.log (‖g‖ + ε))
          have h0 := abs_nonneg (Real.log ε)
          linarith only [hHi, h, h0]
      intro y z
      rw [Real.dist_eq]
      calc
        |Real.log (g y + ε) - Real.log (g z + ε)| ≤
            |Real.log (g y + ε)| + |Real.log (g z + ε)| := abs_sub _ _
        _ ≤ _ := by linarith only [hBound y, hBound z])

/-- The positive approximation is represented exactly as a bounded exponential terminal. -/
theorem exp_logPositiveTerminal (g : Plane →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y) (ε : ℝ) (hε : 0 < ε) (y : Plane) :
    Real.exp (logPositiveTerminal g hg ε hε y) = g y + ε := by
  change Real.exp (Real.log (g y + ε)) = g y + ε
  exact Real.exp_log (add_pos_of_nonneg_of_pos (hg y) hε)

end Critical2DKPZ.NonGaussian

end
