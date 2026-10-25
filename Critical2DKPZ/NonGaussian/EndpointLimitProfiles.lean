/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Bounded logarithmic profiles for endpoint perturbations -/

@[expose] public noncomputable section

open scoped BoundedContinuousFunction

namespace Critical2DKPZ.NonGaussian

/-- A bounded continuous profile bounded away from zero is the exponential
of a bounded continuous logarithmic profile. -/
theorem exists_bounded_log_profile {X : Type*} [TopologicalSpace X]
    (f : X →ᵇ ℝ) {c : ℝ} (hc : 0 < c) (hf : ∀ x, c ≤ f x) :
    ∃ h : X →ᵇ ℝ, ∀ x, Real.exp (h x) = f x := by
  let C : ℝ := ‖f‖ + c
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg f) hc
  have hupper (x : X) : f x ≤ C := by
    exact (le_abs_self _).trans ((f.norm_coe_le_norm x).trans (by dsimp [C]; linarith))
  have hcont : Continuous (fun x => Real.log (f x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Real.continuousAt_log (ne_of_gt (hc.trans_le (hf x)))).comp
      f.continuous.continuousAt
  let B : ℝ := max |Real.log c| |Real.log C|
  have hbound (x : X) : |Real.log (f x)| ≤ B := by
    apply abs_le.mpr
    constructor
    · calc
        -B ≤ -|Real.log c| := neg_le_neg (le_max_left _ _)
        _ ≤ Real.log c := neg_abs_le _
        _ ≤ Real.log (f x) := Real.log_le_log hc (hf x)
    · calc
        Real.log (f x) ≤ Real.log C := Real.log_le_log (hc.trans_le (hf x)) (hupper x)
        _ ≤ B := (le_abs_self _).trans (le_max_right _ _)
  let h : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.log (f x), hcont⟩ (2 * B) (by
      intro x y
      rw [Real.dist_eq]
      change |Real.log (f x) - Real.log (f y)| ≤ 2 * B
      exact (abs_sub _ _).trans (by linarith only [hbound x, hbound y]))
  refine ⟨h, fun x => ?_⟩
  exact Real.exp_log (hc.trans_le (hf x))

end Critical2DKPZ.NonGaussian
