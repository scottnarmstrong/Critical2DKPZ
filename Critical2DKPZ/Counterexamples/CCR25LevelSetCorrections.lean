/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.SiteToPlane
import Critical2DKPZ.RandomWalk.GaussianBridge
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Gaussian lattice level sets

The layer-cake argument in CCR25 Lemma 4.18 uses Euclidean balls with radius equal to the square root of the Gaussian exponent threshold. -/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata.CCR25

/-- Gaussian superlevel sets have the stated square-root radius in every real normed space.
This is the exact level-set equivalence needed by CCR25's layer-cake step. -/
theorem ccr25_09_corrected_level_set {E : Type*} [NormedAddCommGroup E]
    (x z : E) {s c n : ℝ} (hs : 0 < s) (hs1 : s < 1) (hc : 0 < c) (hn : 0 < n) :
    s ≤ Real.exp (-‖z - x‖ ^ 2 / (16 * c * n)) ↔
      ‖z - x‖ ≤ Real.sqrt (16 * c * n * Real.log (1 / s)) := by
  have hD : 0 < 16 * c * n := by positivity
  have hl : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by
    rw [le_div_iff₀ hs]
    simpa only [one_mul] using hs1.le)
  rw [Real.le_sqrt (norm_nonneg _) (mul_nonneg hD.le hl)]
  rw [← Real.log_le_iff_le_exp hs, Real.log_div one_ne_zero hs.ne', Real.log_one, zero_sub]
  constructor
  · intro h
    have hh := (le_div_iff₀ hD).mp h
    linarith only [hh]
  · intro h
    apply (le_div_iff₀ hD).mpr
    linarith only [h]

/-- At `m = n = c = 1`, a lattice point in the ball of radius two can lie outside the Gaussian superlevel set at `s = exp(-1/8)`. -/
theorem ccr25_09_printed_lattice_level_set_false :
    let z : Site := ![2, 0]
    let s : ℝ := Real.exp (-(1 / 8 : ℝ))
    0 < s ∧ s < 1 ∧
      ‖siteToPlane z - siteToPlane (0 : Site)‖ ≤ 16 * (1 : ℝ) * 1 * Real.log (1 / s) ∧
      ¬ s ≤ Real.exp (-‖siteToPlane z - siteToPlane (0 : Site)‖ ^ 2 /
        (16 * (1 : ℝ) * 1)) := by
  dsimp only
  have hsq : ‖siteToPlane ![2, 0] - siteToPlane (0 : Site)‖ ^ 2 = (4 : ℝ) := by
    have hz : siteToPlane (0 : Site) = 0 := by ext i; simp [siteToPlane]
    rw [hz, sub_zero, norm_siteToPlane_sq]
    norm_num
  have hnorm : ‖siteToPlane ![2, 0] - siteToPlane (0 : Site)‖ = (2 : ℝ) := by
    nlinarith only [hsq, norm_nonneg (siteToPlane ![2, 0] - siteToPlane (0 : Site))]
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by norm_num), ?_, ?_⟩
  · rw [hnorm, Real.log_div one_ne_zero (Real.exp_ne_zero _), Real.log_one, Real.log_exp]
    norm_num
  · rw [hsq, Real.exp_le_exp]
    norm_num

end Critical2DKPZ.Errata.CCR25
