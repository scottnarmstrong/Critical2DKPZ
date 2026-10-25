/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ExponentialTilt
public import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.Tactic

/-! # Small-volume and endpoint counterexamples in CSZ19a

The examples concern the renewal-clock tail and logarithmic renewal bounds
in arXiv:1805.01465v4.
-/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata

/-- At `N = 1`, the renewal clock vanishes and the stated probability bound can be less than one. -/
theorem csz19a_zero_clock_tail_false (w : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ ¬ Renewal.cumulativePower w ⌊(1 : ℝ) * Real.log 1⌋₊ ⌊t⌋₊ ≤
      Real.exp (1 - c * Real.log (1 / t)) := by
  refine ⟨Real.exp (-2 / c), Real.exp_pos _, ?_⟩
  simp only [Real.log_one, mul_zero, Nat.floor_zero, Renewal.cumulativePower_zero,
    one_div, Real.log_inv, Real.log_exp]
  have he : 1 - c * -(-2 / c) = (-1 : ℝ) := by field_simp; ring
  rw [he]
  exact not_le.mpr (Real.exp_lt_one_iff.mpr (by norm_num))

/-- At `r = 1`, the renewal probability is positive while its proposed logarithmic upper bound is zero. -/
theorem csz19a_log_one_overlap_bound_false (C : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ¬ replicaOverlap 1 / replicaOverlap N ≤ C * Real.log 1 / Real.log N := by
  simp only [Real.log_one, mul_zero, zero_div]
  exact not_le.mpr (div_pos (replicaOverlap_pos (by omega)) (replicaOverlap_pos hN))

end Critical2DKPZ.Errata
