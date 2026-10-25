/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # Elementary sums used in the geometric block estimates -/

@[expose] public section

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The sum of inverse squares after a positive index is bounded by its inverse. -/
theorem sum_Ioc_inv_sq_le {ℓ n : ℕ} (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    (∑ j ∈ Finset.Ioc ℓ n, 1 / (j : ℝ) ^ 2) ≤ 1 / (ℓ : ℝ) := by
  have hstrong : ∀ n, ℓ ≤ n → (∑ j ∈ Finset.Ioc ℓ n, 1 / (j : ℝ) ^ 2) ≤
      1 / (ℓ : ℝ) - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ioc_succ_top hn]
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hℓ.trans hn))
      have hnp : 0 < (n : ℝ) + 1 := by positivity
      have hid : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      have hterm : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [hid]
        exact one_div_le_one_div_of_le (mul_pos hnpos hnp) (by nlinarith)
      push_cast
      linarith
  exact (hstrong n hℓn).trans (sub_le_self _ (by positivity))

/-- The positive-index harmonic sum is at most `1 + log n`, including `n=0`. -/
theorem sum_Icc_inv_le_one_add_log (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ)⁻¹) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h

end Critical2DKPZ.Extensions.ScaleLimit
