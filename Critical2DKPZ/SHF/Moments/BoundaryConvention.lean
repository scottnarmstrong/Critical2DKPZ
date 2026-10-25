/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.Replica
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-! # Changing endpoints in time sums

Switching between the time sets `1, …, n` and `0, …, n - 1` changes only the endpoint terms. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments




/-- Changing a time sum from the initial to the terminal endpoint adds the terminal value and removes the initial value. -/
theorem sum_Icc_eq_sum_range_boundary (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, f j) = (∑ j ∈ Finset.range n, f j) + f n - f 0 := by
  induction n with
  | zero => simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      Finset.sum_empty, Finset.range_zero, zero_add, sub_self]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_range_succ, ih]
      ring



end Critical2DKPZ.SHF.Moments
