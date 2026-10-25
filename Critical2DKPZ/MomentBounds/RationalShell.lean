/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.RadialSums
import Mathlib.Tactic

/-!
# A telescoping majorant for the rational shell sum

The first lattice estimate of LZ21 Lemma A.1 can be proved by a discrete
reciprocal telescope. No planar integral or unproved radial comparison is needed.
-/

public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The rational shell factor satisfies the one-step telescoping estimate. -/
theorem rational_shell_step {L x : ℝ} (hL : 0 < L) (hx : 0 ≤ x) :
    (x + 1) / (L + (x + 1) ^ 2) ^ 2 ≤
      (L + x ^ 2)⁻¹ - (L + (x + 1) ^ 2)⁻¹ := by
  have hA : 0 < L + x ^ 2 := add_pos_of_pos_of_nonneg hL (sq_nonneg _)
  have hB : 0 < L + (x + 1) ^ 2 := add_pos_of_pos_of_nonneg hL (sq_nonneg _)
  have halg : (x + 1) * (L + x ^ 2) ≤
      ((L + (x + 1) ^ 2) - (L + x ^ 2)) * (L + (x + 1) ^ 2) := by
    rw [← sub_nonneg]
    have he : ((L + (x + 1) ^ 2) - (L + x ^ 2)) * (L + (x + 1) ^ 2) -
        (x + 1) * (L + x ^ 2) = x * L + x ^ 3 + 4 * x ^ 2 + 4 * x + 1 := by ring
    rw [he]
    positivity
  calc
    _ = ((x + 1) * (L + x ^ 2)) /
        ((L + x ^ 2) * (L + (x + 1) ^ 2) ^ 2) := by field_simp
    _ ≤ (((L + (x + 1) ^ 2) - (L + x ^ 2)) * (L + (x + 1) ^ 2)) /
        ((L + x ^ 2) * (L + (x + 1) ^ 2) ^ 2) :=
      div_le_div_of_nonneg_right halg (by positivity)
    _ = _ := by field_simp

/-- The rational shell sum is bounded by its telescoping majorant. -/
theorem sum_rational_shell_le (L : ℝ) (hL : 0 < L) (k : ℕ) :
    (∑ j ∈ Finset.range k, ((j : ℝ) + 1) / (L + ((j : ℝ) + 1) ^ 2) ^ 2) ≤
      L⁻¹ - (L + (k : ℝ) ^ 2)⁻¹ := by
  induction k with
  | zero => simp only [Finset.sum_range_zero, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, sub_self, le_refl]
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_add_one]
      have h := add_le_add ih (rational_shell_step hL (Nat.cast_nonneg k))
      convert h using 1
      ring


end Critical2DKPZ.MomentBounds
