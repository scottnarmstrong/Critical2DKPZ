/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitPotentialTimeTail
import Mathlib.Algebra.BigOperators.Field

/-! # Splitting the free-spectator potential time sum -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- The explicit numerical envelope for a free spectator's potential action. -/
def wordGapTimeEnvelope (m : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) +
    2 / Real.sqrt ((m : ℝ) + 1)

theorem wordGapTimeEnvelope_nonneg (m : ℕ) : 0 ≤ wordGapTimeEnvelope m := by
  unfold wordGapTimeEnvelope
  apply add_nonneg
  · exact div_nonneg (Finset.sum_nonneg (fun k _ =>
      div_nonneg (by norm_num) (Real.sqrt_nonneg _))) (by positivity)
  · exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- The gap-potential convolution time sum is bounded by the stated initial reciprocal-square-root sum and its inverse-square-root tail. -/
theorem sum_gapPotential_convolution_time_le (m n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n,
      1 / (((m : ℝ) + 2 * k + 1) * Real.sqrt ((k : ℝ) + 1))) ≤
      (∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) +
        2 / Real.sqrt ((m : ℝ) + 1) := by
  have hsmall (L : ℕ) (hL : L ≤ m) :
      (∑ k ∈ Finset.Icc 1 L,
        1 / (((m : ℝ) + 2 * k + 1) * Real.sqrt ((k : ℝ) + 1))) ≤
        (∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 L,
          (1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hs : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have hd : ((m : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) ≤
            ((m : ℝ) + 2 * k + 1) * Real.sqrt ((k : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_right _ hs.le
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          linarith only [hk0]
        have hh := one_div_le_one_div_of_le (mul_pos (by positivity) hs) hd
        simpa only [div_div, mul_comm] using hh
      _ = (∑ k ∈ Finset.Icc 1 L, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) :=
        (Finset.sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc (by omega) hL) (fun k _ _ => by positivity)) (by positivity)
  by_cases hnm : n ≤ m
  · exact (hsmall n hnm).trans (le_add_of_nonneg_right (by positivity))
  · have hmn : m ≤ n := by omega
    have hsplit := Finset.sum_Ico_consecutive
      (fun k : ℕ => 1 / (((m : ℝ) + 2 * k + 1) * Real.sqrt ((k : ℝ) + 1)))
      (m := 1) (n := m + 1) (k := n + 1) (by omega) (by omega)
    simp only [Finset.Ico_add_one_right_eq_Icc] at hsplit
    rw [← hsplit]
    apply add_le_add (hsmall m le_rfl)
    calc
      _ ≤ ∑ k ∈ Finset.Icc (m + 1) n,
          1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply one_div_le_one_div_of_le (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        linarith only [hm0, hk0]
      _ ≤ 2 / Real.sqrt (((m + 1 : ℕ) : ℝ)) :=
        sum_inv_mul_sqrt_succ_le (m + 1) n (by omega) (by omega)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]

/-- A square-root bound on the initial reciprocal-square-root sum gives an inverse-square-root bound on the time envelope. -/
theorem wordGapTimeEnvelope_le_of_initial_sum (m : ℕ)
    (hsmall : (∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) ≤
      2 * Real.sqrt ((m : ℝ) + 1)) :
    wordGapTimeEnvelope m ≤ 4 / Real.sqrt ((m : ℝ) + 1) := by
  have hpos : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  calc
    _ ≤ (2 * Real.sqrt ((m : ℝ) + 1)) / ((m : ℝ) + 1) +
        2 / Real.sqrt ((m : ℝ) + 1) :=
      add_le_add (div_le_div_of_nonneg_right hsmall (by positivity)) le_rfl
    _ = _ := by
      have hfrac : (2 * Real.sqrt ((m : ℝ) + 1)) / ((m : ℝ) + 1) =
          2 / Real.sqrt ((m : ℝ) + 1) := by
        apply (div_eq_div_iff (by positivity : (m : ℝ) + 1 ≠ 0) hpos.ne').mpr
        rw [mul_assoc, Real.mul_self_sqrt (show 0 ≤ (m : ℝ) + 1 by positivity)]
      rw [hfrac]
      ring

end Critical2DKPZ.SHF.Moments
