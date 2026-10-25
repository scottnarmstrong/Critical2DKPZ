/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Summable time tails for the gap-potential convolution -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- The inverse-three-halves time weight is bounded by a telescoping
reciprocal-square-root difference. -/
theorem inv_mul_sqrt_succ_le_difference (k : ℕ) (hk : 1 ≤ k) :
    1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) ≤
      2 * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) := by
  let a := Real.sqrt (k : ℝ)
  let b := Real.sqrt ((k : ℝ) + 1)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 0 < a := Real.sqrt_pos.mpr hk0
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a ^ 2 = k := Real.sq_sqrt hk0.le
  have hb2 : b ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hp : 0 < a + b := add_pos ha hb
  have hd : (b - a) * (a + b) = 1 := by nlinarith only [ha2, hb2]
  have hid : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    field_simp [ha.ne', hb.ne', hp.ne']
    nlinarith only [hd]
  have hbound : a * (a + b) ≤ 2 * b ^ 2 := by
    have hsq := pow_le_pow_left₀ ha.le hab 2
    have hmul := mul_le_mul_of_nonneg_right hab hb.le
    nlinarith only [hsq, hmul]
  change 1 / (((k : ℝ) + 1) * b) ≤ 2 * (1 / a - 1 / b)
  rw [← hb2, hid, mul_one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < b ^ 2 * b)
    (by positivity : 0 < a * b * (a + b))).mpr
  have hh := mul_le_mul_of_nonneg_right hbound hb.le
  nlinarith only [hh]

/-- The potential's long-time numerical tail decays at the inverse square
root of its lower endpoint. -/
theorem sum_inv_mul_sqrt_succ_le (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∑ k ∈ Finset.Icc m n, 1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))) ≤
      2 / Real.sqrt (m : ℝ) := by
  have htel : (∑ k ∈ Finset.Icc m n,
      (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1))) =
      1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((n : ℝ) + 1) := by
    simpa only [neg_sub_neg, Nat.cast_add, Nat.cast_one] using
      Finset.sum_Icc_sub hmn (fun k : ℕ => -(1 / Real.sqrt (k : ℝ)))
  calc
    _ ≤ ∑ k ∈ Finset.Icc m n,
        2 * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) :=
      Finset.sum_le_sum (fun k hk => inv_mul_sqrt_succ_le_difference k
        (hm.trans (Finset.mem_Icc.mp hk).1))
    _ = 2 * (1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((n : ℝ) + 1)) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ 2 / Real.sqrt (m : ℝ) := by
      have hh : 0 ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by positivity
      calc
        _ ≤ 2 * (1 / Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ hh) (by norm_num)
        _ = _ := mul_one_div _ _

end Critical2DKPZ.SHF.Moments
