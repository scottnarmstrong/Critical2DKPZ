/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Power sums on partitions with small mesh

For an exponent greater than one, the sum of the powers of the partition increments is
bounded by the total interval length times the maximum increment to the exponent minus one.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology BigOperators

namespace Critical2DKPZ.SHF.Tsai

/-- A bound on every increment controls the sum of its powers by the total length. -/
theorem sum_increment_rpow_le (k : ℕ) (r : ℕ → ℝ) {δ α : ℝ}
    (hα : 1 < α)
    (hinc : ∀ i < k, 0 ≤ r (i + 1) - r i)
    (hmesh : ∀ i < k, r (i + 1) - r i ≤ δ) :
    ∑ i ∈ Finset.range k, (r (i + 1) - r i) ^ α ≤
      δ ^ (α - 1) * (r k - r 0) := by
  have hα0 : 0 ≤ α - 1 := (sub_pos.mpr hα).le
  calc
    _ ≤ ∑ i ∈ Finset.range k, δ ^ (α - 1) * (r (i + 1) - r i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hx := hinc i (Finset.mem_range.mp hi)
      calc
        (r (i + 1) - r i) ^ α =
            (r (i + 1) - r i) * (r (i + 1) - r i) ^ (α - 1) := by
          conv_lhs => rw [show α = 1 + (α - 1) by ring]
          rw [Real.rpow_add_of_nonneg hx zero_le_one hα0, Real.rpow_one]
        _ ≤ (r (i + 1) - r i) * δ ^ (α - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx (hmesh i (Finset.mem_range.mp hi)) hα0) hx
        _ = _ := mul_comm _ _
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

/-- Local errors of order strictly greater than one vanish as the maximum mesh tends to zero. -/
theorem tendsto_sum_increment_rpow_zero (k : ℕ → ℕ) (r : ℕ → ℕ → ℝ)
    {δ : ℕ → ℝ} {α T : ℝ} (hδ : ∀ j, 0 ≤ δ j) (hα : 1 < α)
    (hinc : ∀ j i, i < k j → 0 ≤ r j (i + 1) - r j i)
    (hmesh : ∀ j i, i < k j → r j (i + 1) - r j i ≤ δ j)
    (hwidth : ∀ j, r j (k j) - r j 0 ≤ T) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => ∑ i ∈ Finset.range (k j), (r j (i + 1) - r j i) ^ α)
      atTop (𝓝 0) := by
  have hupper (j) := (sum_increment_rpow_le (k j) (r j) hα (hinc j) (hmesh j)).trans
    (mul_le_mul_of_nonneg_left (hwidth j) (Real.rpow_nonneg (hδ j) _))
  have hzero := (hlim.rpow_const_nhds_zero (sub_pos.mpr hα)).mul_const T
  simp only [zero_mul] at hzero
  exact squeeze_zero (fun j => Finset.sum_nonneg fun i hi =>
    Real.rpow_nonneg (hinc j i (Finset.mem_range.mp hi)) α) hupper hzero

end Critical2DKPZ.SHF.Tsai

end
