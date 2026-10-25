/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.RationalShell
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The unweighted lattice estimate of LZ21 Lemma A.1

An elementary shell telescope gives the uniform constant nine. The exponent is
an arbitrary real number at least two. The proof also establishes summability.
-/

public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The sum of squared inverse quadratic denominators over a lattice box is bounded by nine divided by the scale. -/
theorem sum_latticeBox_reciprocal_sq_le {L : ℝ} (hL : 1 ≤ L) (k : ℕ) :
    (∑ z ∈ latticeBox k, 1 / (L + ‖siteToPlane z‖ ^ 2) ^ 2) ≤ 9 / L := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hz : siteToPlane (0 : Site) = 0 := by ext i; simp only [siteToPlane, Pi.zero_apply, Int.cast_zero, PiLp.zero_apply]
  have hr := sum_latticeBox_le_radial
    (fun z => 1 / (L + ‖siteToPlane z‖ ^ 2) ^ 2)
    (fun j => 1 / (L + (j : ℝ) ^ 2) ^ 2) k
    (fun j z hmem => div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity)
        (add_le_add le_rfl (norm_sq_ge_of_mem_latticeShell hmem)) 2))
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hr
  have hsum : (∑ j ∈ Finset.range k,
      (8 * ((j : ℝ) + 1)) * (1 / (L + ((j + 1 : ℕ) : ℝ) ^ 2) ^ 2)) ≤ 8 / L := by
    simp only [Nat.cast_add_one, mul_one_div]
    calc
      _ = 8 * ∑ j ∈ Finset.range k,
          ((j : ℝ) + 1) / (L + ((j : ℝ) + 1) ^ 2) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ 8 * L⁻¹ := mul_le_mul_of_nonneg_left
        ((sum_rational_shell_le L hLpos k).trans (sub_le_self _ (by positivity))) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ 1 / L ^ 2 + 8 / L := hr.trans (add_le_add le_rfl hsum)
    _ ≤ 1 / L + 8 / L := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_left (by norm_num) hLpos (by nlinarith only [hL])
    _ = _ := by ring

/-- Extract the excess exponent uniformly in the spatial coordinate. -/
theorem rpow_neg_le_scaled_reciprocal_sq {L x r : ℝ} (hL : 0 < L) (hx : 0 ≤ x)
    (hr : 2 ≤ r) :
    (L + x) ^ (-r) ≤ L ^ (2 - r) / (L + x) ^ 2 := by
  have hD : 0 < L + x := add_pos_of_pos_of_nonneg hL hx
  have he : (L + x) ^ (-r) = (L + x) ^ (2 - r) / (L + x) ^ 2 := by
    rw [← Real.rpow_natCast (L + x) 2, ← Real.rpow_sub hD]
    congr 1
    norm_num
  rw [he]
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hL (le_add_of_nonneg_right hx) (by linarith only [hr]))
    (sq_nonneg _)

/-- LZ21 A.1, first estimate, with an explicit safe uniform constant and absolute convergence. -/
theorem lattice_rpow_sum_bound {L r : ℝ} (hL : 1 ≤ L) (hr : 2 ≤ r) :
    Summable (fun z : Site => (L + ‖siteToPlane z‖ ^ 2) ^ (-r)) ∧
      (∑' z : Site, (L + ‖siteToPlane z‖ ^ 2) ^ (-r)) ≤ 9 * L ^ (1 - r) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  apply summable_and_tsum_le_of_latticeBox_bound (fun _ => Real.rpow_nonneg (by positivity) _)
  intro k
  calc
    _ ≤ ∑ z ∈ latticeBox k, L ^ (2 - r) / (L + ‖siteToPlane z‖ ^ 2) ^ 2 :=
      Finset.sum_le_sum fun z _ => rpow_neg_le_scaled_reciprocal_sq hLpos (sq_nonneg _) hr
    _ = L ^ (2 - r) * ∑ z ∈ latticeBox k, 1 / (L + ‖siteToPlane z‖ ^ 2) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ L ^ (2 - r) * (9 / L) := mul_le_mul_of_nonneg_left
      (sum_latticeBox_reciprocal_sq_le hL k) (Real.rpow_nonneg hLpos.le _)
    _ = 9 * L ^ (1 - r) := by
      have he : L ^ ((1 : ℝ) - r) = L ^ ((2 : ℝ) - r) / L := by
        calc
          _ = L ^ (((2 : ℝ) - r) - 1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_sub hLpos, Real.rpow_one]
      rw [he]
      ring

end Critical2DKPZ.MomentBounds
