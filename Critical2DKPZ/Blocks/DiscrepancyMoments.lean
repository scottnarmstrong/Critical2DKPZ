/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
import Mathlib.Tactic

/-! # Finite moments and terminal-time substitution for discrepancy strings -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

/-- Closed discrepancy strings have every positive finite moment. -/
theorem memLp_closedDiscrepancy (β : ℝ) (t : ℕ → ℕ) (u v : ℕ)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    MemLp (closedDiscrepancy β t u v) p disorderLaw := by
  have hp2zero : 2 * p ≠ 0 := mul_ne_zero (by norm_num) hp0
  have hp2top : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hp
  have heq : closedDiscrepancy β t u v = fun ω =>
      ∑ x ∈ closedStartSupport t u, ∑ y ∈ discrepancyStringSupport t u (v - u) x,
        srwKernel (t (u - 1)) x * discrepancyString β t u (v - u) x y ω *
          pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω := by
    funext ω
    unfold closedDiscrepancy
    rw [tsum_eq_sum (s := closedStartSupport t u)]
    · apply Finset.sum_congr rfl
      intro x hx
      apply tsum_eq_sum
      intro y hy
      rw [discrepancyString_eq_zero_of_not_mem_support β t u (v - u) x y ω hy,
        mul_zero, zero_mul]
    · intro x hx
      have hzero : srwKernel (t (u - 1)) x = 0 := by
        simpa only [sub_zero] using
          Polymer.srwKernel_eq_zero_of_not_mem (t (u - 1)) 0 x hx
      simp only [hzero, zero_mul, tsum_zero]
  rw [heq]
  apply memLp_finsetSum
  intro x hx
  apply memLp_finsetSum
  intro y hy
  exact Polymer.memLp_mul_double p
    ((memLp_discrepancyString β t u (v - u) x y (2 * p) hp2zero hp2top).const_mul _)
    (Polymer.memLp_pointToPlane β (t (v - 1)) (t v - t (v - 1)) y (2 * p) hp2top)

/-- The square of a closed discrepancy is integrable. -/
theorem integrable_sq_closedDiscrepancy (β : ℝ) (t : ℕ → ℕ) (u v : ℕ) :
    Integrable (fun ω => closedDiscrepancy β t u v ω ^ 2) disorderLaw := by
  have h := (memLp_closedDiscrepancy β t u v 2 (by norm_num) (by norm_num)).integrable_norm_pow'
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- Changing the terminal grid value leaves the earlier discrepancy kernels unchanged. -/
theorem discrepancyString_update_terminal (β : ℝ) (t : ℕ → ℕ) (T u v k : ℕ)
    (hk : u + k ≤ v) (x y : Site) (ω : Disorder) :
    discrepancyString β (Function.update t v T) u k x y ω =
      discrepancyString β t u k x y ω := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      have hik : u + k ≠ v := by omega
      have hip : u + k - 1 ≠ v := by omega
      simp only [discrepancyString]
      apply tsum_congr
      intro z
      rw [ih (by omega)]
      simp only [blockDiscrepancy, blockKernel, Function.update_of_ne hik,
        Function.update_of_ne hip]

/-- An open string is a closed string with its terminal grid value replaced. -/
theorem openDiscrepancyMass_eq_closedDiscrepancy_update (β : ℝ) (t : ℕ → ℕ)
    (T : ℕ) {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) (ω : Disorder) :
    openDiscrepancyMass β t T u v ω =
      closedDiscrepancy β (Function.update t v T) u v ω := by
  have hstart : u - 1 ≠ v := by omega
  have hend : v - 1 ≠ v := by omega
  unfold openDiscrepancyMass closedDiscrepancy
  simp only [Function.update_of_ne hstart, Function.update_of_ne hend,
    Function.update_self]
  apply tsum_congr
  intro x
  apply tsum_congr
  intro y
  rw [discrepancyString_update_terminal β t T u v (v - u) (by omega)]

end Critical2DKPZ.Blocks
