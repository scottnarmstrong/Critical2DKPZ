/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Estimates
import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # Gaussian walk bounds including the zero-time slice -/

public section

namespace Critical2DKPZ.SHF.Moments

/-- The parity-correct heat-kernel bound, uniformly at all microscopic times, including time zero. -/
theorem srwKernel_gaussianBound_all_times :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, ∀ z : Site,
      srwKernel n z ≤ C / ((n : ℝ) + 1) *
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)) := by
  obtain ⟨C, c, hc, h⟩ := srwKernel_gaussianBound
  let K := max (2 * C) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : C ≤ K / 2 := by
    have hk : 2 * C ≤ K := le_max_left _ _
    linarith only [hk]
  refine ⟨K, c, hK, hc, fun n z => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [srwKernel_zero]
    by_cases hz : z = 0
    · subst z
      have he : siteToPlane (0 : Site) = 0 := by ext i; simp only [siteToPlane,
        Pi.zero_apply, Int.cast_zero, PiLp.zero_apply]
      simp only [he, Nat.cast_zero, zero_add, div_one, norm_zero, zero_pow (by decide : 2 ≠ 0),
        mul_zero, Real.exp_zero, mul_one, ite_true]
      exact le_max_right _ _
    · rw [ite_eq_right hz]
      positivity
  · have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcoeff : C / (n : ℝ) ≤ K / ((n : ℝ) + 1) := by
      apply (div_le_div_of_nonneg_right hC (by positivity)).trans
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hK, hnr]
    have he : -c * ‖siteToPlane z‖ ^ 2 / (n : ℝ) ≤
        -c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_nonneg hc.le (sq_nonneg ‖siteToPlane z‖)]
    exact (h n hn z).trans (mul_le_mul hcoeff (Real.exp_le_exp.mpr he)
      (Real.exp_pos _).le (by positivity))

end Critical2DKPZ.SHF.Moments
