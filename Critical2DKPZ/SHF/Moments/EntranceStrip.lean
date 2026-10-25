/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionEntrance
import Mathlib.Tactic

/-!
# Small-time entrance bounds away from the collision diagonal

A Gaussian bound gives a time-uniform inverse-square displacement bound. Summing
this bound controls a short entrance strip without a harmonic logarithmic loss.
-/

public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- Away from the origin the walk kernel is bounded uniformly in time by an inverse squared spatial distance. -/
theorem srwKernel_inverse_square_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ z : Site, 0 < ‖siteToPlane z‖ ^ 2 →
      srwKernel n z ≤ C / ‖siteToPlane z‖ ^ 2 := by
  obtain ⟨C, c, hC, hc, h⟩ := srwKernel_gaussianBound_all_times
  refine ⟨C / c, by positivity, fun n z hz => ?_⟩
  have hz0 : ‖siteToPlane z‖ ≠ 0 := (sq_pos_iff).mp hz
  let u := c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)
  have hu : u * Real.exp (-u) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one u).trans (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    _ ≤ C / ((n : ℝ) + 1) * Real.exp (-u) := by
      simpa only [u, neg_div, neg_mul] using h n z
    _ = (C / (c * ‖siteToPlane z‖ ^ 2)) * (u * Real.exp (-u)) := by
      dsimp only [u]
      field_simp [hz0]
    _ ≤ (C / (c * ‖siteToPlane z‖ ^ 2)) * 1 :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by ring

/-- Uniform control of the first K microscopic times for a nonzero displacement. -/
theorem collisionEntrance_short_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N K : ℕ, ∀ a b : Site, ∀ F : ℝ × Plane → ℝ,
      ∀ M : ℝ, 0 ≤ M → (∀ p, |F p| ≤ M) → 0 < ‖siteToPlane (b - a)‖ ^ 2 →
      |collisionEntrance N 0 K a b F| ≤
        M * ((K : ℝ) + 1) * C / ‖siteToPlane (b - a)‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := srwKernel_inverse_square_bound
  refine ⟨C, hC, fun N K a b F M hM hF hd => ?_⟩
  calc
    _ ≤ M * ∑ r ∈ Finset.Icc 0 K, srwKernel (2 * r) (b - a) :=
      collisionEntrance_abs_le N 0 K a b hF
    _ ≤ M * ∑ _r ∈ Finset.Icc 0 K, C / ‖siteToPlane (b - a)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => h (2 * r) (b - a) hd) hM
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring

end Critical2DKPZ.SHF.Moments
