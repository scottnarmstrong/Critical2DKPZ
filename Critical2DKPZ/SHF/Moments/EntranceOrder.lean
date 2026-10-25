/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionEntrance
import Mathlib.Tactic

/-! # Positivity and absolute-test comparison for collision entrances -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments

/-- Taking the absolute value of the test dominates a signed collision slice. -/
theorem collisionSlice_abs_le_absTest (r : ℕ) (a b : Site) (f : Site → ℝ) :
    |collisionSlice r a b f| ≤ collisionSlice r a b (fun z => |f z|) := by
  unfold collisionSlice
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro z _hz
  rw [abs_mul, abs_mul, abs_of_nonneg (srwKernel_nonneg _ _),
    abs_of_nonneg (srwKernel_nonneg _ _)]

/-- Absolute-test domination for an entire microscopic entrance window. -/
theorem collisionEntrance_abs_le_absTest (N lo hi : ℕ) (a b : Site) (F : ℝ × Plane → ℝ) :
    |collisionEntrance N lo hi a b F| ≤ collisionEntrance N lo hi a b (fun p => |F p|) := by
  unfold collisionEntrance
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun r _hr => collisionSlice_abs_le_absTest r a b _

/-- Enlarging a clock window increases every nonnegative entrance test. -/
theorem collisionEntrance_mono_window (N lo hi lo' hi' : ℕ) (a b : Site)
    (F : ℝ × Plane → ℝ) (hF : ∀ p, 0 ≤ F p) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    collisionEntrance N lo hi a b F ≤ collisionEntrance N lo' hi' a b F := by
  unfold collisionEntrance
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc hlo hhi)
  intro r _hr _hnot
  exact collisionSlice_nonneg r a b (fun z => hF _)

end Critical2DKPZ.SHF.Moments
