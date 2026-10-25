/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.LastCollision
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Exact covariance expansion of a discrepancy block -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks


/-- Subtracting a constant terminal profile subtracts that constant times the flat mass. -/
theorem terminalProfile_sub_const (β : ℝ) (a n : ℕ) (w : Site) (f : Site → ℝ)
    (c : ℝ) (ω : Disorder) :
    (∑' z, pointToPoint β a n w z ω * (f z - c)) =
      (∑' z, pointToPoint β a n w z ω * f z) - pointToPlane β a n w ω * c := by
  rw [Polymer.tsum_pointToPoint_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Polymer.pointToPlane_eq_sum,
    ← Polymer.tsum_pointToPoint_mul]

/-- Applying a discrepancy kernel centers the terminal data against the absolute heat profile. -/
theorem blockDiscrepancy_apply (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' y, blockDiscrepancy β t i w y ω * f y) =
      ∑' y, pointToPoint β (t (i - 1)) (t i - t (i - 1)) w y ω *
        (f y - Collision.terminalWalkMean (t i) 0 f) := by
  have hZ : Summable (fun y : Site =>
      pointToPoint β (t (i - 1)) (t i - t (i - 1)) w y ω * f y) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints w (t i - t (i - 1)))
    intro y hy
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β (t (i - 1)) (t i - t (i - 1)) w y ω hy,
      zero_mul]
  have hQ := Collision.summable_terminalWalkMean (t i) 0 f
  simp only [sub_zero] at hQ
  rw [terminalProfile_sub_const]
  calc
    _ = ∑' y, (pointToPoint β (t (i - 1)) (t i - t (i - 1)) w y ω * f y -
        pointToPlane β (t (i - 1)) (t i - t (i - 1)) w ω * (srwKernel (t i) y * f y)) := by
      apply tsum_congr
      intro y
      unfold blockDiscrepancy blockKernel
      ring
    _ = _ := by
      rw [hZ.tsum_sub (hQ.mul_left _), tsum_mul_left]
      simp only [Collision.terminalWalkMean, sub_zero]



end Critical2DKPZ.Blocks
