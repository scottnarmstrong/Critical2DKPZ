/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.PointToPoint
public import Critical2DKPZ.Definitions.PointToPlane
public import Critical2DKPZ.Definitions.ProfileP2Fun
public import Critical2DKPZ.Definitions.SmoothedP2Plane
public import Critical2DKPZ.Definitions.SrwKernel
import Mathlib.Tactic

/-! Finite polymer path weights include disorder at times `a+1,…,a+n`, as in equation (1.3), and yield measurable partition functions supported on reachable endpoints. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- The Boltzmann weight of a fixed walk, excluding its initial disorder slice. -/
def pathWeight (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) : ℝ :=
  Real.exp (∑ j ∈ Finset.Icc 1 n,
    (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2))

/-- A site is reachable when an `n`-step nearest-neighbour path from the starting site ends there. -/
def Reachable (n : ℕ) (w z : Site) : Prop :=
  ∃ s : Fin n → Fin 4, walkPosition w s n = z

/-- The polymer path weight is strictly positive. -/
theorem pathWeight_pos (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    0 < pathWeight β a w s ω :=
  Real.exp_pos _


/-- The polymer path weight is measurable. -/
theorem measurable_pathWeight (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) :
    Measurable (pathWeight β a w s) := by
  unfold pathWeight
  fun_prop

/-- The point-to-plane partition function is a finite sum of weighted paths. -/
theorem pointToPlane_eq_sum (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane β a n w ω =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω := rfl

/-- The point-to-point partition function is a finite sum of endpoint-constrained weighted paths. -/
theorem pointToPoint_eq_sum (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β a n w z ω =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
        if walkPosition w s n = z then 1 else 0 := rfl

/-- The point-to-plane partition function is strictly positive. -/
theorem pointToPlane_pos (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    0 < pointToPlane β a n w ω := by
  rw [pointToPlane_eq_sum]
  exact Finset.sum_pos (fun _ _ => mul_pos (by positivity) (pathWeight_pos ..))
    Finset.univ_nonempty

/-- The point-to-point partition function is nonnegative. -/
theorem pointToPoint_nonneg (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    0 ≤ pointToPoint β a n w z ω := by
  rw [pointToPoint_eq_sum]
  exact Finset.sum_nonneg fun s _ => mul_nonneg
    (mul_nonneg (by positivity) (pathWeight_pos β a w s ω).le)
    (by split_ifs <;> positivity)

/-- The point-to-point partition function is positive exactly at reachable endpoints. -/
theorem pointToPoint_pos_iff (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    0 < pointToPoint β a n w z ω ↔ Reachable n w z := by
  rw [pointToPoint_eq_sum]
  rw [Finset.sum_pos_iff_of_nonneg (fun s _ => mul_nonneg
    (mul_nonneg (by positivity) (pathWeight_pos β a w s ω).le)
    (by split_ifs <;> positivity))]
  · constructor
    · rintro ⟨s, _, hs⟩
      refine ⟨s, ?_⟩
      by_contra h
      simp only [ite_eq_right h, mul_zero, lt_self_iff_false] at hs
    · rintro ⟨s, hs⟩
      exact ⟨s, Finset.mem_univ _, by
        rw [ite_eq_left hs, mul_one]
        exact mul_pos (by positivity) (pathWeight_pos ..)⟩

/-- The point-to-point partition function vanishes exactly at unreachable endpoints. -/
theorem pointToPoint_eq_zero_iff (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β a n w z ω = 0 ↔ ¬ Reachable n w z := by
  constructor
  · intro hz hr
    have hp := (pointToPoint_pos_iff β a n w z ω).2 hr
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hr
    exact le_antisymm (le_of_not_gt fun hp =>
      hr ((pointToPoint_pos_iff β a n w z ω).1 hp))
      (pointToPoint_nonneg β a n w z ω)

/-- The point-to-point partition function is bounded by the point-to-plane partition function. -/
theorem pointToPoint_le_pointToPlane (β : ℝ) (a n : ℕ)
    (w z : Site) (ω : Disorder) :
    pointToPoint β a n w z ω ≤ pointToPlane β a n w ω := by
  rw [pointToPoint_eq_sum, pointToPlane_eq_sum]
  exact Finset.sum_le_sum fun s _ => by
    split_ifs
    · exact le_of_eq (mul_one _)
    · rw [mul_zero]
      exact mul_nonneg (by positivity) (pathWeight_pos β a w s ω).le


/-- The point-to-plane partition function is measurable. -/
theorem measurable_pointToPlane (β : ℝ) (a n : ℕ) (w : Site) :
    Measurable (pointToPlane β a n w) := by
  unfold pointToPlane
  fun_prop


/-- The point-to-point partition function is measurable. -/
theorem measurable_pointToPoint (β : ℝ) (a n : ℕ) (w z : Site) :
    Measurable (pointToPoint β a n w z) := by
  unfold pointToPoint
  fun_prop

/-- The walk position at time zero is its starting site. -/
@[simp]
theorem walkPosition_zero {n : ℕ} (w : Site) (s : Fin n → Fin 4) :
    walkPosition w s 0 = w := by
  simp [walkPosition]

/-- Changing the starting site translates every walk position. -/
theorem walkPosition_add_start {n : ℕ} (w v : Site)
    (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition (w + v) s j = w + walkPosition v s j := by
  simp only [walkPosition, add_assoc]

/-- A walk position is its starting site plus its displacement from the origin. -/
theorem walkPosition_eq_start_add {n : ℕ} (w : Site)
    (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition w s j = w + walkPosition 0 s j := by
  simp only [walkPosition, zero_add]

/-- The path weight over zero time is one. -/
@[simp]
theorem pathWeight_zero (β : ℝ) (a : ℕ) (w : Site)
    (s : Fin 0 → Fin 4) (ω : Disorder) :
    pathWeight β a w s ω = 1 := by
  simp [pathWeight]

/-- The point-to-plane partition function at zero duration is one. -/
@[simp]
theorem pointToPlane_zero (β : ℝ) (a : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane β a 0 w ω = 1 := by
  simp [pointToPlane_eq_sum]

/-- The point-to-point partition function at zero duration is the identity kernel. -/
@[simp]
theorem pointToPoint_zero (β : ℝ) (a : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β a 0 w z ω = if w = z then 1 else 0 := by
  simp [pointToPoint_eq_sum]

end Critical2DKPZ.Polymer
