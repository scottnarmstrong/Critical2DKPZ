/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.GaussianMultiplicity
import Mathlib.Tactic

/-!
# Exact pair counting at multiple collisions

The square of each occupation multiplicity counts the diagonal plus twice the
unordered coincident pairs. This includes triple and quadruple coincidences exactly.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- Number of unordered coincident pairs, each pair counted once by the index order. -/
def collisionCount {ι α : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq α]
    (e : ι → α) : ℝ :=
  ∑ i, ∑ j, if i < j ∧ e i = e j then 1 else 0



/-- The ordered coincidence sum equals the family size plus twice its unordered collision count. -/
theorem sum_coincidences {ι α : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq α] (e : ι → α) :
    (∑ i, ∑ j, if e i = e j then (1 : ℝ) else 0) =
      (Fintype.card ι : ℝ) + 2 * collisionCount e := by
  have hid (i j : ι) :
      (if e i = e j then (1 : ℝ) else 0) =
        (if i < j ∧ e i = e j then 1 else 0) +
        (if j < i ∧ e j = e i then 1 else 0) + (if i = j then 1 else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [h, not_lt_of_gt h, false_and, ite_false, ne_of_lt h,
        true_and, add_zero]
    · subst j
      simp only [lt_self_iff_false, false_and, ite_false, zero_add, ite_true]
    · simp only [h, not_lt_of_gt h, false_and, ite_false, ne_of_gt h, add_zero,
        zero_add]
      by_cases he : e i = e j
      · simp only [he, ite_true, and_true]
      · simp only [he, Ne.symm he, ite_false, and_false]
  simp_rw [hid, Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, if j < i ∧ e j = e i then (1 : ℝ) else 0) =
      collisionCount e := Finset.sum_comm
  rw [hswap]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  change collisionCount e + collisionCount e + (Fintype.card ι : ℝ) = _
  ring

/-- The squared grouped coordinate coefficients equal the sum of coefficient products over coincident indices. -/
theorem sum_coordinateCoefficient_sq {ι : Type*} [Fintype ι]
    (e : ι → ℕ × Site) (c : ι → ℝ) :
    (∑ z : ↥(Finset.univ.image e), coordinateCoefficient e c z.val ^ 2) =
      ∑ i, ∑ j, if e i = e j then c i * c j else 0 := by
  classical
  calc
    _ = ∑ z : ↥(Finset.univ.image e),
        coordinateCoefficient e c z.val * coordinateCoefficient e c z.val := by
      simp only [pow_two]
    _ = ∑ i, c i * coordinateCoefficient e c (e i) :=
      sum_coordinateCoefficient e c _
    _ = _ := by
      unfold coordinateCoefficient
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : e i = e j
      · simp only [h, ite_true]
      · simp only [h, Ne.symm h, ite_false, mul_zero]

/-- Equal coordinate coefficients give a squared mass determined by the family size and collision count. -/
theorem sum_constantCoefficient_sq {ι : Type*} [Fintype ι] [LinearOrder ι]
    (e : ι → ℕ × Site) (β : ℝ) :
    (∑ z : ↥(Finset.univ.image e), coordinateCoefficient e (fun _ => β) z.val ^ 2) =
      β ^ 2 * ((Fintype.card ι : ℝ) + 2 * collisionCount e) := by
  rw [sum_coordinateCoefficient_sq, ← sum_coincidences e]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

end Critical2DKPZ.SHF.Moments
