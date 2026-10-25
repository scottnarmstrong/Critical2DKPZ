/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedPathWeight
import Mathlib.Tactic

/-! # Terminal mass of the non-pair remainder -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Summing over any finite terminal set is bounded by the point-to-plane
marked partition expansion. The terminal microscopic interaction is retained. -/
theorem collisionWord_sum_nonpairCollisionRemainder_le_markedPartitionSum
    (β : ℝ) (n h : ℕ) (x : LatticeConfiguration h)
    (B : Finset (LatticeConfiguration h)) :
    (∑ y ∈ B, nonpairCollisionRemainder β n h x y) ≤
      ∑ I ∈ collisionWordMarkedPartitionSequences h n,
        (∏ j : Fin n, |replicaPartitionDisorderMoment β (I j)|) *
          replicaPathWeight (List.ofFn I) x := by
  classical
  let c := fun paths : Fin h → Fin n → Fin 4 => ((4 : ℝ)⁻¹ ^ n) ^ h *
    ∑ I ∈ collisionWordMarkedPartitionSequences h n,
      ∏ j : Fin n, collisionWordLocalAbsPartitionWeight β
        (fun i => walkPosition (x i) (paths i) (j.val + 1)) (I j)
  have hc : ∀ paths, 0 ≤ c paths := by
    intro paths
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro I hI
    exact Finset.prod_nonneg (fun j hj => collisionWordLocalAbsPartitionWeight_nonneg _ _ _)
  have hdelta (paths : Fin h → Fin n → Fin 4) :
      (∑ y ∈ B, ∏ i, if walkPosition (x i) (paths i) n = y i then (1 : ℝ) else 0) ≤ 1 := by
    have heq (y : LatticeConfiguration h) :
        (∏ i, if walkPosition (x i) (paths i) n = y i then (1 : ℝ) else 0) =
          if (fun i => walkPosition (x i) (paths i) n) = y then 1 else 0 := by
      simp only [Fintype.prod_ite_zero, Finset.prod_const_one, ← funext_iff]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq]
    split_ifs <;> norm_num
  calc
    _ ≤ ∑ y ∈ B, ∑ paths : Fin h → Fin n → Fin 4,
        c paths * ∏ i, if walkPosition (x i) (paths i) n = y i then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      exact nonpairCollisionRemainder_le_markedPartitionPaths β n h x y
    _ = ∑ paths : Fin h → Fin n → Fin 4, c paths *
        ∑ y ∈ B, ∏ i, if walkPosition (x i) (paths i) n = y i then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ paths : Fin h → Fin n → Fin 4, c paths := by
      apply Finset.sum_le_sum
      intro paths hpaths
      exact mul_le_of_le_one_right (hc paths) (hdelta paths)
    _ = _ := collisionWord_markedPartitionPathAverage_eq β x

end Critical2DKPZ.SHF.Moments

end
