/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedPaths
public import Critical2DKPZ.MomentBounds.CCR25RunExpansion
public import Critical2DKPZ.MomentBounds.CCR25SequenceMomentProduct
import Mathlib.Tactic

/-! # From microscopic absolute partition weights to CCR partition paths -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- The bottom letter has unit moment and imposes no collision restriction. -/
theorem collisionWord_localAbsPartitionWeight_eq_moment_mul_indicator
    (β : ℝ) {h : ℕ} (x : LatticeConfiguration h) (I : ReplicaPartition h) :
    collisionWordLocalAbsPartitionWeight β x I =
      |replicaPartitionDisorderMoment β I| * collisionIndicator I x := by
  classical
  by_cases hI : I = ⊥
  · subst I
    simp [collisionWordLocalAbsPartitionWeight, replicaPartitionDisorderMoment_bot_eq_one,
      collisionIndicator, isCollisionConfiguration_bot]
  · by_cases hx : IsCollisionConfiguration I x <;>
      simp [collisionWordLocalAbsPartitionWeight, hI, collisionIndicator, hx]

/-- Averaging the absolute local weights of a prescribed history is exactly
its CCR moment coefficient times its constrained replica walk probability. -/
theorem collisionWord_localAbsPartitionPathAverage_eq {h n : ℕ}
    (β : ℝ) (I : Fin n → ReplicaPartition h) (x : LatticeConfiguration h) :
    (∑ paths : Fin h → Fin n → Fin 4, ((4 : ℝ)⁻¹ ^ n) ^ h *
      ∏ j : Fin n, collisionWordLocalAbsPartitionWeight β
        (fun i => walkPosition (x i) (paths i) (j.val + 1)) (I j)) =
      (∏ j : Fin n, |replicaPartitionDisorderMoment β (I j)|) *
        replicaPathWeight (List.ofFn I) x := by
  classical
  have hpow : ((4 : ℝ)⁻¹ ^ n) ^ h = ((4 : ℝ)⁻¹ ^ h) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n h]
  simp only [replicaPathWeight_listOfFn_eq_directionSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro paths hpaths
  simp_rw [collisionWord_localAbsPartitionWeight_eq_moment_mul_indicator]
  rw [Finset.prod_mul_distrib, hpow]
  dsimp [ccr25RunPathCollisionWeight]
  ring

/-- Summing marked microscopic histories commutes with the finite walk
average, retaining their non-pair mark exactly. -/
theorem collisionWord_markedPartitionPathAverage_eq {h n : ℕ}
    (β : ℝ) (x : LatticeConfiguration h) :
    (∑ paths : Fin h → Fin n → Fin 4, ((4 : ℝ)⁻¹ ^ n) ^ h *
      ∑ I ∈ collisionWordMarkedPartitionSequences h n,
        ∏ j : Fin n, collisionWordLocalAbsPartitionWeight β
          (fun i => walkPosition (x i) (paths i) (j.val + 1)) (I j)) =
    ∑ I ∈ collisionWordMarkedPartitionSequences h n,
      (∏ j : Fin n, |replicaPartitionDisorderMoment β (I j)|) *
        replicaPathWeight (List.ofFn I) x := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  exact collisionWord_localAbsPartitionPathAverage_eq β I x

end Critical2DKPZ.SHF.Moments

end
