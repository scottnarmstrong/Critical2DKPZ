/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25InteractingRenewal
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Critical2DKPZ.MomentBounds.CCR25SequenceRunCompression
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Tactic

/-! # A timed interaction run is bounded by the CCR25 renewal kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The contribution of a prescribed finite list of positive collision gaps
inside one fixed partition run. The gaps are listed from the last collision
back toward the first, matching CCR25's final-free-interval recursion. -/
def ccr25TimedInteractionRunAbs {h : ℕ} (β : ℝ) (I : ReplicaPartition h) :
    List ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ
  | [], z, x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0
  | d :: ds, z, x =>
      |replicaPartitionDisorderMoment β I| *
        ∑' y : LatticeConfiguration h,
          ccr25TimedInteractionRunAbs β I ds z y *
            freeReplicaKernel d I I y x

/-- A prescribed timed interaction run has nonnegative weight. -/
theorem ccr25TimedInteractionRunAbs_nonneg {h : ℕ} (β : ℝ)
    (I : ReplicaPartition h) :
    ∀ gaps z x, 0 ≤ ccr25TimedInteractionRunAbs β I gaps z x := by
  intro gaps
  induction gaps with
  | nil =>
      intro z x
      simp only [ccr25TimedInteractionRunAbs]
      split_ifs <;> norm_num
  | cons d ds ih =>
      intro z x
      simp only [ccr25TimedInteractionRunAbs]
      apply mul_nonneg (abs_nonneg _)
      apply tsum_nonneg
      intro y
      exact mul_nonneg (ih z y) (freeReplicaKernel_nonneg d I I y x)

private def ccr25RunEndpointConfigurations {h : ℕ} (d : ℕ)
    (x : LatticeConfiguration h) : Finset (LatticeConfiguration h) :=
  Fintype.piFinset fun i : Fin h => Critical2DKPZ.Polymer.endpoints (x i) d

private theorem freeReplicaKernel_zero_of_not_runEndpointConfigurations
    {h : ℕ} (d : ℕ) (I : ReplicaPartition h)
    (y x : LatticeConfiguration h)
    (hy : y ∉ ccr25RunEndpointConfigurations d x) :
    freeReplicaKernel d I I y x = 0 := by
  have hmissing : ∃ i : Fin h,
      y i ∉ Critical2DKPZ.Polymer.endpoints (x i) d := by
    by_contra hnot
    apply hy
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmissing
  have hq : Critical2DKPZ.srwKernel d (x i - y i) = 0 := by
    rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem d (x i) (y i) hi
  have hprod : (∏ j : Fin h, Critical2DKPZ.srwKernel d (x j - y j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hq
  simp [freeReplicaKernel, hprod]

/-- A free replica kernel has finite support in its source endpoint, so any
function multiplied by it is summable as the source varies. -/
theorem summable_mul_freeReplicaKernel_right {h : ℕ}
    (f : LatticeConfiguration h → ℝ) (d : ℕ) (I : ReplicaPartition h)
    (x : LatticeConfiguration h) :
    Summable (fun y => f y * freeReplicaKernel d I I y x) := by
  apply summable_of_ne_finset_zero (s := ccr25RunEndpointConfigurations d x)
  intro y hy
  rw [freeReplicaKernel_zero_of_not_runEndpointConfigurations d I y x hy]
  ring


end

end Critical2DKPZ.MomentBounds
