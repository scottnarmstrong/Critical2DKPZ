/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25StartBoundaryIdentity
import Mathlib.Tactic

/-! # Time-reversed CCR boundary profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open scoped BigOperators

open Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

private theorem isCollisionConfiguration_bot_for_terminal_boundary {h : ℕ} (z : LatticeConfiguration h) :
    IsCollisionConfiguration (⊥ : ReplicaPartition h) z := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg z hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

/-- The free replica kernel is symmetric when its initial and terminal
collision partitions are interchanged. -/
theorem freeReplicaKernel_timeReverse {h : ℕ} (n : ℕ)
    (I : ReplicaPartition h) (x z : LatticeConfiguration h) :
    freeReplicaKernel n I ⊥ x z = freeReplicaKernel n ⊥ I z x := by
  by_cases hI : IsCollisionConfiguration I x
  · have hprod :
        (∏ i : Fin h, Critical2DKPZ.srwKernel n (z i - x i)) =
          ∏ i : Fin h, Critical2DKPZ.srwKernel n (x i - z i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Critical2DKPZ.Polymer.srwKernel_sub_swap n (z i) (x i)
    rw [freeReplicaKernel, freeReplicaKernel]
    simp only [hI, isCollisionConfiguration_bot_for_terminal_boundary]
    simpa using congrArg (fun q : ℝ => q) hprod
  · rw [freeReplicaKernel, freeReplicaKernel]
    simp [hI]

/-- Summing a terminal product profile against a free kernel is the CCR25
boundary vector, by symmetry of the simple random walk kernel. -/
theorem finite_sum_terminalProfile_mul_freeReplicaKernel_eq_boundaryVector
    {h : ℕ} (n : ℕ) (I : ReplicaPartition h) (A : Finset Critical2DKPZ.Site)
    (φ : Critical2DKPZ.Site → ℝ) (x : LatticeConfiguration h) :
    (∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (z i)) * freeReplicaKernel n I ⊥ x z) =
      replicaBoundaryVector n I A φ x := by
  calc
    _ = ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (z i)) * freeReplicaKernel n ⊥ I z x := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [freeReplicaKernel_timeReverse]
    _ = replicaBoundaryVector n I A φ x :=
      finite_sum_startProfile_mul_freeReplicaKernel_eq_boundaryVector n I A φ x

/-- Summing a horizon-hatted free kernel against a terminal product profile
is exactly the time-hatted CCR boundary vector. -/
theorem finite_sum_terminalProfile_mul_hattedFreeReplicaKernel_eq_hattedBoundaryVector
    {h : ℕ} (L : ℕ) (I : ReplicaPartition h) (A : Finset Critical2DKPZ.Site)
    (φ : Critical2DKPZ.Site → ℝ) (x : LatticeConfiguration h) :
    (∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (z i)) * hattedFreeReplicaKernel L I ⊥ x z) =
      hattedReplicaBoundaryVector L I A φ x := by
  calc
    _ = ∑ n ∈ Finset.range L,
        ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (z i)) * freeReplicaKernel (n + 1) I ⊥ x z := by
          simp only [hattedFreeReplicaKernel, Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range L,
        replicaBoundaryVector (n + 1) I A φ x := by
          apply Finset.sum_congr rfl
          intro n hn
          exact finite_sum_terminalProfile_mul_freeReplicaKernel_eq_boundaryVector
            (n + 1) I A φ x
    _ = hattedReplicaBoundaryVector L I A φ x := by
          simp [hattedReplicaBoundaryVector]

end Critical2DKPZ.SHF.Moments

end
