/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25Operators
public import Critical2DKPZ.MomentBounds.CollisionStrata
import Mathlib.Tactic

/-! # Free transitions onto a pair stratum -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- The bottom partition imposes no collision constraint. -/
theorem isCollisionConfiguration_bot {h : ℕ} (z : Fin h → Site) :
    IsCollisionConfiguration (⊥ : ReplicaPartition h) z := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg z hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

/-- For a single-pair partition, the exact CCR stratum is its pair-equality
stratum; the separation condition adds no restriction. -/
theorem collisionWord_pairPartition_collision_iff {h : ℕ}
    (α : CollisionPair h) (x : Fin h → Site) :
    IsCollisionConfiguration (pairPartition α) x ↔ x α.1.1 = x α.1.2 := by
  constructor
  · intro hx
    exact (isEqualityConfiguration_pair_iff α x).mp hx.1
  · intro hpair
    refine ⟨(isEqualityConfiguration_pair_iff α x).mpr hpair, ?_⟩
    intro i j hi hj hnot
    obtain ⟨i', hi'ne, hi'rel⟩ := hi
    obtain ⟨j', hj'ne, hj'rel⟩ := hj
    have hipair : i = α.1.1 ∨ i = α.1.2 := by
      have hrel := (pairPartition_rel α i i').mp hi'rel
      rcases hrel with hEq | ⟨hleft, _⟩
      · exact (hi'ne hEq.symm).elim
      · exact hleft
    have hjpair : j = α.1.1 ∨ j = α.1.2 := by
      have hrel := (pairPartition_rel α j j').mp hj'rel
      rcases hrel with hEq | ⟨hleft, _⟩
      · exact (hj'ne hEq.symm).elim
      · exact hleft
    have hij : (pairPartition α).r i j :=
      (pairPartition_rel α i j).mpr (Or.inr ⟨hipair, hjpair⟩)
    exact (hnot hij).elim

/-- The unrestricted initial replica walk, restricted to an equality endpoint,
is the product walk kernel on the pair stratum. Off that stratum the CCR
kernel vanishes. -/
theorem freeReplicaKernel_bot_pair_eq {h : ℕ} (α : CollisionPair h)
    (n : ℕ) (x u : Fin h → Site) :
    freeReplicaKernel n ⊥ (pairPartition α) x u =
      if u α.1.1 = u α.1.2 then ∏ i, srwKernel n (u i - x i) else 0 := by
  simp [freeReplicaKernel, isCollisionConfiguration_bot,
    collisionWord_pairPartition_collision_iff]

end Critical2DKPZ.SHF.Moments

end
