/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Replica partitions and the two collision-stratum conventions

A partition is its equivalence relation on the finite label set. LZ21 imposes
only equality inside blocks. CCR25 additionally separates distinct nonsingleton
blocks, while allowing singleton labels to coincide with all other coordinates.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- A partition of the replica labels, represented by its equivalence relation. -/
abbrev ReplicaPartition (h : ℕ) := Setoid (Fin h)

/-- A lattice configuration of h replicas. -/
abbrev LatticeConfiguration (h : ℕ) := Fin h → Site

/-- A label belongs to a nonsingleton block. -/
def InCollisionBlock {h : ℕ} (I : ReplicaPartition h) (i : Fin h) : Prop :=
  ∃ j : Fin h, j ≠ i ∧ I.r i j

/-- LZ21's equality-only condition. No separation of different blocks is imposed. -/
def IsEqualityConfiguration {h : ℕ} (I : ReplicaPartition h) (x : LatticeConfiguration h) : Prop :=
  ∀ i j, I.r i j → x i = x j

/-- CCR25's additional separation applies precisely to distinct nonsingleton blocks. -/
def IsCollisionConfiguration {h : ℕ} (I : ReplicaPartition h) (x : LatticeConfiguration h) : Prop :=
  IsEqualityConfiguration I x ∧ ∀ i j,
    InCollisionBlock I i → InCollisionBlock I j → ¬I.r i j → x i ≠ x j



/-- A pair partition has exactly one nonsingleton block, the indicated pair. -/
@[instance_reducible] def pairPartition {h : ℕ} (α : DeltaBose.CollisionPair h) : ReplicaPartition h where
  r i j := i = j ∨ (i = α.val.1 ∨ i = α.val.2) ∧ (j = α.val.1 ∨ j = α.val.2)
  iseqv := ⟨fun _ => Or.inl rfl,
    fun hij => hij.elim (fun he => Or.inl he.symm) (fun he => Or.inr ⟨he.2, he.1⟩),
    fun hij hjk => by
      rcases hij with rfl | hij
      · exact hjk
      rcases hjk with rfl | hjk
      · exact Or.inr hij
      exact Or.inr ⟨hij.1, hjk.2⟩⟩

/-- Membership in the pair-partition relation is characterized by equality or the selected pair. -/
theorem pairPartition_rel {h : ℕ} (α : DeltaBose.CollisionPair h) (i j : Fin h) :
    (pairPartition α).r i j ↔ i = j ∨
      (i = α.val.1 ∨ i = α.val.2) ∧ (j = α.val.1 ∨ j = α.val.2) := Iff.rfl

/-- The two selected labels are related by their pair partition. -/
theorem pairPartition_related {h : ℕ} (α : DeltaBose.CollisionPair h) :
    (pairPartition α).r α.val.1 α.val.2 := Or.inr ⟨Or.inl rfl, Or.inr rfl⟩

/-- A pair-partition equality configuration is exactly one with the selected coordinates equal. -/
theorem isEqualityConfiguration_pair_iff {h : ℕ} (α : DeltaBose.CollisionPair h)
    (x : LatticeConfiguration h) :
    IsEqualityConfiguration (pairPartition α) x ↔ x α.val.1 = x α.val.2 := by
  constructor
  · intro hx
    exact hx _ _ (pairPartition_related α)
  · intro hx i j hij
    rcases hij with rfl | ⟨hi, hj⟩
    · rfl
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exact hx
    · exact hx.symm
    · rfl



end Critical2DKPZ.MomentBounds
