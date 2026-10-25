/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CollisionStrata
import Mathlib.Tactic

/-!
# Reduction of admissible partitions to two distinct collision pairs

Equal coarser partitions are allowed. Only the common single-pair partition is
excluded. This supplies the reduction implicit in the LZ21 lattice proof.
-/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

instance finite_replicaPartition (h : ℕ) : Finite (ReplicaPartition h) := by
  classical
  apply Finite.of_injective (fun I : ReplicaPartition h => I.r)
  intro I J he
  exact Setoid.ext fun i j => Iff.of_eq (congrFun (congrFun he i) j)

noncomputable instance fintype_replicaPartition (h : ℕ) : Fintype (ReplicaPartition h) :=
  Fintype.ofFinite _

/-- A pair partition refines another partition exactly when its pair is related there. -/
theorem pairPartition_le_iff {h : ℕ} (α : DeltaBose.CollisionPair h) (I : ReplicaPartition h) :
    pairPartition α ≤ I ↔ I.r α.val.1 α.val.2 := by
  constructor
  · intro hle
    exact hle (pairPartition_related α)
  · intro hα i j hij
    rcases hij with rfl | ⟨hi, hj⟩
    · exact I.refl' _
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact I.refl' _
    · exact hα
    · exact I.symm' hα
    · exact I.refl' _

/-- Every non-discrete partition contains a collision pair. -/
theorem exists_collisionPair_of_ne_discrete {h : ℕ} (I : ReplicaPartition h) (hI : I ≠ ⊥) :
    ∃ α : DeltaBose.CollisionPair h, I.r α.val.1 α.val.2 := by
  by_contra hnone
  apply hI
  apply Setoid.ext
  intro i j
  change I.r i j ↔ i = j
  constructor
  · intro hij
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact False.elim (hnone ⟨⟨(i, j), hlt⟩, hij⟩)
    · exact he
    · exact False.elim (hnone ⟨⟨(j, i), hgt⟩, I.symm' hij⟩)
  · rintro rfl
    exact I.refl' _

/-- A partition with precisely one possible collision pair is that single-pair partition. -/
theorem eq_pairPartition_of_only_collisionPair {h : ℕ} (I : ReplicaPartition h)
    (α : DeltaBose.CollisionPair h) (hα : I.r α.val.1 α.val.2)
    (honly : ∀ β : DeltaBose.CollisionPair h, I.r β.val.1 β.val.2 → β = α) :
    I = pairPartition α := by
  apply Setoid.ext
  intro i j
  constructor
  · intro hij
    rcases lt_trichotomy i j with hlt | he | hgt
    · have heq := honly ⟨(i, j), hlt⟩ hij
      rw [← heq]
      exact pairPartition_related ⟨(i, j), hlt⟩
    · exact Or.inl he
    · have heq := honly ⟨(j, i), hgt⟩ (I.symm' hij)
      rw [← heq]
      exact (pairPartition ⟨(j, i), hgt⟩).symm' (pairPartition_related ⟨(j, i), hgt⟩)
  · intro hij
    exact ((pairPartition_le_iff α I).mpr hα) hij

/-- The source admissibility condition yields two different pairs, including equal coarser strata. -/
theorem exists_distinct_collisionPairs {h : ℕ} (I J : ReplicaPartition h)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcommon : ∀ α : DeltaBose.CollisionPair h, ¬(I = pairPartition α ∧ J = pairPartition α)) :
    ∃ α β : DeltaBose.CollisionPair h,
      I.r α.val.1 α.val.2 ∧ J.r β.val.1 β.val.2 ∧ α ≠ β := by
  classical
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  obtain ⟨β, hβ⟩ := exists_collisionPair_of_ne_discrete J hJ
  by_cases hne : α ≠ β
  · exact ⟨α, β, hα, hβ, hne⟩
  have heq : α = β := not_ne_iff.mp hne
  subst β
  by_contra hn
  have hi (γ : DeltaBose.CollisionPair h) (hγ : I.r γ.val.1 γ.val.2) : γ = α := by
    by_contra hγne
    exact hn ⟨γ, α, hγ, hβ, hγne⟩
  have hj (γ : DeltaBose.CollisionPair h) (hγ : J.r γ.val.1 γ.val.2) : γ = α := by
    by_contra hγne
    exact hn ⟨α, γ, hα, hγ, Ne.symm hγne⟩
  exact hcommon α ⟨eq_pairPartition_of_only_collisionPair I α hα hi,
    eq_pairPartition_of_only_collisionPair J α hβ hj⟩


end Critical2DKPZ.MomentBounds
