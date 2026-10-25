/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationLocalPartitionGeometry
public import Critical2DKPZ.SHF.Moments.WordDominationLocalPairPart
import Mathlib.Tactic

/-! # Local non-pair events dominated by marked CCR partition moments -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose

attribute [local instance] Classical.propDecidable

private theorem collisionWord_botCollisionLabels_eq_empty (h : ℕ) :
    ccr25PartitionCollisionLabels (⊥ : ReplicaPartition h) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j, hji, hij⟩ := (Finset.mem_filter.mp hi).2
  have he : i = j := by simpa using hij
  exact hji he.symm

private theorem collisionWord_pairCollisionLabels_card_le_two {h : ℕ} (α : CollisionPair h) :
    (ccr25PartitionCollisionLabels (pairPartition α)).card ≤ 2 := by
  classical
  have hsub : ccr25PartitionCollisionLabels (pairPartition α) ⊆ collisionPairLabels α := by
    intro i hi
    obtain ⟨j, hji, hij⟩ := (Finset.mem_filter.mp hi).2
    rcases (pairPartition_rel α i j).mp hij with he | ⟨hi, hj⟩
    · exact (hji he.symm).elim
    · simpa only [collisionPairLabels, Finset.mem_insert, Finset.mem_singleton] using hi
  calc
    _ ≤ (collisionPairLabels α).card := Finset.card_le_card hsub
    _ = 2 := by simp [collisionPairLabels, ne_of_lt α.2]

/-- A nonzero active moment with at least three active labels induces a
non-pair CCR partition. -/
theorem collisionWordLocalPartition_nonpair_of_three_le {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h)) (hcard : 3 ≤ A.card)
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
      chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1) :
    ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A) ≠ ⊥ ∧
      ∀ α : CollisionPair h,
        ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A) ≠ pairPartition α := by
  have hlabels := collisionWordLocalPartition_collisionLabels_eq x A hnoSingleton
  constructor
  · intro he
    rw [he, collisionWord_botCollisionLabels_eq_empty] at hlabels
    have hc : A.card = 0 := by rw [← hlabels]; rfl
    omega
  · intro α he
    have hc := collisionWord_pairCollisionLabels_card_le_two α
    rw [← he, hlabels] at hc
    omega

/-- The local active-label remainder is bounded by the absolute moments of
non-pair partitions whose exact collision strata contain the configuration.
Singleton coordinate terms vanish before the injective reindexing. -/
theorem abs_localNonpair_sum_le_partitionMoments (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    |∑ A ∈ (Finset.univ : Finset (Fin h)).powerset.filter (fun A => 3 ≤ A.card),
      collisionWordLocalVertexMoment β x A| ≤
      ∑ I ∈ (Finset.univ : Finset (ReplicaPartition h)).filter
        (fun I => I ≠ ⊥ ∧ (∀ α : CollisionPair h, I ≠ pairPartition α) ∧
          IsCollisionConfiguration I x), |replicaPartitionDisorderMoment β I| := by
  classical
  let S : Finset (Finset (Fin h)) :=
    (Finset.univ : Finset (Fin h)).powerset.filter (fun A => 3 ≤ A.card)
  let good : Finset (Finset (Fin h)) := S.filter (fun A =>
    ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
      chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1)
  let P : Finset (ReplicaPartition h) := Finset.univ.filter
    (fun I => I ≠ ⊥ ∧ (∀ α : CollisionPair h, I ≠ pairPartition α) ∧
      IsCollisionConfiguration I x)
  let f : Finset (Fin h) → ReplicaPartition h :=
    fun A => ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A)
  have hgood (A : Finset (Fin h)) (hA : A ∈ good) :
      ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
        chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1 :=
    (Finset.mem_filter.mp hA).2
  have hcard (A : Finset (Fin h)) (hA : A ∈ good) : 3 ≤ A.card :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
  have hsum : (∑ A ∈ S, |collisionWordLocalVertexMoment β x A|) =
      ∑ A ∈ good, |collisionWordLocalVertexMoment β x A| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hnot
    have hbad : ¬ ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
        chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1 := by
      intro hg
      exact hnot (Finset.mem_filter.mpr ⟨hA, hg⟩)
    push Not at hbad
    obtain ⟨z, hz, hc⟩ := hbad
    rw [collisionWordLocalVertexMoment_eq_zero_of_singleton β x A z hz hc, abs_zero]
  have hinj : Set.InjOn f (good : Set (Finset (Fin h))) := by
    intro A hA B hB he
    exact collisionWordLocalPartition_injective_on_noSingleton x A B (hgood A hA) (hgood B hB) he
  have hsub : good.image f ⊆ P := by
    intro I hI
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hbot, hpair⟩ := collisionWordLocalPartition_nonpair_of_three_le x A (hcard A hA) (hgood A hA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbot, hpair,
      collisionWordLocalPartition_isCollisionConfiguration x A⟩
  calc
    _ ≤ ∑ A ∈ S, |collisionWordLocalVertexMoment β x A| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ A ∈ good, |collisionWordLocalVertexMoment β x A| := hsum
    _ = ∑ A ∈ good, |replicaPartitionDisorderMoment β (f A)| := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [collisionWordLocalVertexMoment_eq_partitionMoment β x A (hgood A hA)]
    _ = ∑ I ∈ good.image f, |replicaPartitionDisorderMoment β I| :=
      (Finset.sum_image (f := fun I => |replicaPartitionDisorderMoment β I|) hinj).symm
    _ ≤ ∑ I ∈ P, |replicaPartitionDisorderMoment β I| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro I hI hnot
      exact abs_nonneg _

end Critical2DKPZ.SHF.Moments

end
