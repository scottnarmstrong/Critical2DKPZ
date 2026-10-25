/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationNonpairMoment
public import Critical2DKPZ.SHF.Moments.WordDominationPairOperatorSum
import Mathlib.Tactic

/-! # The two-run partition split in the sharp CCR fourth moment -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- For a single-pair partition, exactly the two selected labels collide. -/
theorem inCollisionBlock_pair_iff {h : ℕ} (α : CollisionPair h) (i : Fin h) :
    InCollisionBlock (pairPartition α) i ↔ i ∈ collisionPairLabels α := by
  constructor
  · rintro ⟨j, hji, hij⟩
    rcases (pairPartition_rel α i j).mp hij with he | ⟨hi, _⟩
    · exact (hji he.symm).elim
    · simpa only [collisionPairLabels, Finset.mem_insert, Finset.mem_singleton] using hi
  · intro hi
    simp only [collisionPairLabels, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨α.1.2, (ne_of_lt α.2).symm, pairPartition_related α⟩
    · exact ⟨α.1.1, ne_of_lt α.2, (pairPartition α).symm' (pairPartition_related α)⟩

/-- Two pair collisions covering all four replicas must be disjoint. This is
the geometry of the only leading two-run contribution. -/
theorem disjoint_pair_labels_of_full_support (α δ : CollisionPair 4)
    (hfull : ∀ i : Fin 4, InCollisionBlock (pairPartition α) i ∨
      InCollisionBlock (pairPartition δ) i) :
    Disjoint (collisionPairLabels α) (collisionPairLabels δ) := by
  classical
  have hcover : collisionPairLabels α ∪ collisionPairLabels δ = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    simpa only [inCollisionBlock_pair_iff] using hfull i
  have hcard (γ : CollisionPair 4) : (collisionPairLabels γ).card = 2 := by
    simp [collisionPairLabels, ne_of_lt γ.2]
  have hc := Finset.card_union_add_card_inter (collisionPairLabels α) (collisionPairLabels δ)
  rw [hcover, hcard α, hcard δ] at hc
  have hi : (collisionPairLabels α ∩ collisionPairLabels δ).card = 0 := by
    simpa using hc
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)

private theorem two_le_card_collisionLabels {h : ℕ}
    (I : ReplicaPartition h) (hI : I ≠ ⊥) :
    2 ≤ (ccr25PartitionCollisionLabels I).card := by
  classical
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  have hne : α.val.1 ≠ α.val.2 := ne_of_lt α.property
  have hfirst : InCollisionBlock I α.val.1 := ⟨α.val.2, hne.symm, hα⟩
  have hsecond : InCollisionBlock I α.val.2 := ⟨α.val.1, hne, I.symm' hα⟩
  have hsubset : ({α.val.1, α.val.2} : Finset (Fin h)) ⊆
      ccr25PartitionCollisionLabels I := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩
    · simp only [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsecond⟩
  have hcard := Finset.card_le_card hsubset
  have hpair : ({α.val.1, α.val.2} : Finset (Fin h)).card = 2 := by
    simp [hne]
  rw [← hpair]
  exact hcard

/-- Two nontrivial Gaussian partition factors gain an extra square-root
variance if at least one partition is not a single pair. -/
theorem two_run_nonpair_disorder_moment_bound {h : ℕ} (β : ℝ)
    (I J : ReplicaPartition h) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hσ : Polymer.sigmaSq β ≤ 1)
    (hnonpair : (∀ α : CollisionPair h, I ≠ pairPartition α) ∨
      (∀ α : CollisionPair h, J ≠ pairPartition α)) :
    |replicaPartitionDisorderMoment β I| * |replicaPartitionDisorderMoment β J| ≤
      (max 1 (ccr25GaussianMomentUniformConstant h)) ^ (2 * h) *
        Polymer.sigmaSq β ^ 2 * Real.sqrt (Polymer.sigmaSq β) := by
  let C := (max 1 (ccr25GaussianMomentUniformConstant h)) ^ h
  let s := Real.sqrt (Polymer.sigmaSq β)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by simpa only [s, Real.sqrt_one] using Real.sqrt_le_sqrt hσ
  have hs2 : s ^ 2 = Polymer.sigmaSq β := Real.sq_sqrt (sigmaSq_nonneg β)
  have hmoment (K : ReplicaPartition h) (hK : K ≠ ⊥) :
      |replicaPartitionDisorderMoment β K| ≤ C * s ^ 2 :=
    (abs_replicaPartitionDisorderMoment_le_supportPower β K hσ).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs hs1
        (two_le_card_collisionLabels K hK)) hC)
  have hnonmoment (K : ReplicaPartition h) (hK : K ≠ ⊥)
      (hp : ∀ α : CollisionPair h, K ≠ pairPartition α) :
      |replicaPartitionDisorderMoment β K| ≤ C * s ^ 3 :=
    (abs_replicaPartitionDisorderMoment_le_supportPower β K hσ).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs hs1
        (SHF.Moments.nonpairPartition_collisionLabels_card_ge_three K hK hp)) hC)
  have hprod : |replicaPartitionDisorderMoment β I| * |replicaPartitionDisorderMoment β J| ≤
      C ^ 2 * (s ^ 2) ^ 2 * s := by
    rcases hnonpair with h | h
    · calc
        _ ≤ (C * s ^ 3) * (C * s ^ 2) :=
          mul_le_mul (hnonmoment I hI h) (hmoment J hJ) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (C * s ^ 2) * (C * s ^ 3) :=
          mul_le_mul (hmoment I hI) (hnonmoment J hJ h) (abs_nonneg _) (by positivity)
        _ = _ := by ring
  rw [hs2] at hprod
  simpa only [C, s, ← pow_mul, mul_comm h 2] using hprod

end Critical2DKPZ.Extensions.GffTangent
