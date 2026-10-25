/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationLocalDomination
public import Critical2DKPZ.SHF.Moments.WordDominationPairStratumFree
public import Critical2DKPZ.SHF.Moments.WordDominationPairOperatorSum
import Mathlib.Tactic

/-! # The local partition alphabet and its marked complement -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- The free letter and the single-pair letters of the partition alphabet. -/
def collisionWordPairPartitionAlphabet (h : ℕ) : Finset (ReplicaPartition h) :=
  insert ⊥ (Finset.univ.image pairPartition)

/-- The non-pair letters of the partition alphabet. -/
def collisionWordNonpairPartitionAlphabet (h : ℕ) : Finset (ReplicaPartition h) :=
  Finset.univ.filter (fun I => I ≠ ⊥ ∧ ∀ α : CollisionPair h, I ≠ pairPartition α)

/-- Absolute local partition weight; bottom represents the unit free term. -/
def collisionWordLocalAbsPartitionWeight (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (I : ReplicaPartition h) : ℝ :=
  if I = ⊥ then 1 else
    if IsCollisionConfiguration I x then |replicaPartitionDisorderMoment β I| else 0

/-- Every local absolute partition weight is nonnegative. -/
theorem collisionWordLocalAbsPartitionWeight_nonneg (β : ℝ) {h : ℕ}
    (x : Fin h → Site) (I : ReplicaPartition h) :
    0 ≤ collisionWordLocalAbsPartitionWeight β x I := by
  unfold collisionWordLocalAbsPartitionWeight
  split_ifs <;> positivity

/-- The marked alphabet is precisely the complement of the free/pair alphabet. -/
theorem mem_collisionWordNonpairPartitionAlphabet_iff {h : ℕ} (I : ReplicaPartition h) :
    I ∈ collisionWordNonpairPartitionAlphabet h ↔ I ∉ collisionWordPairPartitionAlphabet h := by
  simp only [collisionWordNonpairPartitionAlphabet, collisionWordPairPartitionAlphabet,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
  aesop

/-- Pair partition letters reproduce exactly the pair-simple local potential. -/
theorem sum_pairAlphabet_localAbsPartitionWeight (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    (∑ I ∈ collisionWordPairPartitionAlphabet h, collisionWordLocalAbsPartitionWeight β x I) =
      collisionWordLocalPairPotential β x := by
  classical
  have hbot : (⊥ : ReplicaPartition h) ∉ Finset.univ.image pairPartition := by
    intro hm
    obtain ⟨α, _, he⟩ := Finset.mem_image.mp hm
    exact pairPartition_ne_bot α he
  have hpair (α : CollisionPair h) :
      collisionWordLocalAbsPartitionWeight β x (pairPartition α) =
        sigmaSq β * if x α.1.1 = x α.1.2 then (1 : ℝ) else 0 := by
    have hσ : 0 ≤ sigmaSq β := sigmaSq_nonneg β
    rw [collisionWordLocalAbsPartitionWeight, ite_eq_right (pairPartition_ne_bot α),
      collisionWord_pairPartition_collision_iff, pairPartition_disorderMoment_eq_sigmaSq,
      abs_of_nonneg hσ]
    split_ifs <;> ring
  have hbottom : collisionWordLocalAbsPartitionWeight β x (⊥ : ReplicaPartition h) = 1 := by
    simp [collisionWordLocalAbsPartitionWeight]
  rw [collisionWordPairPartitionAlphabet, Finset.sum_insert hbot,
    Finset.sum_image pairPartition_injective.injOn, hbottom]
  simp only [hpair, collisionWordLocalPairPotential, Finset.mul_sum]

/-- Summing the marked local alphabet gives the absolute non-pair moment
majorant on its exact CCR strata. -/
theorem sum_nonpairAlphabet_localAbsPartitionWeight (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    (∑ I ∈ collisionWordNonpairPartitionAlphabet h, collisionWordLocalAbsPartitionWeight β x I) =
      ∑ I ∈ (Finset.univ : Finset (ReplicaPartition h)).filter
        (fun I => I ≠ ⊥ ∧ (∀ α : CollisionPair h, I ≠ pairPartition α) ∧
          IsCollisionConfiguration I x), |replicaPartitionDisorderMoment β I| := by
  rw [collisionWordNonpairPartitionAlphabet, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hbot : I = ⊥ <;>
    by_cases hpair : ∀ α : CollisionPair h, I ≠ pairPartition α <;>
      by_cases hconfig : IsCollisionConfiguration I x <;>
        simp [collisionWordLocalAbsPartitionWeight, hbot, hpair, hconfig]

/-- The full Gaussian local potential is bounded by the sum over the finite
absolute partition alphabet. -/
theorem exp_replicaPotential_le_sum_partitionAlphabet (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    Real.exp (β ^ 2 * replicaPotential x) ≤
      ∑ I : ReplicaPartition h, collisionWordLocalAbsPartitionWeight β x I := by
  classical
  have hdisj : Disjoint (collisionWordPairPartitionAlphabet h) (collisionWordNonpairPartitionAlphabet h) := by
    apply Finset.disjoint_left.mpr
    intro I hI hbad
    exact (mem_collisionWordNonpairPartitionAlphabet_iff I).mp hbad hI
  have hunion : collisionWordPairPartitionAlphabet h ∪ collisionWordNonpairPartitionAlphabet h = Finset.univ := by
    ext I
    simp only [Finset.mem_union, mem_collisionWordNonpairPartitionAlphabet_iff, Finset.mem_univ]
    tauto
  rw [← hunion, Finset.sum_union hdisj, sum_pairAlphabet_localAbsPartitionWeight,
    sum_nonpairAlphabet_localAbsPartitionWeight]
  exact exp_replicaPotential_le_pair_add_nonpairMoments β x

end Critical2DKPZ.SHF.Moments

end
