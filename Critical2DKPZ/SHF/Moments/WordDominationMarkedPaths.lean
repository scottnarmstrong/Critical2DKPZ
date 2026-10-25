/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPartitionAlphabet
import Mathlib.Tactic

/-! # Domination of the remainder by marked microscopic partition histories -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- Microscopic partition histories containing at least one non-pair event.
The index `j` represents the physical time `j + 1`, including the last slice. -/
def collisionWordMarkedPartitionSequences (h n : ℕ) : Finset (Fin n → ReplicaPartition h) :=
  Finset.univ.filter (fun I => ∃ j, I j ∈ collisionWordNonpairPartitionAlphabet h)

private theorem collisionWord_sum_marked_products (h n : ℕ)
    (good : Finset (ReplicaPartition h)) (w : Fin n → ReplicaPartition h → ℝ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n → ReplicaPartition h)).filter (fun I => ∃ j, I j ∉ good),
      ∏ j, w j (I j)) =
      (∏ j, ∑ a : ReplicaPartition h, w j a) - ∏ j, ∑ a ∈ good, w j a := by
  classical
  have hgoodSet : (Finset.univ : Finset (Fin n → ReplicaPartition h)).filter (fun I => ∀ j, I j ∈ good) =
      Fintype.piFinset (fun _ : Fin n => good) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  have hgood :
      (∑ I ∈ (Finset.univ : Finset (Fin n → ReplicaPartition h)).filter (fun I => ∀ j, I j ∈ good),
        ∏ j, w j (I j)) = ∏ j, ∑ a ∈ good, w j a := by
    rw [hgoodSet]
    exact (Finset.prod_univ_sum (fun _ : Fin n => good) w).symm
  have hbadSet : (Finset.univ : Finset (Fin n → ReplicaPartition h)).filter (fun I => ¬ ∀ j, I j ∈ good) =
      Finset.univ.filter (fun I => ∃ j, I j ∉ good) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n → ReplicaPartition h)) (fun I => ∀ j, I j ∈ good)
    (f := fun I => ∏ j, w j (I j))
  rw [hgood, hbadSet, ← Fintype.prod_sum w] at hsplit
  linarith only [hsplit]

/-- Dominate a complete path's local-potential defect by histories carrying
a non-pair partition mark. All other letters retain the usual absolute CCR
weights. -/
theorem collisionWord_pathDefect_le_markedPartitionSequences (β : ℝ) {n h : ℕ}
    (z : Fin n → LatticeConfiguration h) :
    ((∏ j : Fin n, Real.exp (β ^ 2 * replicaPotential (z j))) -
      ∏ j : Fin n, collisionWordLocalPairPotential β (z j)) ≤
      ∑ I ∈ collisionWordMarkedPartitionSequences h n,
        ∏ j : Fin n, collisionWordLocalAbsPartitionWeight β (z j) (I j) := by
  classical
  let w : Fin n → ReplicaPartition h → ℝ := fun j I => collisionWordLocalAbsPartitionWeight β (z j) I
  have hprod : (∏ j : Fin n, Real.exp (β ^ 2 * replicaPotential (z j))) ≤
      ∏ j : Fin n, ∑ I : ReplicaPartition h, w j I := by
    apply Finset.prod_le_prod₀
    · intro j hj
      exact Real.exp_nonneg _
    · intro j hj
      exact exp_replicaPotential_le_sum_partitionAlphabet β (z j)
  have hmarked : collisionWordMarkedPartitionSequences h n =
      Finset.univ.filter (fun I : Fin n → ReplicaPartition h =>
        ∃ j, I j ∉ collisionWordPairPartitionAlphabet h) := by
    ext I
    simp only [collisionWordMarkedPartitionSequences, Finset.mem_filter,
      Finset.mem_univ, true_and, mem_collisionWordNonpairPartitionAlphabet_iff]
  have hid :
      (∑ I ∈ collisionWordMarkedPartitionSequences h n, ∏ j : Fin n, w j (I j)) =
        (∏ j : Fin n, ∑ I : ReplicaPartition h, w j I) -
          ∏ j : Fin n, collisionWordLocalPairPotential β (z j) := by
    rw [hmarked]
    have hid' := collisionWord_sum_marked_products h n (collisionWordPairPartitionAlphabet h) w
    have hgoodProd : (∏ j : Fin n,
        ∑ I ∈ collisionWordPairPartitionAlphabet h, w j I) =
        ∏ j : Fin n, collisionWordLocalPairPotential β (z j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact sum_pairAlphabet_localAbsPartitionWeight β (z j)
    rw [hgoodProd] at hid'
    exact hid'
  calc
    _ ≤ (∏ j : Fin n, ∑ I : ReplicaPartition h, w j I) -
        ∏ j : Fin n, collisionWordLocalPairPotential β (z j) := sub_le_sub_right hprod _
    _ = _ := hid.symm

/-- The exact collision-edge remainder is bounded by a finite independent-
walk path sum of absolute partition histories containing a non-pair event. -/
theorem nonpairCollisionRemainder_le_markedPartitionPaths
    (β : ℝ) (n h : ℕ) (x y : LatticeConfiguration h) :
    nonpairCollisionRemainder β n h x y ≤
      ∑ s : Fin h → Fin n → Fin 4, ((4 : ℝ)⁻¹ ^ n) ^ h *
        (∑ I ∈ collisionWordMarkedPartitionSequences h n,
          ∏ j : Fin n, collisionWordLocalAbsPartitionWeight β
            (fun i => walkPosition (x i) (s i) (j.val + 1)) (I j)) *
        ∏ i, if walkPosition (x i) (s i) n = y i then (1 : ℝ) else 0 := by
  rw [nonpairCollisionRemainder_eq_pathDefect]
  apply Finset.sum_le_sum
  intro s hs
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · exact collisionWord_pathDefect_le_markedPartitionSequences β
        (fun j i => walkPosition (x i) (s i) (j.val + 1))
    · positivity
  · apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> norm_num

end Critical2DKPZ.SHF.Moments

end
