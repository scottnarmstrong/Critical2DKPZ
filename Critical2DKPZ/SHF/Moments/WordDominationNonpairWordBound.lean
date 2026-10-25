/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationValidWords
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
import Mathlib.Tactic

/-! # The small factor retained by words containing a non-pair partition -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

/-- Nontrivial adjacent-distinct partition words containing at least one non-pair letter. -/
def collisionWordNonpairPartitionWords (h n : ℕ) :
    Finset (Fin (n + 1) → ReplicaPartition h) := by
  classical
  exact (collisionWordValidPartitionWords h n).filter
    (fun I => ∃ j, ∀ α : CollisionPair h, I j ≠ pairPartition α)

/-- One non-pair letter retains its relative smallness in the entire
partition-word moment product. -/
theorem collisionWord_nonpairWord_momentWeight_le {h n : ℕ}
    (mom : ReplicaPartition h → ℝ) (σ δ : ℝ) (hσ : 0 ≤ σ)
    (hMom : ∀ I : ReplicaPartition h, I ≠ ⊥ → |mom I| ≤ σ)
    (hBad : ∀ I : ReplicaPartition h, I ≠ ⊥ →
      (∀ α : CollisionPair h, I ≠ pairPartition α) → |mom I| ≤ δ * σ)
    (I : Fin (n + 1) → ReplicaPartition h)
    (hI : I ∈ collisionWordNonpairPartitionWords h n) :
    (∏ j : Fin (n + 1), |mom (I j)|) ≤ δ * σ ^ (n + 1) := by
  classical
  obtain ⟨hIadm, j, hj⟩ := Finset.mem_filter.mp hI
  have hpart : ∀ j, I j ≠ ⊥ := (Finset.mem_filter.mp hIadm).2.1
  have hrest : (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
      |mom (I i)|) ≤ σ ^ n := by
    calc
      _ ≤ ∏ _i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j, σ :=
        Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hMom _ (hpart i))
      _ = _ := by simp
  calc
    _ = (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          |mom (I i)|) * |mom (I j)| :=
      (Finset.prod_erase_mul Finset.univ (fun i => |mom (I i)|) (Finset.mem_univ j)).symm
    _ ≤ σ ^ n * (δ * σ) :=
      mul_le_mul hrest (hBad _ (hpart j) hj) (abs_nonneg _) (pow_nonneg hσ n)
    _ = _ := by rw [pow_succ]; ring

/-- The finite CCR operator estimate preserves the extra small factor from
a non-pair letter. The alphabet bound is elementary and independent of the
word length. -/
theorem collisionWord_nonpair_word_operator_bound {h n : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (hu : ∀ I x, 0 ≤ u I x) (hv : ∀ I x, 0 ≤ v I x)
    (mom : ReplicaPartition h → ℝ) (σ δ cU cQ left right : ℝ)
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hMom : ∀ I : ReplicaPartition h, I ≠ ⊥ → |mom I| ≤ σ)
    (hBad : ∀ I : ReplicaPartition h, I ≠ ⊥ →
      (∀ α : CollisionPair h, I ≠ pairPartition α) → |mom I| ≤ δ * σ)
    (hcU : 0 ≤ cU) (hcQ : 0 ≤ cQ) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleft_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left)
    (hright_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right)
    (hU_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W (ccr25LabelKernel L lam β (.interacting I))) f) ≤
          cU * finiteLpNorm s q f)
    (hQ_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W (ccr25LabelKernel L lam β (.free I J))) f) ≤
          cQ * finiteLpNorm s q f) :
    (∑ I ∈ collisionWordNonpairPartitionWords h n,
      (∏ j : Fin (n + 1), |mom (I j)|) *
        ccr25FiniteWordPairing s L lam β I u v) ≤
      δ * left * right * (cU * σ * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n := by
  classical
  let K := fun I : Fin (n + 1) → ReplicaPartition h =>
    ccr25FiniteWordPairing s L lam β I u v
  have hK (I : Fin (n + 1) → ReplicaPartition h) : 0 ≤ K I :=
    ccr25FiniteWordPairing_nonneg s L lam β I u v hu hv
  have hsubset : collisionWordNonpairPartitionWords h n ⊆ collisionWordValidPartitionWords h n :=
    Finset.filter_subset _ _
  have hfull := collisionWord_valid_word_constantMoment_operator_bound (h := h) (n := n)
    s L lam β W hW hpq u v σ cU cQ left right hσ
    hcU hcQ hleft hright hleft_bound hright_bound hU_bound hQ_bound
  calc
    _ ≤ ∑ I ∈ collisionWordNonpairPartitionWords h n, (δ * σ ^ (n + 1)) * K I := by
      apply Finset.sum_le_sum
      intro I hI
      exact mul_le_mul_of_nonneg_right
        (collisionWord_nonpairWord_momentWeight_le mom σ δ hσ hMom hBad I hI) (hK I)
    _ = δ * ∑ I ∈ collisionWordNonpairPartitionWords h n, σ ^ (n + 1) * K I := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ ≤ δ * ∑ I ∈ collisionWordValidPartitionWords h n, σ ^ (n + 1) * K I := by
      apply mul_le_mul_of_nonneg_left _ hδ
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro I hI hnot
      exact mul_nonneg (pow_nonneg hσ _) (hK I)
    _ ≤ δ * (left * right * (cU * σ * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      simpa only [K] using hfull
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments

end
