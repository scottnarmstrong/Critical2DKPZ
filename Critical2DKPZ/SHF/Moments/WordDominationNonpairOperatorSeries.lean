/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationNonpairWordBound
public import Critical2DKPZ.MomentBounds.CCR25GeometricSeries
import Mathlib.Tactic

/-! # The marked operator series retains its non-pair small factor -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose

/-- Summing every marked operator word retains the relative non-pair small
factor; the only denominator is the fixed alphabet contraction gap. -/
theorem collisionWord_nonpair_word_operator_series_bound {h : ℕ}
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
          cQ * finiteLpNorm s q f)
    (hsmall : (cU * σ * (2 ^ (h * h) : ℝ)) * cQ < 1) :
    (∑ n ∈ Finset.range L, ∑ I ∈ collisionWordNonpairPartitionWords h n,
      (∏ j : Fin (n + 1), |mom (I j)|) *
        ccr25FiniteWordPairing s L lam β I u v) ≤
      (δ * left * right) * (cU * σ * (2 ^ (h * h) : ℝ)) /
        (1 - (cU * σ * (2 ^ (h * h) : ℝ)) * cQ) := by
  classical
  let F := fun n : ℕ => ∑ I ∈ collisionWordNonpairPartitionWords h n,
    (∏ j : Fin (n + 1), |mom (I j)|) *
      ccr25FiniteWordPairing s L lam β I u v
  have hF0 : ∀ n, 0 ≤ F n := by
    intro n
    apply Finset.sum_nonneg
    intro I hI
    exact mul_nonneg (Finset.prod_nonneg (fun j hj => abs_nonneg _))
      (ccr25FiniteWordPairing_nonneg s L lam β I u v hu hv)
  have hF (n : ℕ) : F n ≤ (δ * left * right) *
      (cU * σ * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n :=
    collisionWord_nonpair_word_operator_bound s L lam β W hW hpq u v hu hv
      mom σ δ cU cQ left right hσ hδ hMom hBad hcU hcQ hleft hright
      hleft_bound hright_bound hU_bound hQ_bound
  obtain ⟨hsum, hbound⟩ := ccr25_tsum_le_geometric_run_sum
    (cU * σ * (2 ^ (h * h) : ℝ)) cQ (δ * left * right)
    (by positivity) hcQ hsmall hF0 hF
  exact (hsum.sum_le_tsum (Finset.range L) (fun n hn => hF0 n)).trans hbound

end Critical2DKPZ.SHF.Moments

end
