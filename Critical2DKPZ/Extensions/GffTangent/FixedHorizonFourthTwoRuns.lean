/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonLeadingPairWord
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthOperatorBounds
import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
import Mathlib.Tactic

/-! # Leading and negligible contributions of the two-run fourth moment -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The two-run CCR contribution is bounded by the sharp disjoint-pair term
and a remainder with an extra square-root variance. The fixed combinatorial
constant is independent of the profile, coupling and window length. -/
theorem ccr25_fourth_two_runs_le
    (β : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4))
    (b : FourthWordOperatorBounds s L β
      (fun I => hattedReplicaBoundaryVector L I S φ) collisionIndicator)
    (hσ : Polymer.sigmaSq β ≤ 1) :
    ccr25GaussianFiniteWordRun s L 0 β
      (fun I => hattedReplicaBoundaryVector L I S φ) collisionIndicator 1 ≤
      (2 : ℝ) ^ 32 *
        (Polymer.sigmaSq β ^ 2 * (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 *
          (B * ∑ y ∈ S, φ y) ^ 2 +
        (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 8 *
          Polymer.sigmaSq β ^ 2 * Real.sqrt (Polymer.sigmaSq β) *
            (b.leftCost * b.rightCost * b.interactionCost ^ 2 * b.freeCost)) := by
  classical
  let leading := Polymer.sigmaSq β ^ 2 * (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 *
    (B * ∑ y ∈ S, φ y) ^ 2
  let moment := (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 8 *
    Polymer.sigmaSq β ^ 2 * Real.sqrt (Polymer.sigmaSq β)
  let operator := b.leftCost * b.rightCost * b.interactionCost ^ 2 * b.freeCost
  have hleading : 0 ≤ leading := by dsimp [leading]; positivity
  have hmoment : 0 ≤ moment := by dsimp [moment]; positivity
  have hoperator : 0 ≤ operator := mul_nonneg
    (mul_nonneg (mul_nonneg b.leftCost_nonneg b.rightCost_nonneg) (sq_nonneg _)) b.freeCost_nonneg
  have hword (I : Fin 2 → ReplicaPartition 4) (hI : I ∈ ccr25AdmissibleWords 4 1) :
      (∏ j : Fin 2, |replicaPartitionDisorderMoment β (I j)|) *
        ccr25FiniteWordPairing s L 0 β I
          (fun J => hattedReplicaBoundaryVector L J S φ) collisionIndicator ≤
      leading + moment * operator := by
    have hIadm : ccr25AdmissibleWord I := (Finset.mem_filter.mp hI).2
    by_cases hpairs : (∃ α : CollisionPair 4, I 0 = pairPartition α) ∧
        (∃ δ : CollisionPair 4, I 1 = pairPartition δ)
    · obtain ⟨⟨α, hI0⟩, ⟨δ, hI1⟩⟩ := hpairs
      have hfull (i : Fin 4) : InCollisionBlock (pairPartition α) i ∨
          InCollisionBlock (pairPartition δ) i := by
        obtain ⟨j, hj⟩ := hIadm.2.2 i
        fin_cases j
        · exact Or.inl (hI0 ▸ hj)
        · exact Or.inr (hI1 ▸ hj)
      have hd := disjoint_pair_labels_of_full_support α δ hfull
      exact (weighted_ccr25_disjoint_pair_word_le α δ hd β L S φ hB hφ hφB s I hI0 hI1).trans
        (le_add_of_nonneg_right (mul_nonneg hmoment hoperator))
    · have hn : (∀ α : CollisionPair 4, I 0 ≠ pairPartition α) ∨
          (∀ δ : CollisionPair 4, I 1 ≠ pairPartition δ) := by
        by_cases h0 : ∃ α : CollisionPair 4, I 0 = pairPartition α
        · right
          intro δ hδ
          exact hpairs ⟨h0, δ, hδ⟩
        · left
          exact fun α hα => h0 ⟨α, hα⟩
      have hcoef : (∏ j : Fin 2, |replicaPartitionDisorderMoment β (I j)|) ≤ moment := by
        rw [Fin.prod_univ_two]
        exact two_run_nonpair_disorder_moment_bound β (I 0) (I 1) (hIadm.1 0) (hIadm.1 1) hσ hn
      have hop : ccr25FiniteWordPairing s L 0 β I
          (fun J => hattedReplicaBoundaryVector L J S φ) collisionIndicator ≤ operator := by
        simpa only [Nat.reduceAdd, pow_one] using b.word_le I hIadm
      have hnword := ccr25FiniteWordPairing_nonneg s L 0 β I
        (fun J => hattedReplicaBoundaryVector L J S φ) collisionIndicator b.left_nonneg b.right_nonneg
      exact (mul_le_mul hcoef hop hnword hmoment).trans (le_add_of_nonneg_left hleading)
  have hcard : ((ccr25AdmissibleWords 4 1).card : ℝ) ≤ (2 : ℝ) ^ 32 := by
    have hn : (ccr25AdmissibleWords 4 1).card ≤ 2 ^ 32 := by
      simpa using ccr25_admissibleWords_card_le_explicit (h := 4) (n := 1)
    exact_mod_cast hn
  calc
    _ ≤ ∑ _I ∈ ccr25AdmissibleWords 4 1, (leading + moment * operator) :=
      Finset.sum_le_sum hword
    _ = ((ccr25AdmissibleWords 4 1).card : ℝ) * (leading + moment * operator) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (add_nonneg hleading (mul_nonneg hmoment hoperator))

end Critical2DKPZ.Extensions.GffTangent
