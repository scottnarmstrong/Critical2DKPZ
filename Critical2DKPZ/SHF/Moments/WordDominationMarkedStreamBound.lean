/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.MarkedRunClockIdentities
import Mathlib.Tactic

/-! # Summing first free gaps of marked collision streams

The grouping follows CCR25's first-gap resummation, with the non-pair mark
retained and full support replaced by explicit positive timing bounds.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Marked streams are dominated by their damped key contributions, uniformly
in the first free gap and without requiring every replica to collide. -/
theorem collisionWord_markedGapRunStreamSum_le_keyGapProfileSum
    {h L : ℕ} (β lam : ℝ) (hlam : 0 ≤ lam)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ runs ∈ collisionWordMarkedGapRunStreams h L,
      ccr25GapRunStreamProfileScore β A φ runs) ≤
      ∑ key ∈ collisionWordMarkedGapRunKeys h L,
        Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
          ∑ x ∈ configBox h A L,
            hattedReplicaBoundaryVector L key.firstLabel A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x := by
  classical
  let streams := collisionWordMarkedGapRunStreams h L
  let keys := collisionWordMarkedGapRunKeys h L
  let pairs := streams.image ccr25GapRunStreamCode
  have hcodeInj : Set.InjOn ccr25GapRunStreamCode
      (↑streams : Set (List (CCR25GapRun h))) := by
    intro runs hruns runs' hruns' hcode
    apply ccr25GapRunStreamCode_injective_of_positive
      (collisionWord_markedGapRunStream_ne_nil hruns)
      (collisionWord_markedGapRunStream_ne_nil hruns')
      (collisionWord_markedGapRunStream_gapFacts hruns).1
      (collisionWord_markedGapRunStream_gapFacts hruns').1 hcode
  have hsumImage :
      (∑ runs ∈ streams, ccr25GapRunStreamProfileScore β A φ runs) =
        ∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p := by
    calc
      _ = ∑ runs ∈ streams,
          ccr25GapRunKeyGapProfileScore β A φ
            (ccr25GapRunStreamCode runs) := by
        apply Finset.sum_congr rfl
        intro runs hruns
        have hne := collisionWord_markedGapRunStream_ne_nil hruns
        have hfacts := collisionWord_markedGapRunStream_gapFacts hruns
        cases runs with
        | nil => exact (hne rfl).elim
        | cons first later =>
            have hpos := hfacts.1 first (by simp)
            simp [ccr25GapRunStreamProfileScore,
              ccr25GapRunKeyGapProfileScore, ccr25GapRunStreamCode,
              ccr25GapRunKeyOfD, ccr25GapRunKeyRestore,
              Nat.sub_add_cancel hpos]
      _ = ∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p := by
        dsimp [pairs]
        symm
        exact Finset.sum_image hcodeInj
  have hpairsSubset : pairs ⊆ keys ×ˢ Finset.range L := by
    intro p hp
    obtain ⟨runs, hruns, rfl⟩ := Finset.mem_image.mp hp
    exact (collisionWord_markedGapRunStreamCode_mem hruns).1
  have hpairsBudget : ∀ p ∈ pairs,
      ccr25GapRunKeyGapBudget L p := by
    intro p hp
    obtain ⟨runs, hruns, rfl⟩ := Finset.mem_image.mp hp
    exact (collisionWord_markedGapRunStreamCode_mem hruns).2
  have hsumBudget :
      (∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p) ≤
        ∑ p ∈ keys ×ˢ Finset.range L,
          ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := by
    calc
      _ = ∑ p ∈ pairs,
          ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [ccr25GapRunKeyGapProfileScoreWithBudget,
          hpairsBudget p hp]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hpairsSubset (by
        intro p hp hnot
        exact ccr25GapRunKeyGapProfileScoreWithBudget_nonneg
          β A φ hφ p)
  have hsumProduct :
      (∑ p ∈ keys ×ˢ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p) =
      ∑ key ∈ keys, ∑ n ∈ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ (key, n) := by
    rw [Finset.sum_product]
  have hkeyBound (key : CCR25GapRunKey h) (hkey : key ∈ keys) :
      (∑ n ∈ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ (key, n)) ≤
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x := by
    let N := (Finset.range L).filter
      (fun n => ccr25GapRunKeyGapBudget L (key, n))
    have hN : N ⊆ Finset.range L := Finset.filter_subset _ _
    have hbudget : ∀ n ∈ N,
        n + 1 + key.firstInternalGapsRev.sum +
          (key.laterRuns.map fun run =>
            run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    calc
      _ = ∑ n ∈ N,
          ccr25GapRunKeyGapProfileScore β A φ (key, n) := by
        change (∑ n ∈ Finset.range L,
          if ccr25GapRunKeyGapBudget L (key, n) then
            ccr25GapRunKeyGapProfileScore β A φ (key, n) else 0) = _
        dsimp [N]
        rw [← Finset.sum_filter]
      _ ≤ _ := ccr25GapRunKey_validGapProfileSum_le_of_gapFacts β lam hlam
        A φ hφ key (collisionWord_markedGapRunKey_gapFacts hkey) N hN hbudget
  calc
    _ = ∑ p ∈ pairs, ccr25GapRunKeyGapProfileScore β A φ p := hsumImage
    _ ≤ ∑ p ∈ keys ×ˢ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ p := hsumBudget
    _ = ∑ key ∈ keys, ∑ n ∈ Finset.range L,
        ccr25GapRunKeyGapProfileScoreWithBudget L β A φ (key, n) := hsumProduct
    _ ≤ ∑ key ∈ keys,
        Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
          ∑ x ∈ configBox h A L,
            hattedReplicaBoundaryVector L key.firstLabel A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x :=
      Finset.sum_le_sum fun key hkey => hkeyBound key hkey

end Critical2DKPZ.SHF.Moments

end
