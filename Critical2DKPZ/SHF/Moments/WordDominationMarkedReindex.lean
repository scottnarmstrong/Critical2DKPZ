/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedRuns
public import Critical2DKPZ.MomentBounds.CCR25ActiveMomentExpansion
public import Critical2DKPZ.MomentBounds.CCR25WordRunAssembly
import Mathlib.Tactic

/-! # Exact reindexing of marked partition histories by their run streams -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- The compressed run streams of histories containing a non-pair event. -/
def collisionWordMarkedGapRunStreams (h L : ℕ) : Finset (List (CCR25GapRun h)) := by
  classical
  exact (collisionWordMarkedPartitionSequences h L).image fun I =>
    ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))

/-- Moment-weighted partition paths factor exactly into maximal runs, even
when the untouched replicas do not belong to any collision block. -/
theorem collisionWord_partitionMomentPath_eq_gapRunPath {h L : ℕ}
    (β : ℝ) (I : Fin L → ReplicaPartition h) (x : LatticeConfiguration h) :
    (∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) *
      replicaPathWeight (List.ofFn I) x =
    ccr25GapRunPathWeight β ⊥
      (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))) x := by
  rw [absMoment_mul_replicaPathWeight_eq_activeMomentKernelPathWeight,
    ccr25ActiveMomentKernelPathWeight_eq_runFactored,
    ccr25ActiveRunFactoredPathWeight_eq_gapRunPathWeight]

/-- Encoding marked histories as run streams preserves the weighted sum and permits free spectator labels. -/
theorem collisionWord_markedPartitionSum_eq_gapRunSum {h L : ℕ}
    (β : ℝ) (A : Finset Site) (φ : Site → ℝ) :
    (∑ I ∈ collisionWordMarkedPartitionSequences h L,
      ∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (x i)) *
          ((∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) *
            replicaPathWeight (List.ofFn I) x)) =
    ∑ runs ∈ collisionWordMarkedGapRunStreams h L,
      ∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (x i)) * ccr25GapRunPathWeight β ⊥ runs x := by
  classical
  rw [collisionWordMarkedGapRunStreams, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro x hx
    rw [collisionWord_partitionMomentPath_eq_gapRunPath]
  · intro I hI J hJ heq
    apply ccr25ActiveGapEncodeFrom_zero_ofFn_injective
    have hExpand := congrArg ccr25GapRunExpand heq
    simpa only [ccr25GapRunExpand_encode] using hExpand

/-- Every marked run stream is nonempty and carries a non-pair letter. -/
theorem collisionWord_markedGapRunStream_mark {h L : ℕ}
    {runs : List (CCR25GapRun h)} (hruns : runs ∈ collisionWordMarkedGapRunStreams h L) :
    ∃ J ∈ runs.map CCR25GapRun.label, J ∈ collisionWordNonpairPartitionAlphabet h := by
  classical
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hruns
  exact collisionWord_markedPartitionSequence_compressed_mark I hI

/-- Marked streams have positive entry and internal gaps, with total elapsed
time at most the microscopic horizon. -/
theorem collisionWord_markedGapRunStream_gapFacts {h L : ℕ}
    {runs : List (CCR25GapRun h)} (hruns : runs ∈ collisionWordMarkedGapRunStreams h L) :
    (∀ run ∈ runs, 1 ≤ run.firstGap) ∧
      (∀ run ∈ runs, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
      (runs.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
  classical
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hruns
  have hpos := ccr25GapRunEncode_gap_pos
    (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))
    (fun e he => ccr25ActiveGapEncodeFrom_gap_pos 0 (List.ofFn I) he)
  refine ⟨?_, ?_, ?_⟩
  · intro run hr
    exact hpos run hr run.firstGap (by simp)
  · intro run hr d hd
    exact hpos run hr d (by simp [hd])
  · rw [← ccr25GapRunExpand_gapSum, ccr25GapRunExpand_encode]
    simpa using ccr25ActiveGapEncodeFrom_sum_le (gap := 0) (List.ofFn I)

end Critical2DKPZ.SHF.Moments

end
