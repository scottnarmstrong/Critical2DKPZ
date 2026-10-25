/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedReindex
public import Critical2DKPZ.MomentBounds.CCR25PartitionSumWordRuns
import Mathlib.Tactic

/-! # Timing and word facts for marked CCR run keys -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Marked run keys omit only the first free gap of an exact run stream. -/
def collisionWordMarkedGapRunKeys (h L : ℕ) : Finset (CCR25GapRunKey h) := by
  classical
  exact (collisionWordMarkedGapRunStreams h L).image ccr25GapRunKeyOfD

/-- A non-pair mark excludes the empty run stream. -/
theorem collisionWord_markedGapRunStream_ne_nil {h L : ℕ}
    {runs : List (CCR25GapRun h)} (hruns : runs ∈ collisionWordMarkedGapRunStreams h L) :
    runs ≠ [] := by
  obtain ⟨J, hJ, _⟩ := collisionWord_markedGapRunStream_mark hruns
  intro he
  simp [he] at hJ

/-- Positive bounded timing facts for marked keys, without full support. -/
theorem collisionWord_markedGapRunKey_gapFacts {h L : ℕ}
    {key : CCR25GapRunKey h} (hkey : key ∈ collisionWordMarkedGapRunKeys h L) :
    (∀ run ∈ key.laterRuns, 1 ≤ run.firstGap) ∧
      (∀ run ∈ key.laterRuns, ∀ d ∈ run.internalGapsRev, 1 ≤ d) ∧
      (∀ d ∈ key.firstInternalGapsRev, 1 ≤ d) ∧
      key.firstInternalGapsRev.sum +
        (key.laterRuns.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
  classical
  obtain ⟨runs, hruns, hkeyEq⟩ := Finset.mem_image.mp hkey
  obtain ⟨first, later, rfl⟩ :=
    List.exists_cons_of_ne_nil (collisionWord_markedGapRunStream_ne_nil hruns)
  have hfacts := collisionWord_markedGapRunStream_gapFacts hruns
  have hsumKey : first.internalGapsRev.sum +
      (later.map fun run => run.firstGap + run.internalGapsRev.sum).sum ≤ L := by
    have hsum := hfacts.2.2
    simp only [List.map_cons, List.sum_cons] at hsum
    omega
  simp only [ccr25GapRunKeyOfD] at hkeyEq
  rcases hkeyEq with ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro run hr
    exact hfacts.1 run (by simp [hr])
  · intro run hr d hd
    exact hfacts.2.1 run (by simp [hr]) d hd
  · intro d hd
    exact hfacts.2.1 first (by simp) d hd
  · simpa [ccr25GapRunKeyOfD] using hsumKey

/-- The stream code belongs to the marked key set and satisfies the exact
first-gap budget. -/
theorem collisionWord_markedGapRunStreamCode_mem {h L : ℕ}
    {runs : List (CCR25GapRun h)} (hruns : runs ∈ collisionWordMarkedGapRunStreams h L) :
    ccr25GapRunStreamCode runs ∈ collisionWordMarkedGapRunKeys h L ×ˢ Finset.range L ∧
      ccr25GapRunKeyGapBudget L (ccr25GapRunStreamCode runs) := by
  classical
  cases runs with
  | nil => exact (collisionWord_markedGapRunStream_ne_nil hruns rfl).elim
  | cons first later =>
    have hfacts := collisionWord_markedGapRunStream_gapFacts hruns
    simp only [List.map_cons, List.sum_cons] at hfacts
    have hfirstPos := hfacts.1 first (by simp)
    have htailCost := hfacts.2.2
    have hkeyMem : ccr25GapRunKeyOfD (first :: later) ∈
        collisionWordMarkedGapRunKeys h L :=
      Finset.mem_image.mpr ⟨first :: later, hruns, rfl⟩
    constructor
    · apply Finset.mem_product.mpr
      refine ⟨hkeyMem, ?_⟩
      simp only [ccr25GapRunStreamCode, Finset.mem_range]
      omega
    · simp only [ccr25GapRunStreamCode, ccr25GapRunKeyOfD,
        ccr25GapRunKeyGapBudget]
      omega

/-- A marked key reads a non-pair valid word, and has fewer than L later runs. -/
theorem collisionWord_markedGapRunKey_word_mem {h L : ℕ}
    {key : CCR25GapRunKey h} (hkey : key ∈ collisionWordMarkedGapRunKeys h L) :
    ccr25GapRunKeyWord key ∈ collisionWordNonpairPartitionWords h key.laterRuns.length ∧
      key.laterRuns.length < L := by
  classical
  obtain ⟨runs, hruns, hkeyEq⟩ := Finset.mem_image.mp hkey
  have hne := collisionWord_markedGapRunStream_ne_nil hruns
  have hfacts := collisionWord_markedGapRunStream_gapFacts hruns
  have hlength : runs.length ≤ L := by
    have hle : ∀ rs : List (CCR25GapRun h), (∀ r ∈ rs, 1 ≤ r.firstGap) →
        rs.length ≤ (rs.map fun r => r.firstGap + r.internalGapsRev.sum).sum := by
      intro rs
      induction rs with
      | nil => simp
      | cons r rs ih =>
        intro hpos
        have hr := hpos r (by simp)
        have ht := ih (fun r hr => hpos r (by simp [hr]))
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
    exact (hle runs hfacts.1).trans hfacts.2.2
  have hkeyLabels := ccr25GapRunKeyLabels_eq_runLabels_ofD hne
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hruns
  obtain ⟨n, J, hJ, hlist⟩ := collisionWord_markedPartitionSequence_compressed_word I hI
  have hlabels : List.ofFn J = ccr25GapRunKeyLabels key := by
    rw [← hkeyEq]
    exact hlist.trans hkeyLabels.symm
  have hnum : n = key.laterRuns.length := by
    have := congrArg List.length hlabels
    simp only [List.length_ofFn, ccr25GapRunKeyLabels_length] at this
    omega
  subst n
  have hword : J = ccr25GapRunKeyWord key := by
    apply List.ofFn_inj.mp
    rw [ccr25GapRunKeyWord_ofFn]
    exact hlabels
  refine ⟨hword ▸ hJ, ?_⟩
  have hlen : key.laterRuns.length + 1 =
      (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).length := by
    have he' := congrArg List.length hkeyLabels
    rw [hkeyEq] at he'
    simpa only [ccr25GapRunKeyLabels_length, List.length_map] using he'
  omega

end Critical2DKPZ.SHF.Moments

end
