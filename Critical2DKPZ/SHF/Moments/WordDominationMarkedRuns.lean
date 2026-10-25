/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedPaths
public import Critical2DKPZ.SHF.Moments.WordDominationNonpairWordBound
public import Critical2DKPZ.MomentBounds.CCR25GapRunEncoding
import Mathlib.Tactic

/-! # Non-pair marks survive active run compression -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Every nontrivial letter survives removal of inactive times and compression
of repeated consecutive letters. -/
theorem collisionWord_nontrivial_mem_compressed_labels {h n : ℕ}
    (I : Fin n → ReplicaPartition h) (j : Fin n) (hj : I j ≠ ⊥) :
    I j ∈ (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
      CCR25GapRun.label := by
  classical
  rw [ccr25ActiveGapRun_labels_eq_positioned,
    ccr25PositionedCollisionRuns_labels_eq_collisionRunWord]
  have hactive : I j ∈ (List.ofFn I).filter ccr25IsActivePartition := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, by simpa [ccr25IsActivePartition] using hj⟩
  obtain ⟨run, hrun, hlabel⟩ := ccr25EncodeRuns_mem_value hactive
  exact List.mem_map.mpr ⟨run, hrun, hlabel⟩

/-- A marked microscopic history has a non-pair letter in its compressed run
word; no full-support condition on the replicas is required. -/
theorem collisionWord_markedPartitionSequence_compressed_mark {h n : ℕ}
    (I : Fin n → ReplicaPartition h)
    (hI : I ∈ collisionWordMarkedPartitionSequences h n) :
    ∃ J ∈ (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
      CCR25GapRun.label, J ∈ collisionWordNonpairPartitionAlphabet h := by
  classical
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hI).2
  have hnonbot : I j ≠ ⊥ := (Finset.mem_filter.mp hj).2.1
  exact ⟨I j, collisionWord_nontrivial_mem_compressed_labels I j hnonbot, hj⟩

/-- Convert a nonempty adjacent-distinct list to the finite word convention,
without imposing full support on replica labels. -/
theorem collisionWord_validPartitionList_to_word {h : ℕ}
    (word : List (ReplicaPartition h)) (hne : word ≠ [])
    (hpart : ∀ I ∈ word, I ≠ ⊥)
    (hadj : ccr25RunAdjacentDistinct word) :
    ∃ n, ∃ J ∈ collisionWordValidPartitionWords h n, List.ofFn J = word := by
  classical
  let n := word.length - 1
  have hlen : n + 1 = word.length := Nat.sub_add_cancel
    (List.length_pos_iff.mpr hne)
  let J : Fin (n + 1) → ReplicaPartition h := fun j =>
    word.get ⟨j.val, by rw [← hlen]; exact j.isLt⟩
  have hJlist : List.ofFn J = word := by
    calc
      List.ofFn J = List.ofFn (fun j : Fin word.length => word.get j) := by
        rw [List.ofFn_congr hlen J]
        congr 1
      _ = word := List.ofFn_get word
  refine ⟨n, J, ?_, hJlist⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro j
    apply hpart
    rw [← hJlist]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  · intro j
    have hchain := (ccr25RunAdjacentDistinct_iff_isChain word).mp hadj
    have hlt : j.val + 1 < word.length := by
      rw [← hlen]
      exact Nat.succ_lt_succ j.isLt
    simpa [J, List.get] using hchain.getElem j.val hlt

/-- Compression of a marked history produces a valid non-pair operator word. -/
theorem collisionWord_markedPartitionSequence_compressed_word {h L : ℕ}
    (I : Fin L → ReplicaPartition h)
    (hI : I ∈ collisionWordMarkedPartitionSequences h L) :
    ∃ n, ∃ J ∈ collisionWordNonpairPartitionWords h n,
      List.ofFn J =
        (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
          CCR25GapRun.label := by
  classical
  let word := (ccr25CollisionRunWord (List.ofFn I)).map Prod.fst
  have heq : (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
      CCR25GapRun.label = word := by
    rw [ccr25ActiveGapRun_labels_eq_positioned,
      ccr25PositionedCollisionRuns_labels_eq_collisionRunWord]
  obtain ⟨K, hK, hbad⟩ := collisionWord_markedPartitionSequence_compressed_mark I hI
  rw [heq] at hK
  have hne : word ≠ [] := by
    intro he
    simp [he] at hK
  have hshape := ccr25CollisionRunWord_admissibleShape (List.ofFn I)
  obtain ⟨n, J, hJ, hlist⟩ := collisionWord_validPartitionList_to_word word hne
    (by
      intro K hK
      obtain ⟨run, hrun, rfl⟩ := List.mem_map.mp hK
      exact hshape.1 run hrun) hshape.2
  refine ⟨n, J, ?_, hlist.trans heq.symm⟩
  apply Finset.mem_filter.mpr
  refine ⟨hJ, ?_⟩
  rw [← hlist] at hK
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hK
  refine ⟨j, ?_⟩
  rw [hj]
  exact (Finset.mem_filter.mp hbad).2.2

end Critical2DKPZ.SHF.Moments

end
