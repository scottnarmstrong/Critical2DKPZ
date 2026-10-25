/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedStreamBound
import Mathlib.Tactic

/-! # Resumming marked microscopic histories into non-pair operator words -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Length-indexed valid non-pair words below the microscopic horizon. -/
def collisionWordNonpairWordIndices (h L : ℕ) : Finset (CCR25PartitionWordIndex h) := by
  classical
  exact (Finset.range L).sigma (collisionWordNonpairPartitionWords h)

/-- Resumming positive timed keys in each marked word fiber retains the mark. -/
theorem collisionWord_markedGapRunKeySum_le_wordIndexSum
    {h L : ℕ} (lam β : ℝ)
    (A : Finset Site) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ key ∈ collisionWordMarkedGapRunKeys h L,
      Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
        ∑ x ∈ configBox h A L,
          hattedReplicaBoundaryVector L key.firstLabel A φ x *
            ccr25GapRunKeyDampedTail L lam β A key x) ≤
      Real.exp (lam * L) *
        ∑ idx ∈ collisionWordNonpairWordIndices h L,
          ccr25WordIndexContribution (L := L) lam β A φ idx := by
  classical
  let keys := collisionWordMarkedGapRunKeys h L
  let indices := collisionWordNonpairWordIndices h L
  let keyIndex : CCR25GapRunKey h → CCR25PartitionWordIndex h :=
    ccr25GapRunKeyWordIndex
  let keyContribution (key : CCR25GapRunKey h) :=
    Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
      ∑ x ∈ configBox h A L,
        hattedReplicaBoundaryVector L key.firstLabel A φ x *
          ccr25GapRunKeyDampedTail L lam β A key x
  have hmap : ∀ key ∈ keys, keyIndex key ∈ indices := by
    intro key hkey
    obtain ⟨hword, hlength⟩ := collisionWord_markedGapRunKey_word_mem hkey
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hlength, hword⟩
  have hfiberwise :
      (∑ key ∈ keys, keyContribution key) =
        ∑ idx ∈ indices,
          ∑ key ∈ keys.filter (fun key => keyIndex key = idx),
            keyContribution key := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfiber (idx : CCR25PartitionWordIndex h) (hidx : idx ∈ indices) :
      (∑ key ∈ keys.filter (fun key => keyIndex key = idx),
        keyContribution key) ≤
        Real.exp (lam * L) *
          ccr25WordIndexContribution (L := L) lam β A φ idx := by
    exact ccr25GapRunKeyFiber_contribution_le_wordIndex_of_gapFacts lam β A φ hφ
      idx (keys.filter fun key => keyIndex key = idx)
      (fun key hk => collisionWord_markedGapRunKey_gapFacts
        ((Finset.mem_filter.mp hk).1)) (by
        intro key hk
        exact (Finset.mem_filter.mp hk).2)
  calc
    _ = ∑ idx ∈ indices,
        ∑ key ∈ keys.filter (fun key => keyIndex key = idx),
          keyContribution key := hfiberwise
    _ ≤ ∑ idx ∈ indices,
        Real.exp (lam * L) *
          ccr25WordIndexContribution (L := L) lam β A φ idx :=
      Finset.sum_le_sum fun idx hidx => hfiber idx hidx
    _ = Real.exp (lam * L) *
        ∑ idx ∈ indices,
          ccr25WordIndexContribution (L := L) lam β A φ idx := by
      rw [← Finset.mul_sum]

/-- The marked partition expansion is bounded by a damped operator word sum.
The untouched replica labels remain free spectators. -/
theorem collisionWord_markedPartitionSum_le_wordRuns {h L : ℕ}
    (β lam : ℝ) (hlam : 0 ≤ lam) (A : Finset Site)
    (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
      (∏ i : Fin h, φ (x i)) *
        ∑ I ∈ collisionWordMarkedPartitionSequences h L,
          (∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) *
            replicaPathWeight (List.ofFn I) x) ≤
      Real.exp (lam * L) * ∑ n ∈ Finset.range L,
        ∑ J ∈ collisionWordNonpairPartitionWords h n,
          (∏ j : Fin (n + 1), |replicaPartitionDisorderMoment β (J j)|) *
            ccr25FiniteWordPairing (configBox h A L) L lam β J
              (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator := by
  classical
  calc
    _ = ∑ I ∈ collisionWordMarkedPartitionSequences h L,
        ∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
          (∏ i : Fin h, φ (x i)) *
            ((∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) *
              replicaPathWeight (List.ofFn I) x) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ runs ∈ collisionWordMarkedGapRunStreams h L,
        ccr25GapRunStreamProfileScore β A φ runs :=
      collisionWord_markedPartitionSum_eq_gapRunSum β A φ
    _ ≤ ∑ key ∈ collisionWordMarkedGapRunKeys h L,
        Real.exp (lam * L) * ccr25GapRunKeyMomentCoefficient β key *
          ∑ x ∈ configBox h A L,
            hattedReplicaBoundaryVector L key.firstLabel A φ x *
              ccr25GapRunKeyDampedTail L lam β A key x :=
      collisionWord_markedGapRunStreamSum_le_keyGapProfileSum β lam hlam A φ hφ
    _ ≤ Real.exp (lam * L) * ∑ idx ∈ collisionWordNonpairWordIndices h L,
        ccr25WordIndexContribution (L := L) lam β A φ idx :=
      collisionWord_markedGapRunKeySum_le_wordIndexSum lam β A φ hφ
    _ = _ := by
      rw [collisionWordNonpairWordIndices, Finset.sum_sigma]
      rfl

end Critical2DKPZ.SHF.Moments

end
