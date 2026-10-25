/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationBoundaryPairing
public import Critical2DKPZ.SHF.Moments.WordDominationPairPartitions
public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
import Mathlib.Tactic

/-! # Finite CCR operator form of the hatted pair path -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The alternating free and interacting kernel sequence is the CCR25 operator word for the corresponding pair partitions. -/
theorem pairWordInteriorKernels_eq_ccr25Labels {h n : ℕ}
    (L : ℕ) (lam β : ℝ) (w : CollisionWord h (n + 1)) :
    pairWordInteriorKernels L lam β (List.ofFn w.1) =
      (ccr25PartitionWordLabels n (collisionWordPairPartition w)).map
        (ccr25LabelKernel L lam β) := by
  induction n with
  | zero =>
      simp [pairWordInteriorKernels, ccr25PartitionWordLabels,
        ccr25LabelKernel, collisionWordPairPartition]
  | succ n ih =>
      let wt : CollisionWord h (n + 1) :=
        ⟨fun i => w.1 i.succ, by
          intro i j hij
          apply w.2 i.succ j.succ
          simp only [Fin.val_succ]
          omega⟩
      have hword : List.ofFn w.1 = w.1 0 :: List.ofFn wt.1 := by
        simp [wt]
      have hwtword :
          List.ofFn wt.1 =
            wt.1 0 :: List.ofFn (fun i : Fin n => wt.1 i.succ) := by
        simp only [List.ofFn_succ]
      rw [hword]
      rw [hwtword]
      change
        hattedInteractingReplicaKernelAbs L lam β (pairPartition (w.1 0)) ::
          hattedFreeReplicaKernel L (pairPartition (w.1 0))
            (pairPartition (wt.1 0)) ::
            pairWordInteriorKernels L lam β
              (wt.1 0 :: List.ofFn (fun i : Fin n => wt.1 i.succ)) =
        hattedInteractingReplicaKernelAbs L lam β (collisionWordPairPartition w 0) ::
          hattedFreeReplicaKernel L (collisionWordPairPartition w 0)
            (collisionWordPairPartition w 1) ::
            (ccr25PartitionWordLabels n
              (fun j => collisionWordPairPartition w j.succ)).map
                (ccr25LabelKernel L lam β)
      rw [← hwtword, ih wt]
      have hseq : collisionWordPairPartition wt =
          (fun j : Fin (n + 1) => pairPartition (w.1 j.succ)) := by
        funext j
        rfl
      rw [hseq]
      rfl

/-- The endpoint-summed hatted pair path equals CCR25's finite-volume
operator pairing on a configuration box large enough for every intermediate
state. -/
theorem finite_sum_hattedPairWordPath_eq_ccr25FiniteWordPairing
    {h n : ℕ} (L : ℕ) (lam β : ℝ) (A : Finset Site)
    (w : CollisionWord h (n + 1)) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
      ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
        hattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) =
      ccr25FiniteWordPairing
        (configBox h A
          (L + (pairWordInteriorKernels L lam β (List.ofFn w.1)).length * L))
        L lam β (collisionWordPairPartition w)
        (fun _ x => hattedReplicaBoundaryVector L (pairPartition (w.1 0))
          A (collisionWordSiteIndicator A) x)
        (fun _ x => hattedReplicaBoundaryVector L
          (pairWordLastPartition (List.ofFn w.1))
          A (collisionWordSiteIndicator A) x) := by
  classical
  let α : CollisionPair h := w.1 0
  let rest : List (CollisionPair h) := List.ofFn (fun i : Fin n => w.1 i.succ)
  let mid : List (LatticeConfiguration h → LatticeConfiguration h → ℝ) :=
    pairWordInteriorKernels L lam β (List.ofFn w.1)
  let base : Finset (LatticeConfiguration h) := configBox h A L
  let s : Finset (LatticeConfiguration h) := configBox h A (L + mid.length * L)
  let leftBoundary : LatticeConfiguration h → ℝ :=
    hattedReplicaBoundaryVector L (pairPartition α) A (collisionWordSiteIndicator A)
  let rightBoundary : LatticeConfiguration h → ℝ :=
    hattedReplicaBoundaryVector L (pairWordLastPartition (List.ofFn w.1))
      A (collisionWordSiteIndicator A)
  have hword : List.ofFn w.1 = α :: rest := by
    dsimp [α, rest]
    simp only [List.ofFn_succ]
  have hsplit :
      hattedPairWordKernelList L lam β ⊥ (List.ofFn w.1) =
        hattedFreeReplicaKernel L ⊥ (pairPartition α) ::
          (mid ++ [hattedFreeReplicaKernel L
            (pairWordLastPartition (List.ofFn w.1)) ⊥]) := by
    rw [hword]
    simpa [mid] using
      hattedPairWordKernelList_split L lam β ⊥ α rest
  have hcoreMem (K : LatticeConfiguration h → LatticeConfiguration h → ℝ)
      (hK : K ∈ mid) :
      K ∈ hattedPairWordKernelList L lam β ⊥ (List.ofFn w.1) := by
    rw [hsplit]
    simp only [List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl hK)
  have hstep : ∀ K ∈ mid, ∀ r : ℕ, ∀ x,
      x ∈ configBox h A r → ∀ y, K x y ≠ 0 → y ∈ configBox h A (r + L) := by
    intro K hK r x hx y hKxy
    exact hattedPairWordKernelList_boxStep
      (A := A) (lam := lam) (β := β) (previous := ⊥)
      (List.ofFn w.1) K (hcoreMem K hK) r x hx y hKxy
  have hleftZero (x : LatticeConfiguration h) (hx : x ∉ base) :
      leftBoundary x = 0 := by
    exact hattedReplicaBoundaryVector_zero_of_not_configBox
      L (pairPartition α) A (collisionWordSiteIndicator A) hx
  have hfinitePath (x : LatticeConfiguration h) (hx : x ∈ base) :
      collisionKernelWordAction mid rightBoundary x =
        finiteKernelWordApply s mid rightBoundary x := by
    have h := collisionKernelWordAction_eq_finiteKernelWordApply
      (A := A) mid hstep rightBoundary L x hx
    simpa [base, s, mid] using h
  have hpath := finite_sum_hattedPairWordPath_eq_boundaryPairing
    L lam β A A α rest
  rw [← hword] at hpath
  have hpath' :
      (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
          hattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) =
        ∑ x ∈ base, leftBoundary x * finiteKernelWordApply s mid rightBoundary x := by
    rw [hpath]
    rw [tsum_eq_sum (s := base)]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [hfinitePath x hx]
    · intro x hx
      change leftBoundary x *
        collisionKernelWordAction mid rightBoundary x = 0
      rw [hleftZero x hx]
      simp
  have hsubset : base ⊆ s := by
    apply ccr25ConfigBox_mono
    omega
  have hpair : ccr25FiniteWordPairing s L lam β
      (collisionWordPairPartition w)
      (fun _ x => leftBoundary x) (fun _ x => rightBoundary x) =
      ∑ x ∈ base, leftBoundary x * finiteKernelWordApply s mid rightBoundary x := by
    rw [ccr25FiniteWordPairing]
    have hlabels := pairWordInteriorKernels_eq_ccr25Labels L lam β w
    change (∑ x ∈ s, leftBoundary x *
        finiteKernelWordApply s
          ((ccr25PartitionWordLabels n (collisionWordPairPartition w)).map
            (ccr25LabelKernel L lam β)) rightBoundary x) = _
    rw [← hlabels]
    rw [Finset.sum_subset hsubset]
    intro x hxS hxBase
    change leftBoundary x *
      finiteKernelWordApply s mid rightBoundary x = 0
    rw [hleftZero x hxBase]
    simp
  rw [hpath']
  simpa [base, s, mid, leftBoundary, rightBoundary, α] using hpair.symm

end Critical2DKPZ.SHF.Moments

end
