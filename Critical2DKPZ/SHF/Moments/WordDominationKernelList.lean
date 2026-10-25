/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPathLinearity
public import Critical2DKPZ.SHF.Moments.WordDominationHattedPath
import Mathlib.Tactic

/-! Kernel lists encode the normalized collision path. -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- The alternating hatted kernel list for a collision word, including the
initial free interval and the terminal free interval. -/
def hattedPairWordKernelList {h : ℕ} (L : ℕ) (lam β : ℝ)
    (previous : ReplicaPartition h) : List (CollisionPair h) →
    List (LatticeConfiguration h → LatticeConfiguration h → ℝ)
  | [] => [hattedFreeReplicaKernel L previous ⊥]
  | α :: w => hattedFreeReplicaKernel L previous (pairPartition α) ::
      hattedInteractingReplicaKernelAbs L lam β (pairPartition α) ::
        hattedPairWordKernelList L lam β (pairPartition α) w

/-- The hatted path is the unrestricted operator application of its
alternating free and interacting kernel list. -/
theorem hattedPairWordPath_eq_fullKernelWordApply {h : ℕ}
    (L : ℕ) (lam β : ℝ) (previous : ReplicaPartition h) :
    ∀ (w : List (CollisionPair h)) (x y : LatticeConfiguration h),
      hattedPairWordPath L lam β previous w x y =
        collisionKernelWordAction
          (hattedPairWordKernelList L lam β previous w)
          (fun z => if z = y then 1 else 0) x := by
  intro w
  induction w generalizing previous with
  | nil =>
      intro x y
      simp [hattedPairWordPath, hattedPairWordKernelList,
        collisionKernelWordAction]
  | cons α w ih =>
      intro x y
      simp only [hattedPairWordPath, hattedPairWordKernelList,
        collisionKernelWordAction]
      apply tsum_congr
      intro u
      apply congrArg (fun q : ℝ =>
        hattedFreeReplicaKernel L previous (pairPartition α) x u * q)
      apply tsum_congr
      intro v
      rw [ih (pairPartition α) v y]

/-- Each kernel in the hatted pair-word list expands a configuration box by
at most the cutoff horizon. -/
theorem hattedPairWordKernelList_boxStep {h L : ℕ}
    (A : Finset Critical2DKPZ.Site) (lam β : ℝ) (previous : ReplicaPartition h) :
    ∀ (w : List (CollisionPair h))
      (K : LatticeConfiguration h → LatticeConfiguration h → ℝ)
      (_hK : K ∈ hattedPairWordKernelList L lam β previous w)
      (r : ℕ) (x : LatticeConfiguration h),
      x ∈ configBox h A r → ∀ y, K x y ≠ 0 → y ∈ configBox h A (r + L) := by
  intro w
  induction w generalizing previous with
  | nil =>
      intro K _hK r x hx y hKxy
      simp only [hattedPairWordKernelList, List.mem_singleton] at _hK
      subst K
      by_contra hy
      have hz := hattedFreeReplicaKernel_zero_of_not_configBox
        (I := previous) (J := ⊥) hx hy
      rw [hz] at hKxy
      exact hKxy rfl
  | cons α w ih =>
      intro K _hK r x hx y hKxy
      simp only [hattedPairWordKernelList, List.mem_cons] at _hK
      rcases _hK with rfl | rfl | _hK
      · by_contra hy
        have hz := hattedFreeReplicaKernel_zero_of_not_configBox
          (I := previous) (J := pairPartition α) hx hy
        rw [hz] at hKxy
        exact hKxy rfl
      · by_contra hy
        have hz := hattedInteractingReplicaKernelAbs_zero_of_not_configBox
          lam β (pairPartition α) hx hy
        rw [hz] at hKxy
        exact hKxy rfl
      · exact ih (pairPartition α) K _hK r x hx y hKxy

end Critical2DKPZ.SHF.Moments

end
