/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationDampedProfileSum
public import Critical2DKPZ.SHF.Moments.WordDominationFreeTail
public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.WordDominationHattedPath
public import Critical2DKPZ.MomentBounds.CCR25FreeKernelSemigroup
import Mathlib.Tactic

/-! # Iteration of the damped pair-run contraction along a word -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

/-- The hatted operator path with one distinguished variance for each
collision-word letter. -/
noncomputable def varianceWeightedHattedPairWordPath {h : ℕ} (L : ℕ) (lam β : ℝ)
    (previous : ReplicaPartition h) :
    List (CollisionPair h) → LatticeConfiguration h → LatticeConfiguration h → ℝ
  | [], x, y => hattedFreeReplicaKernel L previous ⊥ x y
  | α :: w, x, y =>
      ∑' u : LatticeConfiguration h,
        hattedFreeReplicaKernel L previous (pairPartition α) x u *
          ∑' v : LatticeConfiguration h,
            (sigmaSq β * hattedInteractingReplicaKernelAbs L lam β
              (pairPartition α) u v) *
              varianceWeightedHattedPairWordPath L lam β (pairPartition α) w v y



/-- The variance-weighted hatted path is nonnegative for every collision word. -/
theorem varianceWeightedHattedPairWordPath_nonneg {h : ℕ} (L : ℕ) (lam β : ℝ)
    (previous : ReplicaPartition h) :
    ∀ w x y, 0 ≤ varianceWeightedHattedPairWordPath L lam β previous w x y := by
  intro w
  induction w generalizing previous with
  | nil =>
      intro x y
      exact hattedFreeReplicaKernel_nonneg L previous ⊥ x y
  | cons α w ih =>
      intro x y
      apply tsum_nonneg
      intro u
      apply mul_nonneg
      · exact hattedFreeReplicaKernel_nonneg L previous (pairPartition α) x u
      · apply tsum_nonneg
        intro v
        exact mul_nonneg
          (mul_nonneg (sigmaSq_nonneg β)
            (hattedInteractingReplicaKernelAbs_nonneg L lam β
              (pairPartition α) u v))
          (ih (pairPartition α) v y)



end Critical2DKPZ.SHF.Moments

end
