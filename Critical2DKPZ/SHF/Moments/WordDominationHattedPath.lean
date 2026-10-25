/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.WordDominationRunDampingProduct
import Mathlib.Tactic

/-! # Hatted operator path attached to a collision word -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

/-- The full-lattice hatted operator path for a list of pair-collision runs.
The free kernels connect the previous and next pair strata, and the empty
tail supplies the final free endpoint transition. -/
def hattedPairWordPath {h : ℕ} (L : ℕ) (lam β : ℝ)
    (previous : ReplicaPartition h) :
    List (CollisionPair h) → LatticeConfiguration h → LatticeConfiguration h → ℝ
  | [], x, y => hattedFreeReplicaKernel L previous ⊥ x y
  | α :: w, x, y =>
      ∑' u : LatticeConfiguration h,
        hattedFreeReplicaKernel L previous (pairPartition α) x u *
          ∑' v : LatticeConfiguration h,
            hattedInteractingReplicaKernelAbs L lam β (pairPartition α) u v *
              hattedPairWordPath L lam β (pairPartition α) w v y



end Critical2DKPZ.SHF.Moments

end
