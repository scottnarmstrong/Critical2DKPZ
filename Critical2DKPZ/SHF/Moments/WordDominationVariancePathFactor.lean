/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationDampedPathRecursion
public import Critical2DKPZ.SHF.Moments.WordDominationHattedPath
import Mathlib.Tactic

/-! # Variance factors in the damped pair-word path -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

/-- The variance-weighted damped path is the ordinary hatted path multiplied
by one variance factor for each collision-word letter. -/
theorem varianceWeightedHattedPairWordPath_eq_sigmaSq_pow_mul
    {h : ℕ} (L : ℕ) (lam β : ℝ) (previous : ReplicaPartition h)
    (w : List (CollisionPair h)) (x y : LatticeConfiguration h) :
    varianceWeightedHattedPairWordPath L lam β previous w x y =
      sigmaSq β ^ w.length * hattedPairWordPath L lam β previous w x y := by
  induction w generalizing previous x y with
  | nil => simp [varianceWeightedHattedPairWordPath, hattedPairWordPath]
  | cons α w ih =>
      simp only [List.length_cons, varianceWeightedHattedPairWordPath,
        hattedPairWordPath]
      have htail (u v : LatticeConfiguration h) :
          varianceWeightedHattedPairWordPath L lam β (pairPartition α) w v y =
            sigmaSq β ^ w.length *
              hattedPairWordPath L lam β (pairPartition α) w v y :=
        ih (pairPartition α) v y
      have hinner (u : LatticeConfiguration h) :
          hattedFreeReplicaKernel L previous (pairPartition α) x u *
              (∑' v : LatticeConfiguration h,
                sigmaSq β * hattedInteractingReplicaKernelAbs L lam β
                  (pairPartition α) u v *
                  varianceWeightedHattedPairWordPath L lam β
                    (pairPartition α) w v y) =
            sigmaSq β ^ (w.length + 1) *
              (hattedFreeReplicaKernel L previous (pairPartition α) x u *
                ∑' v : LatticeConfiguration h,
                  hattedInteractingReplicaKernelAbs L lam β
                    (pairPartition α) u v *
                    hattedPairWordPath L lam β
                      (pairPartition α) w v y) := by
        have hsum :
            (∑' v : LatticeConfiguration h,
              sigmaSq β * hattedInteractingReplicaKernelAbs L lam β
                (pairPartition α) u v *
                varianceWeightedHattedPairWordPath L lam β
                  (pairPartition α) w v y) =
              sigmaSq β ^ (w.length + 1) *
                ∑' v : LatticeConfiguration h,
                  hattedInteractingReplicaKernelAbs L lam β
                    (pairPartition α) u v *
                    hattedPairWordPath L lam β
                      (pairPartition α) w v y := by
          calc
            _ = ∑' v : LatticeConfiguration h,
                  sigmaSq β ^ (w.length + 1) *
                    (hattedInteractingReplicaKernelAbs L lam β
                      (pairPartition α) u v *
                      hattedPairWordPath L lam β
                        (pairPartition α) w v y) := by
                apply tsum_congr
                intro v
                rw [htail u v, pow_succ]
                ring
            _ = _ := tsum_mul_left
        calc
          _ = hattedFreeReplicaKernel L previous (pairPartition α) x u *
                (sigmaSq β ^ (w.length + 1) *
                  ∑' v : LatticeConfiguration h,
                    hattedInteractingReplicaKernelAbs L lam β
                      (pairPartition α) u v *
                      hattedPairWordPath L lam β
                        (pairPartition α) w v y) := by rw [hsum]
          _ = _ := by ring
      calc
        _ = ∑' u : LatticeConfiguration h,
              sigmaSq β ^ (w.length + 1) *
                (hattedFreeReplicaKernel L previous (pairPartition α) x u *
                  ∑' v : LatticeConfiguration h,
                    hattedInteractingReplicaKernelAbs L lam β
                      (pairPartition α) u v *
                      hattedPairWordPath L lam β (pairPartition α) w v y) := by
          apply tsum_congr
          intro u
          exact hinner u
        _ = _ := by rw [tsum_mul_left]

end Critical2DKPZ.SHF.Moments

end
