/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourCoordinates
public import Critical2DKPZ.SHF.Moments.PairStratumRenewalIdentity
import Critical2DKPZ.SHF.Moments.WordDominationPairStratumFree
import Mathlib.Tactic

/-! # Exact product kernels for the leading two-pair fourth-moment term -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A free interval between disjoint pair strata is the four independent walk
kernels, restricted only at its two pair endpoints. -/
theorem freeReplicaKernel_disjoint_pairs_eq (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (n : ℕ) (z x : LatticeConfiguration 4) :
    freeReplicaKernel n (pairPartition α) (pairPartition δ) z x =
      if z α.1.1 = z α.1.2 ∧ x δ.1.1 = x δ.1.2 then
        (srwKernel n (x α.1.1 - z α.1.1) * srwKernel n (x α.1.2 - z α.1.2)) *
          (srwKernel n (x δ.1.1 - z δ.1.1) * srwKernel n (x δ.1.2 - z δ.1.2))
      else 0 := by
  rw [freeReplicaKernel, SHF.Moments.collisionWord_pairPartition_collision_iff,
    SHF.Moments.collisionWord_pairPartition_collision_iff,
    prod_disjointPair_labels α δ hd]
  split_ifs <;> rfl

/-- On a pair stratum, the two other replicas remain free throughout the
interaction run. This identity includes runs of duration zero. -/
theorem interactingReplicaKernelAbs_disjoint_pairs_eq (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (n : ℕ) (z x : LatticeConfiguration 4) :
    interactingReplicaKernelAbs β (pairPartition α) n z x =
      if z α.1.1 = z α.1.2 ∧ x α.1.1 = x α.1.2 then
        Collision.spatialRenewal (Polymer.sigmaSq β) n (x α.1.1 - z α.1.1) *
          (srwKernel n (x δ.1.1 - z δ.1.1) * srwKernel n (x δ.1.2 - z δ.1.2))
      else 0 := by
  by_cases hz : z α.1.1 = z α.1.2
  · by_cases hx : x α.1.1 = x α.1.2
    · rw [ite_eq_left ⟨hz, hx⟩,
        SHF.Moments.interactingReplicaKernelAbs_pairPartition_eq_on_strata β α n z x hz hx,
        SHF.Moments.otherBlocksFreeKernel_pairPartition_eq,
        prod_disjointPair_labels α δ hd]
      obtain ⟨hac, had, hbc, hbd⟩ := disjoint_pair_cross_ne α δ hd
      simp only [true_or, or_true, ite_true,
        ite_eq_right (show ¬ (δ.1.1 = α.1.1 ∨ δ.1.1 = α.1.2) from
          not_or.mpr ⟨hac.symm, hbc.symm⟩),
        ite_eq_right (show ¬ (δ.1.2 = α.1.1 ∨ δ.1.2 = α.1.2) from
          not_or.mpr ⟨had.symm, hbd.symm⟩), one_mul]
    · rw [ite_eq_right (by simp only [hz, hx, and_false, not_false_eq_true])]
      exact SHF.Moments.interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
        β α n z x (Or.inr hx)
  · rw [ite_eq_right (by simp only [hz, false_and, not_false_eq_true])]
    exact SHF.Moments.interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
      β α n z x (Or.inl hz)

/-- At its first pair collision, the initial four-test product factors into
a square on the colliding pair and two free test convolutions. -/
theorem replicaBoundaryVector_disjoint_pairs_eq (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (n : ℕ) (S : Finset Site) (φ : Site → ℝ) (x : LatticeConfiguration 4) :
    replicaBoundaryVector n (pairPartition α) S φ x =
      if x α.1.1 = x α.1.2 then
        finiteBoundaryConvolution n S φ (x α.1.1) ^ 2 *
          (finiteBoundaryConvolution n S φ (x δ.1.1) * finiteBoundaryConvolution n S φ (x δ.1.2))
      else 0 := by
  rw [replicaBoundaryVector, SHF.Moments.collisionWord_pairPartition_collision_iff,
    prod_disjointPair_labels α δ hd]
  split_ifs with hx
  · rw [← hx]
    ring
  · rfl

end Critical2DKPZ.Extensions.GffTangent
