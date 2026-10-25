/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairSelection
public import Critical2DKPZ.MomentBounds.PairStratumBilinearDistinct
import Mathlib.Tactic

/-! # Finite-support form of LZ21 Equation 3.21 -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The LZ21 estimate for finite supports in two non-discrete equality strata,
excluding only the common single-pair stratum. The reduction permits nested and
equal coarser partitions. -/
theorem finite_equalityStratum_bilinear_le {h : ℕ}
    (I J : ReplicaPartition h) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcommon : ∀ α : DeltaBose.CollisionPair h,
      ¬(I = pairPartition α ∧ J = pairPartition α))
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (s t : Finset (LatticeConfiguration h))
    (hs : ∀ x ∈ s, IsEqualityConfiguration I x)
    (ht : ∀ y ∈ t, IsEqualityConfiguration J y)
    (f g : LatticeConfiguration h → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, |f x| * replicaGreenKernel x y * |g y|) ≤
      4 ^ ((h : ℝ) - 1) * 4 * (9 : ℝ) ^ (h - 3) * 1188 * (p * q) *
        (∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
        (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by
  obtain ⟨α, β, hα, hβ, hne⟩ := exists_distinct_collisionPairs I J hI hJ hcommon
  have hs' : ∀ x ∈ s, x α.val.1 = x α.val.2 := by
    intro x hx
    exact hs x hx _ _ hα
  have ht' : ∀ y ∈ t, y β.val.1 = y β.val.2 := by
    intro y hy
    exact ht y hy _ _ hβ
  exact finite_distinct_pair_stratum_bilinear_le α β hne hpq s t hs' ht' f g

end Critical2DKPZ.MomentBounds
