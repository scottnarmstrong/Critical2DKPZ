/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationRunDampingProduct
import Mathlib.Tactic

/-! # Truncated Laplace sums of collision runs -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- The Laplace-weighted sum of a pair run over durations at most `d` is
bounded by the full hatted interacting kernel, whenever `d ≤ L`. -/
theorem collisionWord_pairRunFactor_laplace_sum_le_hatted
    {h : ℕ} (β lam : ℝ) (L d : ℕ) (hd : d ≤ L)
    (α : CollisionPair h) (z x : LatticeConfiguration h) :
    (∑ r ∈ Finset.range (d + 1),
      Real.exp (-((lam / (L : ℝ)) * (r : ℝ))) *
        collisionWordUndampedPairRunFactor β α r z x) ≤
      sigmaSq β * hattedInteractingReplicaKernelAbs L
        (lam / (L : ℝ)) β (pairPartition α) z x := by
  have hfull := pairRunFactor_laplace_sum_eq_hattedInteracting
    β lam L α z x
  have hsumEq :
      (∑ r ∈ Finset.range (L + 1),
        Real.exp (-((lam / (L : ℝ)) * (r : ℝ))) *
          collisionWordUndampedPairRunFactor β α r z x) =
        sigmaSq β * hattedInteractingReplicaKernelAbs L
          (lam / (L : ℝ)) β (pairPartition α) z x := by
    simpa only [collisionWordUndampedPairRunFactor] using hfull
  have hsubset : Finset.range (d + 1) ⊆ Finset.range (L + 1) := by
    intro r hr
    simp only [Finset.mem_range] at hr ⊢
    omega
  have hnonneg (r : ℕ) :
      0 ≤ Real.exp (-((lam / (L : ℝ)) * (r : ℝ))) *
        collisionWordUndampedPairRunFactor β α r z x := by
    rw [collisionWordUndampedPairRunFactor,
      pairRunFactor_eq_sigmaSq_mul_interactingReplicaKernelAbs]
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (sigmaSq_nonneg β)
      (interactingReplicaKernelAbs_nonneg β (pairPartition α) r z x))
  calc
    _ ≤ ∑ r ∈ Finset.range (L + 1),
        Real.exp (-((lam / (L : ℝ)) * (r : ℝ))) *
          collisionWordUndampedPairRunFactor β α r z x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro r hr hnot
        exact hnonneg r)
    _ = _ := hsumEq

end Critical2DKPZ.SHF.Moments

end
