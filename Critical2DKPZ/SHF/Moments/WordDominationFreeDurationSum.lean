/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Summing positive free durations -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Summing exact free replica transitions over durations `1,…,n` is bounded
by the hatted free kernel at any cutoff `L ≥ n`. -/
theorem collisionWord_freeReplicaKernel_duration_sum_le {h n L : ℕ} (hnL : n ≤ L)
    (I J : ReplicaPartition h) (x y : LatticeConfiguration h) :
    (∑ d ∈ Finset.Icc 1 n, freeReplicaKernel d I J x y) ≤
      hattedFreeReplicaKernel L I J x y := by
  have hshift :
      (∑ d ∈ Finset.Icc 1 n, freeReplicaKernel d I J x y) =
        ∑ r ∈ Finset.range n, freeReplicaKernel (r + 1) I J x y := by
    apply Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      simp only [Finset.mem_range]
      omega
    · intro d hd e he hde
      simp only [Finset.mem_Icc] at hd he
      omega
    · intro r hr
      have hr' : r < n := Finset.mem_range.mp hr
      refine ⟨r + 1, Finset.mem_Icc.mpr ?_, ?_⟩
      · omega
      · simp
    · intro d hd
      have hd' : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      congr 1
      exact (Nat.sub_add_cancel hd').symm
  have hsubset : Finset.range n ⊆ Finset.range L := by
    intro r hr
    simp only [Finset.mem_range] at hr ⊢
    omega
  have hnonneg (r : ℕ) : 0 ≤ freeReplicaKernel (r + 1) I J x y :=
    freeReplicaKernel_nonneg (r + 1) I J x y
  calc
    _ = ∑ r ∈ Finset.range n, freeReplicaKernel (r + 1) I J x y := hshift
    _ ≤ ∑ r ∈ Finset.range L, freeReplicaKernel (r + 1) I J x y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro r hr hnot
        exact hnonneg r)
    _ = hattedFreeReplicaKernel L I J x y := by
      rfl

end Critical2DKPZ.SHF.Moments

end
