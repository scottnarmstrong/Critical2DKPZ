/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.KernelVariation
import Mathlib.Tactic

/-! # Entrance mass averaged over a finite set of starting gaps -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

/-- Restricting the spatial mass of a walk to any finite set costs at most one. -/
theorem sum_srwKernel_finite_le_one (D : Finset Site) (n : ℕ) :
    ∑ z ∈ D, srwKernel n z ≤ 1 := by
  have hs : Summable (fun z : Site => srwKernel n z) := by
    apply summable_of_ne_finset_zero (s := endpoints 0 n)
    intro z hz
    simpa only [sub_zero] using srwKernel_eq_zero_of_not_mem n 0 z hz
  have ht : (∑' z : Site, srwKernel n z) = 1 := by
    simpa only [sub_zero] using tsum_srwKernel n 0
  rw [← ht]
  exact Summable.sum_le_tsum D (fun z _ => kernel_nonneg n z) hs



end Critical2DKPZ.SHF.Moments
