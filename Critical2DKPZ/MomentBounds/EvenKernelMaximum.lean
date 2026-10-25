/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.WalkKernel
import Critical2DKPZ.Lattice.Basic

/-! # The even walk kernel is maximized at the origin -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Cauchy--Schwarz for the two halves of the walk, written as `2ab ≤ a²+b²`. -/
theorem srwKernel_two_mul_le_zero (n : ℕ) (z : Site) :
    srwKernel (2 * n) z ≤ srwKernel (2 * n) 0 := by
  have hs : Summable (fun y => srwKernel n y ^ 2) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 n)
    intro y hy
    have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 y hy
    simp only [sub_zero] at h
    rw [h]
    norm_num
  have ht : (∑' y, srwKernel n (z - y) ^ 2) = ∑' y, srwKernel n y ^ 2 :=
    (Equiv.subLeft z).tsum_eq (fun y => srwKernel n y ^ 2)
  have hs' : Summable (fun y => srwKernel n (z - y) ^ 2) :=
    (Equiv.subLeft z).summable_iff (f := fun y : Site => srwKernel n y ^ 2) |>.2 hs
  have hp : Summable (fun y => srwKernel n y * srwKernel n (z - y)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 n)
    intro y hy
    have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 y hy
    simp only [sub_zero] at h
    rw [h, zero_mul]
  calc
    _ = ∑' y, srwKernel n y * srwKernel n (z - y) := by
      simpa only [← two_mul, sub_zero] using Polymer.srwKernel_convolution n n 0 z
    _ ≤ ∑' y, (srwKernel n y ^ 2 + srwKernel n (z - y) ^ 2) / 2 :=
      hp.tsum_le_tsum (fun y => by nlinarith only [sq_nonneg (srwKernel n y - srwKernel n (z - y))])
        ((hs.add hs').div_const 2)
    _ = ∑' y, srwKernel n y ^ 2 := by
      rw [tsum_div_const, hs.tsum_add hs', ht]
      ring
    _ = _ := by simpa only [sub_zero, pow_two] using Polymer.srwKernel_collision n 0 0

end Critical2DKPZ.MomentBounds
