/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ArrivalKernel
import Mathlib.Tactic

/-! # Finite spatial support of the collision sums used in block moments -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Blocks

/-- The spatial renewal profile at the polymer coupling has the walk's finite reachable support. -/
theorem spatialRenewal_sigmaSq_eq_zero_of_not_mem (β : ℝ) (n : ℕ) (w x : Site)
    (hx : x ∉ Polymer.endpoints w n) :
    Collision.spatialRenewal (Polymer.sigmaSq β) n (x - w) = 0 := by
  cases n with
  | zero =>
    simpa only [Collision.spatialRenewal_zero, Polymer.srwKernel_zero] using
      Polymer.srwKernel_eq_zero_of_not_mem 0 w x hx
  | succ n =>
    rw [← sigmaSq_mul_preTerminalKernel_sq_integral β 0 n w x]
    simp only [preTerminalKernel_eq_zero_of_not_mem β 0 n w x _ hx,
      zero_pow (by omega : 2 ≠ 0), MeasureTheory.integral_zero, mul_zero]


end Critical2DKPZ.Blocks
