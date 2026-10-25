/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewalComposition
import Mathlib.Tactic

/-! # Reflection symmetry of the CCR25 spatial renewal profile -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

private theorem squareConvolution_neg (ks : List ℕ) (x : Site) :
    Critical2DKPZ.Collision.squareConvolution ks (-x) =
      Critical2DKPZ.Collision.squareConvolution ks x := by
  induction ks generalizing x with
  | nil =>
      simp [Critical2DKPZ.Collision.squareConvolution]
  | cons k ks ih =>
      change (∑' z : Site,
          Critical2DKPZ.srwKernel k z ^ 2 *
            Critical2DKPZ.Collision.squareConvolution ks (-x - z)) =
        ∑' z : Site,
          Critical2DKPZ.srwKernel k z ^ 2 *
            Critical2DKPZ.Collision.squareConvolution ks (x - z)
      calc
        _ = ∑' z : Site,
            Critical2DKPZ.srwKernel k (-z) ^ 2 *
              Critical2DKPZ.Collision.squareConvolution ks (-x - -z) := by
              exact (Equiv.neg Site).tsum_eq (fun z : Site =>
                Critical2DKPZ.srwKernel k z ^ 2 *
                  Critical2DKPZ.Collision.squareConvolution ks (-x - z)) |>.symm
        _ = _ := by
          apply tsum_congr
          intro z
          have harg : -x - -z = -(x - z) := by abel
          rw [Critical2DKPZ.Polymer.srwKernel_neg, harg, ih]

/-- The spatial renewal profile is invariant under reflection of its displacement. -/
theorem spatialRenewal_neg (σ2 : ℝ) (n : ℕ) (x : Site) :
    Critical2DKPZ.Collision.spatialRenewal σ2 n (-x) =
      Critical2DKPZ.Collision.spatialRenewal σ2 n x := by
  cases n with
  | zero => simp [Critical2DKPZ.Collision.spatialRenewal_zero]
  | succ n =>
      rw [Critical2DKPZ.Collision.spatialRenewal_eq_sum_compositions σ2 (by omega),
        Critical2DKPZ.Collision.spatialRenewal_eq_sum_compositions σ2 (by omega)]
      apply Finset.sum_congr rfl
      intro c hc
      rw [squareConvolution_neg]

end Critical2DKPZ.MomentBounds

end
