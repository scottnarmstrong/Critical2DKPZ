/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlockMass

/-! # Testing the endpoint of a fixed first collision block -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The nested reachable sums in the word recursion are exactly terminal
testing of its first-block kernel on the fixed total endpoint set. -/
theorem sum_free_run_terminal_eq {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x : LatticeConfiguration h) (H : LatticeConfiguration h → ℝ) :
    (∑ u ∈ collisionWordConfigurationEndpointSet s x,
      ∑ v ∈ collisionWordConfigurationEndpointSet r u,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v) =
      ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        (∑ u ∈ collisionWordConfigurationEndpointSet s x,
          (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
  have hin (u : LatticeConfiguration h) (hu : u ∈ collisionWordConfigurationEndpointSet s x) :
      (∑ v ∈ collisionWordConfigurationEndpointSet r u,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v) =
      ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
    have hsmall :
        (∑' v : LatticeConfiguration h,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v) =
        ∑ v ∈ collisionWordConfigurationEndpointSet r u,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
      apply tsum_eq_sum
      intro v hv
      rw [collisionWord_runFactor_zero_of_not_endpoints β α r u v hv, mul_zero, zero_mul]
    have htotal :
        (∑' v : LatticeConfiguration h,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v) =
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
      apply tsum_eq_sum
      intro v hv
      rw [runFactor_zero_of_not_total_endpoints β α s r x u v hu hv, mul_zero, zero_mul]
    exact hsmall.symm.trans htotal
  calc
    _ = ∑ u ∈ collisionWordConfigurationEndpointSet s x,
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v :=
      Finset.sum_congr rfl hin
    _ = ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        ∑ u ∈ collisionWordConfigurationEndpointSet s x,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (Finset.sum_mul _ _ _).symm

end Critical2DKPZ.SHF.Moments
