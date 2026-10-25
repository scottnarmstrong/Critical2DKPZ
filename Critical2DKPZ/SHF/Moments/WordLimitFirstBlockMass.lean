/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitEntranceRunMass

/-! # Finite endpoint mass of a fixed first collision block -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Reachability through an entrance and a run restricts the run endpoint to their total horizon. -/
theorem runFactor_zero_of_not_total_endpoints {h : ℕ}
    (β : ℝ) (α : CollisionPair h) (s r : ℕ) (x u v : LatticeConfiguration h)
    (hu : u ∈ collisionWordConfigurationEndpointSet s x)
    (hv : v ∉ collisionWordConfigurationEndpointSet (s + r) x) :
    collisionWordUndampedPairRunFactor β α r u v = 0 := by
  apply collisionWord_runFactor_zero_of_not_endpoints
  intro hmem
  apply hv
  apply Fintype.mem_piFinset.mpr
  intro i
  exact endpoints_compose_collisionRun (Fintype.mem_piFinset.mp hu i)
    (Fintype.mem_piFinset.mp hmem i)


/-- Summing the fixed first block on its finite total endpoint set gives
exactly the scalar entrance mass times its renewal run mass. -/
theorem sum_free_run_total_mass {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x : LatticeConfiguration h) :
    (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
      ∑ u ∈ collisionWordConfigurationEndpointSet s x,
        (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) =
      srwKernel (2 * s) (x α.1.2 - x α.1.1) *
        (sigmaSq β * Renewal.renewalMass
          (fun k => sigmaSq β * Renewal.returnWeight k) r) := by
  have hin (u : LatticeConfiguration h) (hu : u ∈ collisionWordConfigurationEndpointSet s x) :
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        collisionWordUndampedPairRunFactor β α r u v) =
        ∑' v : LatticeConfiguration h, collisionWordUndampedPairRunFactor β α r u v := by
    symm
    apply tsum_eq_sum
    intro v hv
    exact runFactor_zero_of_not_total_endpoints β α s r x u v hu hv
  have hout :
      (∑ u ∈ collisionWordConfigurationEndpointSet s x, (∏ i, srwKernel s (u i - x i)) *
        ∑' v : LatticeConfiguration h, collisionWordUndampedPairRunFactor β α r u v) =
      ∑' u : LatticeConfiguration h, (∏ i, srwKernel s (u i - x i)) *
        ∑' v : LatticeConfiguration h, collisionWordUndampedPairRunFactor β α r u v := by
    symm
    apply tsum_eq_sum
    intro u hu
    rw [collisionWord_freeProduct_zero_of_not_endpoints s x u hu, zero_mul]
  calc
    _ = ∑ u ∈ collisionWordConfigurationEndpointSet s x,
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v :=
      Finset.sum_comm
    _ = ∑ u ∈ collisionWordConfigurationEndpointSet s x,
        (∏ i, srwKernel s (u i - x i)) *
          ∑' v : LatticeConfiguration h, collisionWordUndampedPairRunFactor β α r u v := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum, hin u hu]
    _ = _ := hout.trans (tsum_pair_entrance_run_mass β α s r x)

end Critical2DKPZ.SHF.Moments
