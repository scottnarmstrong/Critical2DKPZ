/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitPairMass

/-! # Run mass with any number of free spectator labels -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The run on its colliding pair and the independent spectator strands. -/
theorem pairRunFactor_eq_pairTwo_mul_spectators {h : ℕ} (β : ℝ)
    (α : CollisionPair h) (r : ℕ) (u v : LatticeConfiguration h) :
    collisionWordUndampedPairRunFactor β α r u v =
      collisionWordUndampedPairRunFactor β pairTwo r (pairRestrict α u) (pairRestrict α v) *
        ∏ i : Spectator α, srwKernel r (v i.1 - u i.1) := by
  classical
  have hprod : (∏ i : Fin h, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ)
      else srwKernel r (v i - u i)) =
      ∏ i : Spectator α, srwKernel r (v i.1 - u i.1) := by
    rw [wordLimit_prod_pair_spectators α]
    have hspec (i : Spectator α) :
        (if i.1 = α.1.1 ∨ i.1 = α.1.2 then (1 : ℝ) else srwKernel r (v i.1 - u i.1)) =
          srwKernel r (v i.1 - u i.1) := by simp only [i.2.1, i.2.2, or_self, ite_false]
    simp [Fin.prod_univ_two, hspec]
  simp [collisionWordUndampedPairRunFactor, hprod, pairTwo, pairRestrict, Fin.prod_univ_two]

/-- Summing a run's terminal coordinates leaves its scalar renewal mass;
all spectators contribute unit mass. -/
theorem tsum_pairRunFactor_eq_renewalMass {h : ℕ} (β : ℝ)
    (α : CollisionPair h) (r : ℕ) (u : LatticeConfiguration h) :
    (∑' v : LatticeConfiguration h, collisionWordUndampedPairRunFactor β α r u v) =
      if u α.1.1 = u α.1.2 then sigmaSq β * Renewal.renewalMass
        (fun k => sigmaSq β * Renewal.returnWeight k) r else 0 := by
  classical
  rw [tsum_eq_sum (s := collisionWordConfigurationEndpointSet r u)]
  · have hsum :
        (∑ v ∈ collisionWordConfigurationEndpointSet r u, collisionWordUndampedPairRunFactor β α r u v) =
        ∑ v ∈ collisionWordConfigurationEndpointSet r u,
          collisionWordUndampedPairRunFactor β pairTwo r (pairRestrict α u) (pairRestrict α v) *
            ∏ i : Spectator α, srwKernel r (v i.1 - u i.1) :=
        Finset.sum_congr rfl (fun v _ => pairRunFactor_eq_pairTwo_mul_spectators β α r u v)
    rw [hsum]
    simp only [collisionWordConfigurationEndpointSet]
    rw [wordLimit_sum_pair_spectator_coordinates α (fun i => endpoints (u i) r)
      (fun p => collisionWordUndampedPairRunFactor β pairTwo r (pairRestrict α u) p)
      (fun i z => srwKernel r (z - u i.1))]
    have hpair :
        (∑ p ∈ Fintype.piFinset (fun j : Fin 2 => endpoints (u (if j = 0 then α.1.1 else α.1.2)) r),
          collisionWordUndampedPairRunFactor β pairTwo r (pairRestrict α u) p) =
        ∑' p : Fin 2 → Site, collisionWordUndampedPairRunFactor β pairTwo r (pairRestrict α u) p := by
      symm
      apply tsum_eq_sum
      intro p hp
      exact collisionWord_runFactor_zero_of_not_endpoints β pairTwo r (pairRestrict α u) p hp
    simp_rw [sum_srwKernel_endpoints]
    rw [hpair, tsum_pairTwo_runFactor]
    simp [pairRestrict]
  · intro v hv
    exact collisionWord_runFactor_zero_of_not_endpoints β α r u v hv

end Critical2DKPZ.SHF.Moments
