/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitRunMass

/-! # Total mass of a fixed entrance and renewal run -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Free spectators disappear from the collision entrance mass. -/
theorem tsum_pair_entrance_constant {h : ℕ} (s : ℕ) (α : CollisionPair h)
    (x : LatticeConfiguration h) (C : ℝ) :
    (∑' u : LatticeConfiguration h, (∏ i, srwKernel s (u i - x i)) *
      (if u α.1.1 = u α.1.2 then C else 0)) =
      srwKernel (2 * s) (x α.1.2 - x α.1.1) * C := by
  classical
  let F : (Fin 2 → Site) → ℝ := fun p =>
    (∏ j, srwKernel s (p j - pairRestrict α x j)) * (if p 0 = p 1 then C else 0)
  have hpoint (u : LatticeConfiguration h) :
      (∏ i, srwKernel s (u i - x i)) * (if u α.1.1 = u α.1.2 then C else 0) =
        F (pairRestrict α u) * ∏ i : Spectator α, srwKernel s (u i.1 - x i.1) := by
    rw [wordLimit_prod_pair_spectators α]
    dsimp only [F]
    have hu0 : pairRestrict α u 0 = u α.1.1 := rfl
    have hu1 : pairRestrict α u 1 = u α.1.2 := rfl
    rw [hu0, hu1]
    simp only [Fin.prod_univ_two]
    simp [pairRestrict]
    ac_rfl
  rw [tsum_eq_sum (s := collisionWordConfigurationEndpointSet s x)]
  · simp_rw [hpoint]
    simp only [collisionWordConfigurationEndpointSet]
    rw [wordLimit_sum_pair_spectator_coordinates α (fun i => endpoints (x i) s) F
      (fun i z => srwKernel s (z - x i.1))]
    have hpair :
        (∑ p ∈ Fintype.piFinset (fun j : Fin 2 => endpoints (x (if j = 0 then α.1.1 else α.1.2)) s), F p) =
        ∑' p : Fin 2 → Site, F p := by
      symm
      apply tsum_eq_sum
      intro p hp
      dsimp only [F]
      rw [collisionWord_freeProduct_zero_of_not_endpoints s (pairRestrict α x) p hp, zero_mul]
    simp_rw [sum_srwKernel_endpoints]
    rw [hpair]
    simp only [Finset.prod_const_one, mul_one, F]
    have hh := tsum_pairTwo_entrance_constant s (pairRestrict α x) C
    simpa [pairRestrict] using hh
  · intro u hu
    rw [collisionWord_freeProduct_zero_of_not_endpoints s x u hu, zero_mul]

/-- At each fixed pair of durations, the entire entrance/run mass is one
entrance walk kernel multiplied by one scalar renewal mass. -/
theorem tsum_pair_entrance_run_mass {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x : LatticeConfiguration h) :
    (∑' u : LatticeConfiguration h, (∏ i, srwKernel s (u i - x i)) *
      ∑' v : LatticeConfiguration h, collisionWordUndampedPairRunFactor β α r u v) =
      srwKernel (2 * s) (x α.1.2 - x α.1.1) *
        (sigmaSq β * Renewal.renewalMass
          (fun k => sigmaSq β * Renewal.returnWeight k) r) := by
  simp_rw [tsum_pairRunFactor_eq_renewalMass]
  exact tsum_pair_entrance_constant s α x _

end Critical2DKPZ.SHF.Moments
