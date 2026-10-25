/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonPairRowMass
import Critical2DKPZ.MomentBounds.CCR25HattedInteractionSupport
import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Exact action of a pair run on the two spectator coordinates -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- An arbitrary function of the spectator pair evolves by two independent
walks through a collision run. Its colliding pair contributes only its scalar
renewal mass. Finite walk support ensures summability without a bound on V. -/
theorem tsum_interacting_pair_mul_spectators
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (n : ℕ) (z : LatticeConfiguration 4) (V : Site × Site → ℝ) :
    (∑' x : LatticeConfiguration 4,
      interactingReplicaKernelAbs β (pairPartition α) n z x * V (x δ.1.1, x δ.1.2)) =
      if z α.1.1 = z α.1.2 then
        Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) n *
          ∑' q : Site × Site,
            (srwKernel n (q.1 - z δ.1.1) * srwKernel n (q.2 - z δ.1.2)) * V q
      else 0 := by
  have hs : Summable (fun x : LatticeConfiguration 4 =>
      interactingReplicaKernelAbs β (pairPartition α) n z x * V (x δ.1.1, x δ.1.2)) := by
    apply summable_of_ne_finset_zero
      (s := configBox 4 (ccr25ConfigurationCenterSites z) n)
    intro x hx
    rw [interactingReplicaKernelAbs_zero_of_not_configBox β (pairPartition α)
      (ccr25_mem_configBox_centerSites z) (by simpa only [Nat.zero_add] using hx), zero_mul]
  by_cases hz : z α.1.1 = z α.1.2
  · rw [ite_eq_left hz]
    let e := disjointPairConfigurationEquiv α δ hd
    have hc1 (p : (Site × Site) × (Site × Site)) : e.symm p α.1.1 = p.1.1 :=
      congrArg (fun q : (Site × Site) × (Site × Site) => q.1.1) (e.apply_symm_apply p)
    have hc2 (p : (Site × Site) × (Site × Site)) : e.symm p α.1.2 = p.1.2 :=
      congrArg (fun q : (Site × Site) × (Site × Site) => q.1.2) (e.apply_symm_apply p)
    have hc3 (p : (Site × Site) × (Site × Site)) : e.symm p δ.1.1 = p.2.1 :=
      congrArg (fun q : (Site × Site) × (Site × Site) => q.2.1) (e.apply_symm_apply p)
    have hc4 (p : (Site × Site) × (Site × Site)) : e.symm p δ.1.2 = p.2.2 :=
      congrArg (fun q : (Site × Site) × (Site × Site) => q.2.2) (e.apply_symm_apply p)
    let Q : ℝ := ∑' q : Site × Site,
      (srwKernel n (q.1 - z δ.1.1) * srwKernel n (q.2 - z δ.1.2)) * V q
    let K : (Site × Site) × (Site × Site) → ℝ := fun p =>
      interactingReplicaKernelAbs β (pairPartition α) n z (e.symm p) *
        V (e.symm p δ.1.1, e.symm p δ.1.2)
    have hK : Summable K := hs.comp_injective e.symm.injective
    have hKe (p : (Site × Site) × (Site × Site)) : K p =
        if p.1.1 = p.1.2 then
          Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1.1 - z α.1.1) *
            ((srwKernel n (p.2.1 - z δ.1.1) * srwKernel n (p.2.2 - z δ.1.2)) * V p.2)
        else 0 := by
      dsimp only [K]
      rw [interactingReplicaKernelAbs_disjoint_pairs_eq α δ hd, hc1, hc2, hc3, hc4]
      simp only [hz, true_and]
      split_ifs <;> simp only [mul_assoc, zero_mul, Prod.mk.eta]
    have hinner (p : Site × Site) : (∑' q : Site × Site, K (p, q)) =
        if p.1 = p.2 then Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1 - z α.1.1) * Q
        else 0 := by
      simp_rw [hKe]
      by_cases hp : p.1 = p.2
      · simp only [hp, ite_true, tsum_mul_left]
        rfl
      · simp only [hp, ite_false, tsum_zero]
    have houter : Summable (fun p : Site × Site =>
        if p.1 = p.2 then Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1 - z α.1.1) * Q
        else 0) := hK.prod.congr hinner
    calc
      _ = ∑' p, K p := (e.symm.tsum_eq _).symm
      _ = ∑' p : Site × Site, ∑' q : Site × Site, K (p, q) := hK.tsum_prod
      _ = ∑' p : Site × Site, if p.1 = p.2 then
          Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1 - z α.1.1) * Q else 0 := tsum_congr hinner
      _ = (∑' x : Site, Collision.spatialRenewal (Polymer.sigmaSq β) n (x - z α.1.1)) * Q := by
        rw [houter.tsum_prod]
        simp only [tsum_ite_eq', tsum_mul_right]
      _ = _ := by
        have hshift := (Equiv.subRight (z α.1.1)).tsum_eq
          (Collision.spatialRenewal (Polymer.sigmaSq β) n)
        exact congrArg (· * Q) (hshift.trans (SHF.Moments.tsum_spatialRenewal_eq_renewalMass _ _))
  · rw [ite_eq_right hz]
    simp_rw [SHF.Moments.interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
      β α n z _ (Or.inl hz), zero_mul, tsum_zero]

private theorem tsum_walk_pair_potential (n k : ℕ) (a b : Site) :
    (∑' q : Site × Site, (srwKernel n (q.1 - a) * srwKernel n (q.2 - b)) *
      srwKernel k (q.2 - q.1)) = srwKernel (2 * n + k) (b - a) := by
  calc
    _ = ∑ q ∈ Polymer.endpoints a n ×ˢ Polymer.endpoints b n,
        (srwKernel n (q.1 - a) * srwKernel n (q.2 - b)) * srwKernel k (q.2 - q.1) := by
      apply tsum_eq_sum
      intro q hq
      simp only [Finset.mem_product, not_and_or] at hq
      rcases hq with h | h
      · rw [Polymer.srwKernel_eq_zero_of_not_mem n a q.1 h, zero_mul, zero_mul]
      · rw [Polymer.srwKernel_eq_zero_of_not_mem n b q.2 h, mul_zero, zero_mul]
    _ = _ := by
      rw [Finset.sum_product]
      exact Polymer.kernel_sandwich n k a b

/-- A collision probability of the spectator pair is propagated by adding the
run duration to its free heat time, while the interacting pair pays its exact
scalar renewal mass. -/
theorem tsum_interacting_pair_mul_pair_kernel
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (n k : ℕ) (z : LatticeConfiguration 4) :
    (∑' x : LatticeConfiguration 4,
      interactingReplicaKernelAbs β (pairPartition α) n z x *
        srwKernel k (x δ.1.2 - x δ.1.1)) =
      if z α.1.1 = z α.1.2 then
        Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) n *
          srwKernel (2 * n + k) (z δ.1.2 - z δ.1.1)
      else 0 := by
  have h := tsum_interacting_pair_mul_spectators α δ hd β n z
    (fun q => srwKernel k (q.2 - q.1))
  simpa only [tsum_walk_pair_potential] using h

end Critical2DKPZ.Extensions.GffTangent
