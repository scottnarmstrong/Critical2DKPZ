/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonPairKernels
public import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
public import Critical2DKPZ.Renewal.PolymerBridge
import Critical2DKPZ.MomentBounds.CCR25HattedInteractionSupport
import Mathlib.Tactic

/-! # Exact row masses of the pair interaction kernels -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

attribute [local instance] Classical.propDecidable

private theorem summable_interacting_row (β : ℝ) (I : ReplicaPartition 4)
    (n : ℕ) (z : LatticeConfiguration 4) :
    Summable (interactingReplicaKernelAbs β I n z) := by
  apply summable_of_ne_finset_zero
    (s := configBox 4 (ccr25ConfigurationCenterSites z) n)
  intro x hx
  exact interactingReplicaKernelAbs_zero_of_not_configBox β I
    (ccr25_mem_configBox_centerSites z) (by simpa only [Nat.zero_add] using hx)

private theorem tsum_two_walk_kernels (n : ℕ) (a b : Site) :
    (∑' p : Site × Site, srwKernel n (p.1 - a) * srwKernel n (p.2 - b)) = 1 := by
  have hs : Summable (fun p : Site × Site => srwKernel n (p.1 - a) * srwKernel n (p.2 - b)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints a n ×ˢ Polymer.endpoints b n)
    intro p hp
    simp only [Finset.mem_product, not_and_or] at hp
    rcases hp with h | h
    · rw [Polymer.srwKernel_eq_zero_of_not_mem n a p.1 h, zero_mul]
    · rw [Polymer.srwKernel_eq_zero_of_not_mem n b p.2 h, mul_zero]
  rw [hs.tsum_prod]
  simp_rw [tsum_mul_left, Polymer.tsum_srwKernel, mul_one]
  exact Polymer.tsum_srwKernel n a

/-- The total pair-interaction row is exactly the scalar renewal mass. The
other two replicas contribute free walk rows of total mass one. -/
theorem tsum_interactingReplicaKernelAbs_disjoint_pair_row
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (n : ℕ) (z : LatticeConfiguration 4) :
    (∑' x : LatticeConfiguration 4, interactingReplicaKernelAbs β (pairPartition α) n z x) =
      if z α.1.1 = z α.1.2 then
        Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) n
      else 0 := by
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
    let K : (Site × Site) × (Site × Site) → ℝ :=
      fun p => interactingReplicaKernelAbs β (pairPartition α) n z (e.symm p)
    have hK : Summable K :=
      (summable_interacting_row β (pairPartition α) n z).comp_injective e.symm.injective
    have hKe (p : (Site × Site) × (Site × Site)) :
        K p = if p.1.1 = p.1.2 then
          Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1.1 - z α.1.1) *
            (srwKernel n (p.2.1 - z δ.1.1) * srwKernel n (p.2.2 - z δ.1.2)) else 0 := by
      dsimp only [K]
      rw [interactingReplicaKernelAbs_disjoint_pairs_eq α δ hd, hc1, hc2, hc3, hc4]
      simp only [hz, true_and]
    have hinner (p : Site × Site) : (∑' q : Site × Site, K (p, q)) =
        if p.1 = p.2 then Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1 - z α.1.1) else 0 := by
      simp_rw [hKe]
      by_cases hp : p.1 = p.2
      · simp only [hp, ite_true]
        rw [tsum_mul_left, tsum_two_walk_kernels, mul_one]
      · simp only [hp, ite_false, tsum_zero]
    have houter : Summable (fun p : Site × Site =>
        if p.1 = p.2 then Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1 - z α.1.1) else 0) :=
      hK.prod.congr hinner
    calc
      _ = ∑' p, K p := (e.symm.tsum_eq _).symm
      _ = ∑' p : Site × Site, ∑' q : Site × Site, K (p, q) := hK.tsum_prod
      _ = ∑' p : Site × Site, if p.1 = p.2 then
          Collision.spatialRenewal (Polymer.sigmaSq β) n (p.1 - z α.1.1) else 0 := tsum_congr hinner
      _ = ∑' x : Site, Collision.spatialRenewal (Polymer.sigmaSq β) n (x - z α.1.1) := by
        rw [houter.tsum_prod]
        simp only [tsum_ite_eq']
      _ = _ := by
        have hshift := (Equiv.subRight (z α.1.1)).tsum_eq
          (Collision.spatialRenewal (Polymer.sigmaSq β) n)
        exact hshift.trans (SHF.Moments.tsum_spatialRenewal_eq_renewalMass _ _)
  · rw [ite_eq_right hz]
    simp_rw [SHF.Moments.interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
      β α n z _ (Or.inl hz), tsum_zero]

/-- At zero Laplace parameter, summing a pair run over all durations up to L
has exactly the free polymer second moment as its row mass. -/
theorem tsum_hattedInteracting_disjoint_pair_row
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (L : ℕ) (z : LatticeConfiguration 4) :
    (∑' x : LatticeConfiguration 4,
      hattedInteractingReplicaKernelAbs L 0 β (pairPartition α) z x) =
      if z α.1.1 = z α.1.2 then Renewal.freeSecondMoment β L else 0 := by
  have he (x : LatticeConfiguration 4) :
      hattedInteractingReplicaKernelAbs L 0 β (pairPartition α) z x =
        ∑ m ∈ Finset.range (L + 1), interactingReplicaKernelAbs β (pairPartition α) m z x := by
    rw [Finset.sum_range_succ']
    have hzero : interactingReplicaKernelAbs β (pairPartition α) 0 z x =
        if z = x ∧ IsCollisionConfiguration (pairPartition α) x then 1 else 0 := by
      rw [interactingReplicaKernelAbs]
    simp only [hattedInteractingReplicaKernelAbs, zero_mul, neg_zero, Real.exp_zero, one_mul, hzero]
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun m _ => summable_interacting_row β (pairPartition α) m z)]
  simp_rw [tsum_interactingReplicaKernelAbs_disjoint_pair_row α δ hd]
  by_cases hz : z α.1.1 = z α.1.2
  · simp only [hz, ite_true]
    rw [Renewal.sum_renewalMass_range, Renewal.freeSecondMoment_eq_renewalFunction]
    rfl
  · simp only [hz, ite_false, Finset.sum_const_zero]

/-- The finite pair-interaction row is bounded uniformly in the configuration
by the free second moment at its time cutoff. -/
theorem sum_hattedInteracting_disjoint_pair_row_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (L : ℕ) (S : Finset (LatticeConfiguration 4)) (z : LatticeConfiguration 4) :
    (∑ x ∈ S, hattedInteractingReplicaKernelAbs L 0 β (pairPartition α) z x) ≤
      Renewal.freeSecondMoment β L := by
  have hsum : Summable (hattedInteractingReplicaKernelAbs L 0 β (pairPartition α) z) := by
    apply summable_of_ne_finset_zero
      (s := configBox 4 (ccr25ConfigurationCenterSites z) L)
    intro x hx
    exact hattedInteractingReplicaKernelAbs_zero_of_not_configBox 0 β (pairPartition α)
      (ccr25_mem_configBox_centerSites z) (by simpa only [Nat.zero_add] using hx)
  have hle := hsum.sum_le_tsum S (fun x _ =>
    hattedInteractingReplicaKernelAbs_nonneg L 0 β (pairPartition α) z x)
  rw [tsum_hattedInteracting_disjoint_pair_row α δ hd] at hle
  by_cases hz : z α.1.1 = z α.1.2
  · simpa only [hz, ite_true] using hle
  · simp only [hz, ite_false] at hle
    exact hle.trans (integral_nonneg (fun _ => sq_nonneg _))

end Critical2DKPZ.Extensions.GffTangent
