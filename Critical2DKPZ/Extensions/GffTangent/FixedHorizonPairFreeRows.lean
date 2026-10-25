/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonPairKernels
import Critical2DKPZ.MomentBounds.CCR25HattedInteractionSupport
import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Exact free transition rows between the disjoint pair strata -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A summable product of observables of two disjoint coordinate pairs factors
into the corresponding two sums. -/
theorem tsum_disjointPair_product (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (A B : Site × Site → ℝ)
    (hs : Summable (fun x : LatticeConfiguration 4 =>
      A (x α.1.1, x α.1.2) * B (x δ.1.1, x δ.1.2))) :
    (∑' x : LatticeConfiguration 4, A (x α.1.1, x α.1.2) * B (x δ.1.1, x δ.1.2)) =
      (∑' p : Site × Site, A p) * (∑' q : Site × Site, B q) := by
  let e := disjointPairConfigurationEquiv α δ hd
  have hc (p : (Site × Site) × (Site × Site)) :
      A (e.symm p α.1.1, e.symm p α.1.2) * B (e.symm p δ.1.1, e.symm p δ.1.2) =
        A p.1 * B p.2 := by
    change A (e (e.symm p)).1 * B (e (e.symm p)).2 = _
    rw [e.apply_symm_apply]
  have hK : Summable (fun p : (Site × Site) × (Site × Site) => A p.1 * B p.2) :=
    (hs.comp_injective e.symm.injective).congr hc
  calc
    _ = ∑' p : (Site × Site) × (Site × Site), A p.1 * B p.2 :=
      (e.symm.tsum_eq _).symm.trans (tsum_congr hc)
    _ = _ := by
      rw [hK.tsum_prod]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]

private theorem summable_walk_pair_product (n : ℕ) (a b : Site) :
    Summable (fun p : Site × Site => srwKernel n (p.1 - a) * srwKernel n (p.2 - b)) := by
  apply summable_of_ne_finset_zero (s := Polymer.endpoints a n ×ˢ Polymer.endpoints b n)
  intro p hp
  simp only [Finset.mem_product, not_and_or] at hp
  rcases hp with h | h
  · rw [Polymer.srwKernel_eq_zero_of_not_mem n a p.1 h, zero_mul]
  · rw [Polymer.srwKernel_eq_zero_of_not_mem n b p.2 h, mul_zero]

private theorem tsum_walk_pair_product (n : ℕ) (a b : Site) :
    (∑' p : Site × Site, srwKernel n (p.1 - a) * srwKernel n (p.2 - b)) = 1 := by
  rw [(summable_walk_pair_product n a b).tsum_prod]
  simp_rw [tsum_mul_left, Polymer.tsum_srwKernel, mul_one]
  exact Polymer.tsum_srwKernel n a

private theorem tsum_walk_pair_diagonal (n : ℕ) (a b : Site) :
    (∑' q : Site × Site, if q.1 = q.2 then
      srwKernel n (q.1 - a) * srwKernel n (q.2 - b) else 0) = srwKernel (2 * n) (b - a) := by
  have hs : Summable (fun q : Site × Site => if q.1 = q.2 then
      srwKernel n (q.1 - a) * srwKernel n (q.2 - b) else 0) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints a n ×ˢ Polymer.endpoints b n)
    intro q hq
    split_ifs with hdiag
    · simp only [Finset.mem_product, not_and_or] at hq
      rcases hq with h | h
      · rw [Polymer.srwKernel_eq_zero_of_not_mem n a q.1 h, zero_mul]
      · rw [Polymer.srwKernel_eq_zero_of_not_mem n b q.2 h, mul_zero]
    · rfl
  rw [hs.tsum_prod]
  simp only [tsum_ite_eq']
  have hconv := (Polymer.srwKernel_convolution n n a b).symm
  rw [show n + n = 2 * n by omega] at hconv
  apply Eq.trans _ hconv
  apply tsum_congr
  intro x
  rw [Polymer.srwKernel_sub_swap n b x]

/-- The row of a free interval ending in the other collision pair is exactly
that pair's collision probability. -/
theorem tsum_freeReplicaKernel_disjoint_pairs (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (n : ℕ) (z : LatticeConfiguration 4) :
    (∑' x : LatticeConfiguration 4, freeReplicaKernel n (pairPartition α) (pairPartition δ) z x) =
      if z α.1.1 = z α.1.2 then srwKernel (2 * n) (z δ.1.2 - z δ.1.1) else 0 := by
  have hs : Summable (freeReplicaKernel n (pairPartition α) (pairPartition δ) z) := by
    apply summable_of_ne_finset_zero
      (s := configBox 4 (ccr25ConfigurationCenterSites z) n)
    intro x hx
    exact freeReplicaKernel_zero_of_not_configBox (ccr25_mem_configBox_centerSites z)
      (by simpa only [Nat.zero_add] using hx) _ _
  by_cases hz : z α.1.1 = z α.1.2
  · rw [ite_eq_left hz]
    let A : Site × Site → ℝ := fun p => srwKernel n (p.1 - z α.1.1) * srwKernel n (p.2 - z α.1.2)
    let B : Site × Site → ℝ := fun q => if q.1 = q.2 then
      srwKernel n (q.1 - z δ.1.1) * srwKernel n (q.2 - z δ.1.2) else 0
    have he (x : LatticeConfiguration 4) : freeReplicaKernel n (pairPartition α) (pairPartition δ) z x =
        A (x α.1.1, x α.1.2) * B (x δ.1.1, x δ.1.2) := by
      rw [freeReplicaKernel_disjoint_pairs_eq α δ hd]
      simp only [hz, true_and, A, B]
      split_ifs <;> simp only [mul_zero]
    calc
      _ = ∑' x : LatticeConfiguration 4, A (x α.1.1, x α.1.2) * B (x δ.1.1, x δ.1.2) := tsum_congr he
      _ = (∑' p, A p) * (∑' q, B q) := tsum_disjointPair_product α δ hd A B (hs.congr he)
      _ = _ := by rw [tsum_walk_pair_product, tsum_walk_pair_diagonal, one_mul]
  · rw [ite_eq_right hz]
    simp_rw [freeReplicaKernel_disjoint_pairs_eq α δ hd]
    simp only [hz, false_and, ite_false, tsum_zero]

end Critical2DKPZ.Extensions.GffTangent
