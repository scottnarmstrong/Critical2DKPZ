/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25IndependentDurationSum
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Critical2DKPZ.MomentBounds.CCR25RunExpansionBase
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Tactic

/-! # The free replica semigroup through the unrestricted stratum -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem collisionConfig_bot_freeKernel {h : ℕ}
    (z : LatticeConfiguration h) : IsCollisionConfiguration (⊥ : ReplicaPartition h) z := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg z hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

private theorem replicaWalk_kernel_zero_of_not_endpoints {h : ℕ}
    (m : ℕ) (J : ReplicaPartition h) (y x : LatticeConfiguration h)
    (hy : y ∉ Fintype.piFinset
      (fun i : Fin h => Critical2DKPZ.Polymer.endpoints (x i) m)) :
    freeReplicaKernel m ⊥ J y x = 0 := by
  have hmissing : ∃ i : Fin h,
      y i ∉ Critical2DKPZ.Polymer.endpoints (x i) m := by
    by_contra hnot
    apply hy
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmissing
  have hq : Critical2DKPZ.srwKernel m (x i - y i) = 0 := by
    rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem m (x i) (y i) hi
  have hprod : (∏ j : Fin h, Critical2DKPZ.srwKernel m (x j - y j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hq
  simp [freeReplicaKernel, collisionConfig_bot_freeKernel, hprod]

private def replicaEndpointConfigurations {h : ℕ} (n : ℕ)
    (z : LatticeConfiguration h) : Finset (LatticeConfiguration h) :=
  Fintype.piFinset fun i : Fin h => Critical2DKPZ.Polymer.endpoints (z i) n

private theorem freeReplicaKernel_zero_of_not_endpoint_targets {h : ℕ}
    (n : ℕ) (I J : ReplicaPartition h) (z y : LatticeConfiguration h)
    (hy : y ∉ replicaEndpointConfigurations n z) :
    freeReplicaKernel n I J z y = 0 := by
  have hmissing : ∃ i : Fin h,
      y i ∉ Critical2DKPZ.Polymer.endpoints (z i) n := by
    by_contra hnot
    apply hy
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmissing
  have hq : Critical2DKPZ.srwKernel n (y i - z i) = 0 := by
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem n (z i) (y i) hi
  have hprod : (∏ j : Fin h, Critical2DKPZ.srwKernel n (y j - z j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hq
  simp [freeReplicaKernel, hprod]

private theorem srwKernel_endpoint_convolution (n m : ℕ) (z x : Site) :
    (∑ y ∈ Critical2DKPZ.Polymer.endpoints x m,
      Critical2DKPZ.srwKernel n (y - z) *
        Critical2DKPZ.srwKernel m (x - y)) =
      Critical2DKPZ.srwKernel (n + m) (x - z) := by
  calc
    _ = ∑' y : Site,
        Critical2DKPZ.srwKernel n (y - z) *
          Critical2DKPZ.srwKernel m (x - y) := by
      symm
      apply tsum_eq_sum
      intro y hy
      have hzero : Critical2DKPZ.srwKernel m (x - y) = 0 := by
        rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
        exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem m x y hy
      rw [hzero]
      simp
    _ = Critical2DKPZ.srwKernel (n + m) (x - z) := by
      simpa using (Critical2DKPZ.Polymer.srwKernel_convolution n m z x).symm

/-- Summing over an intermediate unrestricted configuration adds two free
replica durations while preserving the endpoint collision constraints. -/
theorem freeReplicaKernel_comp_bot {h : ℕ} (n m : ℕ)
    (I J : ReplicaPartition h) (z x : LatticeConfiguration h) :
    (∑' y : LatticeConfiguration h,
      freeReplicaKernel n I ⊥ z y *
        freeReplicaKernel m ⊥ J y x) =
      freeReplicaKernel (n + m) I J z x := by
  classical
  let D : Fin h → Finset Site :=
    fun i => Critical2DKPZ.Polymer.endpoints (x i) m
  let S : Finset (LatticeConfiguration h) := Fintype.piFinset D
  have hzero (y : LatticeConfiguration h) (hy : y ∉ S) :
      freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x = 0 := by
    rw [replicaWalk_kernel_zero_of_not_endpoints m J y x (by simpa [S, D] using hy)]
    ring
  have hpoint (y : LatticeConfiguration h)
      (hz : IsCollisionConfiguration I z)
      (hx : IsCollisionConfiguration J x) :
      freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x =
        ∏ i : Fin h,
          (Critical2DKPZ.srwKernel n (y i - z i) *
            Critical2DKPZ.srwKernel m (x i - y i)) := by
    simp [freeReplicaKernel, collisionConfig_bot_freeKernel, hz, hx]
    rw [← Finset.prod_mul_distrib]
  have hsumProd :
      (∑ y ∈ S, ∏ i : Fin h,
        (Critical2DKPZ.srwKernel n (y i - z i) *
          Critical2DKPZ.srwKernel m (x i - y i))) =
        ∏ i : Fin h, ∑ y ∈ D i,
          (Critical2DKPZ.srwKernel n (y - z i) *
            Critical2DKPZ.srwKernel m (x i - y)) := by
    simpa [S, D] using
      finite_sum_product_over_piFinset_eq_product_sums D
        (fun i y => Critical2DKPZ.srwKernel n (y - z i) *
          Critical2DKPZ.srwKernel m (x i - y))
  by_cases hz : IsCollisionConfiguration I z <;>
    by_cases hx : IsCollisionConfiguration J x
  · calc
      (∑' y : LatticeConfiguration h,
          freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) =
          ∑ y ∈ S,
            freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x :=
        tsum_eq_sum (s := S) hzero
      _ = ∑ y ∈ S, ∏ i : Fin h,
            (Critical2DKPZ.srwKernel n (y i - z i) *
              Critical2DKPZ.srwKernel m (x i - y i)) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hpoint y hz hx
      _ = ∏ i : Fin h, Critical2DKPZ.srwKernel (n + m) (x i - z i) := by
        rw [hsumProd]
        apply Finset.prod_congr rfl
        intro i hi
        exact srwKernel_endpoint_convolution n m (z i) (x i)
      _ = freeReplicaKernel (n + m) I J z x := by
        simp [freeReplicaKernel, hz, hx]
  · simp [freeReplicaKernel, hz, hx]
  · simp [freeReplicaKernel, hz, hx]
  · simp [freeReplicaKernel, hz, hx]



/-! The next lemma is the operator form of the same identity: unlike the
pointwise semigroup equation, it permits a continuation depending on the
intermediate endpoint. -/

/-- Free replica kernels compose against an arbitrary continuation. The sums
are finite-support sums: the intermediate endpoint is in the `n`-step box,
and the final endpoint is in the finite union of the following `m`-step boxes. -/
theorem freeReplicaKernel_comp_bot_mul_tsum {h : ℕ} (n m : ℕ)
    (I J : ReplicaPartition h) (z : LatticeConfiguration h)
    (f : LatticeConfiguration h → ℝ) :
    (∑' y : LatticeConfiguration h,
      freeReplicaKernel n I ⊥ z y *
        (∑' x : LatticeConfiguration h,
          freeReplicaKernel m ⊥ J y x * f x)) =
      ∑' x : LatticeConfiguration h,
        freeReplicaKernel (n + m) I J z x * f x := by
  classical
  let S := replicaEndpointConfigurations n z
  let U := S.biUnion fun y => replicaEndpointConfigurations m y
  have hfirst (y : LatticeConfiguration h) (hy : y ∉ S) :
      freeReplicaKernel n I ⊥ z y = 0 := by
    exact freeReplicaKernel_zero_of_not_endpoint_targets n I ⊥ z y
      (by simpa [S] using hy)
  have hsecond (y x : LatticeConfiguration h) (hy : y ∈ S) (hx : x ∉ U) :
      freeReplicaKernel m ⊥ J y x = 0 := by
    exact freeReplicaKernel_zero_of_not_endpoint_targets m ⊥ J y x (by
      intro hxEnd
      apply hx
      exact Finset.mem_biUnion.mpr ⟨y, hy, by
        simpa [replicaEndpointConfigurations] using hxEnd⟩)
  have hleft :
      (∑' y : LatticeConfiguration h,
        freeReplicaKernel n I ⊥ z y *
          (∑' x : LatticeConfiguration h,
            freeReplicaKernel m ⊥ J y x * f x)) =
        ∑ y ∈ S,
          freeReplicaKernel n I ⊥ z y *
            (∑ x ∈ U, freeReplicaKernel m ⊥ J y x * f x) := by
    rw [tsum_eq_sum (s := S) (fun y hy => by rw [hfirst y hy]; simp)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [tsum_eq_sum (s := U) (fun x hx => by rw [hsecond y x hy hx]; simp)]
  have hswap :
      (∑ y ∈ S,
        freeReplicaKernel n I ⊥ z y *
          (∑ x ∈ U, freeReplicaKernel m ⊥ J y x * f x)) =
        ∑ x ∈ U,
          (∑ y ∈ S,
            freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) * f x := by
    calc
      _ = ∑ y ∈ S, ∑ x ∈ U,
            (freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) * f x := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ x ∈ U, ∑ y ∈ S,
            (freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) * f x := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ U,
            (∑ y ∈ S,
              freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) * f x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
  have hcomp (x : LatticeConfiguration h) :
      (∑ y ∈ S,
        freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) =
        freeReplicaKernel (n + m) I J z x := by
    have hsum :
        (∑' y : LatticeConfiguration h,
          freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) =
          ∑ y ∈ S,
            freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x :=
      tsum_eq_sum (s := S) (fun y hy => by rw [hfirst y hy]; simp)
    rw [← hsum]
    exact freeReplicaKernel_comp_bot n m I J z x
  have hzero (x : LatticeConfiguration h) (hx : x ∉ U) :
      freeReplicaKernel (n + m) I J z x = 0 := by
    rw [← hcomp x]
    apply Finset.sum_eq_zero
    intro y hy
    rw [hsecond y x hy hx]
    ring
  calc
    _ = ∑ x ∈ U,
        (∑ y ∈ S,
          freeReplicaKernel n I ⊥ z y * freeReplicaKernel m ⊥ J y x) * f x :=
      hleft.trans hswap
    _ = ∑ x ∈ U, freeReplicaKernel (n + m) I J z x * f x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hcomp]
    _ = ∑' x : LatticeConfiguration h,
        freeReplicaKernel (n + m) I J z x * f x := by
      exact (tsum_eq_sum (s := U)
        (fun x hx => by rw [hzero x hx]; simp)).symm

/-- An inactive prefix in a collision sequence collapses to one free
replica kernel before the first active collision, leaving the remaining path
weight as an arbitrary continuation. -/
theorem replicaPathWeight_inactive_prefix {h : ℕ} (k : ℕ)
    (I : ReplicaPartition h) (Is : List (ReplicaPartition h))
    (z : LatticeConfiguration h) :
    replicaPathWeight (List.replicate k ⊥ ++ I :: Is) z =
      ∑' x : LatticeConfiguration h,
        freeReplicaKernel (k + 1) ⊥ I z x * replicaPathWeight Is x := by
  induction k generalizing z with
  | zero =>
      simp [replicaPathWeight, replicaStepKernel]
  | succ k ih =>
      have hlist : List.replicate (k + 1) (⊥ : ReplicaPartition h) ++ I :: Is =
          (⊥ : ReplicaPartition h) :: (List.replicate k ⊥ ++ I :: Is) := by
        simp [List.replicate_succ]
      rw [hlist, replicaPathWeight]
      change (∑' y : LatticeConfiguration h,
        freeReplicaKernel 1 ⊥ ⊥ z y *
          replicaPathWeight (List.replicate k ⊥ ++ I :: Is) y) = _
      rw [show replicaPathWeight (List.replicate k ⊥ ++ I :: Is) =
          fun y => ∑' x : LatticeConfiguration h,
            freeReplicaKernel (k + 1) ⊥ I y x * replicaPathWeight Is x by
        funext y
        exact ih y]
      simpa only [show 1 + (k + 1) = k + 2 by omega] using
        (freeReplicaKernel_comp_bot_mul_tsum 1 (k + 1) ⊥ I z
          (replicaPathWeight Is))

/-- At a collision configuration for `I`, the starting `I` restriction on a
free kernel is redundant relative to the unrestricted bottom stratum. -/
theorem freeReplicaKernel_bot_start_eq_of_collision {h : ℕ} (n : ℕ)
    (I J : ReplicaPartition h) (z x : LatticeConfiguration h)
    (hz : IsCollisionConfiguration I z) :
    freeReplicaKernel n ⊥ J z x = freeReplicaKernel n I J z x := by
  classical
  change (if IsCollisionConfiguration (⊥ : ReplicaPartition h) z ∧
      IsCollisionConfiguration J x then
        ∏ i : Fin h, Critical2DKPZ.srwKernel n (x i - z i) else 0) =
    (if IsCollisionConfiguration I z ∧ IsCollisionConfiguration J x then
      ∏ i : Fin h, Critical2DKPZ.srwKernel n (x i - z i) else 0)
  by_cases hx : IsCollisionConfiguration J x
  · rw [ite_eq_left ⟨collisionConfig_bot_freeKernel z, hx⟩,
      ite_eq_left ⟨hz, hx⟩]
  · rw [ite_eq_right (by rintro ⟨_, hJ⟩; exact hx hJ),
      ite_eq_right (by rintro ⟨_, hJ⟩; exact hx hJ)]



end Critical2DKPZ.MomentBounds
