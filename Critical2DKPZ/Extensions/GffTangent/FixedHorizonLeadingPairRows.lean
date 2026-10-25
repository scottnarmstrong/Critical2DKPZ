/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonPairBoundary
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonPairSpectators
import Critical2DKPZ.MomentBounds.CCR25HattedInteractionSupport
import Mathlib.Tactic

/-! # Finite row bounds for the leading two disjoint interaction runs -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Restricting the free row to a finite cutoff cannot increase its exact
spectator collision probability. -/
theorem sum_freeReplicaKernel_disjoint_pairs_le (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (n : ℕ) (s : Finset (LatticeConfiguration 4)) (z : LatticeConfiguration 4) :
    (∑ x ∈ s, freeReplicaKernel n (pairPartition α) (pairPartition δ) z x) ≤
      srwKernel (2 * n) (z δ.1.2 - z δ.1.1) := by
  have hs : Summable (freeReplicaKernel n (pairPartition α) (pairPartition δ) z) := by
    apply summable_of_ne_finset_zero
      (s := configBox 4 (ccr25ConfigurationCenterSites z) n)
    intro x hx
    exact freeReplicaKernel_zero_of_not_configBox (ccr25_mem_configBox_centerSites z)
      (by simpa only [Nat.zero_add] using hx) _ _
  have hle := hs.sum_le_tsum s (fun x _ => freeReplicaKernel_nonneg n _ _ z x)
  rw [tsum_freeReplicaKernel_disjoint_pairs α δ hd] at hle
  by_cases hz : z α.1.1 = z α.1.2
  · simpa only [hz, ite_true] using hle
  · simp only [hz, ite_false] at hle
    exact hle.trans (Polymer.kernel_nonneg _ _)

/-- Restricting a pair-interaction row tested against a spectator collision
probability costs at most its scalar renewal mass times the evolved kernel. -/
theorem sum_interacting_pair_mul_pair_kernel_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (d g : ℕ) (s : Finset (LatticeConfiguration 4)) (z : LatticeConfiguration 4) :
    (∑ x ∈ s, interactingReplicaKernelAbs β (pairPartition α) d z x *
      srwKernel (2 * g) (x δ.1.2 - x δ.1.1)) ≤
      Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) d *
        srwKernel (2 * (d + g)) (z δ.1.2 - z δ.1.1) := by
  have hs : Summable (fun x : LatticeConfiguration 4 =>
      interactingReplicaKernelAbs β (pairPartition α) d z x *
        srwKernel (2 * g) (x δ.1.2 - x δ.1.1)) := by
    apply summable_of_ne_finset_zero
      (s := configBox 4 (ccr25ConfigurationCenterSites z) d)
    intro x hx
    rw [interactingReplicaKernelAbs_zero_of_not_configBox β (pairPartition α)
      (ccr25_mem_configBox_centerSites z) (by simpa only [Nat.zero_add] using hx), zero_mul]
  have hle := hs.sum_le_tsum s (fun x _ => mul_nonneg
    (interactingReplicaKernelAbs_nonneg β (pairPartition α) d z x) (Polymer.kernel_nonneg _ _))
  rw [tsum_interacting_pair_mul_pair_kernel α δ hd] at hle
  have hclock : 2 * d + 2 * g = 2 * (d + g) := by omega
  rw [hclock] at hle
  by_cases hz : z α.1.1 = z α.1.2
  · simpa only [hz, ite_true] using hle
  · simp only [hz, ite_false] at hle
    exact hle.trans (mul_nonneg (Renewal.renewalMass_nonneg (fun r =>
      mul_nonneg (sigmaSq_nonneg β) (Critical2DKPZ.srwKernel_nonneg _ _)) _)
        (Polymer.kernel_nonneg _ _))

/-- A first boundary, one interaction run and the next free interval have a
uniform finite-volume bound. The initial profile contributes two quadratic
energy factors, rather than an operator norm losing a window-length factor. -/
theorem sum_boundary_pair_run_free_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (n d g : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4)) :
    (∑ x ∈ s, replicaBoundaryVector n (pairPartition α) S φ x *
      (∑ y ∈ s, interactingReplicaKernelAbs β (pairPartition α) d x y *
        (∑ z ∈ s, freeReplicaKernel g (pairPartition α) (pairPartition δ) y z))) ≤
      Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) d *
        (B * ∑ y ∈ S, φ y) ^ 2 := by
  let R := Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) d
  have hR : 0 ≤ R := Renewal.renewalMass_nonneg (fun r =>
    mul_nonneg (sigmaSq_nonneg β) (Critical2DKPZ.srwKernel_nonneg _ _)) _
  calc
    _ ≤ ∑ x ∈ s, replicaBoundaryVector n (pairPartition α) S φ x *
        (∑ y ∈ s, interactingReplicaKernelAbs β (pairPartition α) d x y *
          srwKernel (2 * g) (y δ.1.2 - y δ.1.1)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (replicaBoundaryVector_nonneg n _ S φ hφ x)
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (sum_freeReplicaKernel_disjoint_pairs_le α δ hd g s y)
        (interactingReplicaKernelAbs_nonneg β (pairPartition α) d x y)
    _ ≤ ∑ x ∈ s, replicaBoundaryVector n (pairPartition α) S φ x *
        (R * srwKernel (2 * (d + g)) (x δ.1.2 - x δ.1.1)) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (sum_interacting_pair_mul_pair_kernel_le α δ hd β d g s x)
        (replicaBoundaryVector_nonneg n _ S φ hφ x)
    _ = R * ∑ x ∈ s, replicaBoundaryVector n (pairPartition α) S φ x *
        srwKernel (2 * (d + g)) (x δ.1.2 - x δ.1.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ R * (B * ∑ y ∈ S, φ y) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (sum_replicaBoundaryVector_mul_pair_kernel_le α δ hd n (d + g) S φ hB hφ hφB s) hR

end Critical2DKPZ.Extensions.GffTangent
