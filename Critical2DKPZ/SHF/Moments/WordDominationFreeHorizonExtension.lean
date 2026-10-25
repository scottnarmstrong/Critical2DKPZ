/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationDampedPathRecursion
public import Critical2DKPZ.SHF.Moments.WordDominationFreeDurationSum
import Mathlib.Tactic

/-! # Summed terminal free horizon -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

private theorem collisionWord_horizon_bottom_collision_config {h : ℕ}
    (x : LatticeConfiguration h) : IsCollisionConfiguration (⊥ : ReplicaPartition h) x := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg x hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

private theorem collisionWord_sum_shifted_durations {K n : ℕ} (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, f (n + k + 1)) =
      ∑ d ∈ Finset.Icc (n + 1) (n + K), f d := by
  classical
  apply Finset.sum_bij (fun k _ => n + k + 1)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk j hj hEq
    simp only [Finset.mem_range] at hk hj
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d - (n + 1), Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  · intro k hk
    rfl

/-- Summing free terminal durations over a common horizon is bounded by one time-summed free transition. -/
theorem collisionWord_freeHorizonExtension_le_hattedFree
    {h n K L : ℕ} (hK : 1 ≤ K) (hcut : n + K ≤ L)
    (β lam : ℝ) (hlam : 0 ≤ lam) (previous : ReplicaPartition h)
    (x y : LatticeConfiguration h)
    (hstart : IsCollisionConfiguration previous x) :
    (∑ k ∈ Finset.range K,
      ∑' z : LatticeConfiguration h,
        blockWordKernel (sigmaSq β) [] n x z *
          ∏ i, srwKernel (k + 1) (y i - z i)) ≤
      Real.exp ((lam / (L : ℝ)) * ((n + K : ℕ) : ℝ)) *
        hattedFreeReplicaKernel L previous ⊥ x y := by
  have hL : 1 ≤ L := by omega
  have hconv (k : ℕ) :
      (∑' z : LatticeConfiguration h,
        blockWordKernel (sigmaSq β) [] n x z *
          ∏ i, srwKernel (k + 1) (y i - z i)) =
        freeReplicaKernel (n + k + 1) previous ⊥ x y := by
    rw [blockWordKernel_nil_append_free]
    have hblock :
        blockWordKernel (sigmaSq β) [] (n + (k + 1)) x y =
          freeReplicaKernel (n + (k + 1)) ⊥ ⊥ x y := by
      simp [blockWordKernel, freeReplicaKernel,
        collisionWord_horizon_bottom_collision_config]
    rw [hblock]
    have hEq := freeReplicaKernel_bot_start_eq_of_collision
      (n + (k + 1)) previous ⊥ x y hstart
    simpa [Nat.add_assoc] using hEq
  have hshift :
      (∑ k ∈ Finset.range K,
        freeReplicaKernel (n + k + 1) previous ⊥ x y) =
        ∑ d ∈ Finset.Icc (n + 1) (n + K),
          freeReplicaKernel d previous ⊥ x y := by
    exact collisionWord_sum_shifted_durations
      (n := n) (K := K) (fun d => freeReplicaKernel d previous ⊥ x y)
  have hsubset : Finset.Icc (n + 1) (n + K) ⊆ Finset.Icc 1 L := by
    intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  have hnonneg (d : ℕ) :
      0 ≤ freeReplicaKernel d previous ⊥ x y :=
    freeReplicaKernel_nonneg d previous ⊥ x y
  have hsum :
      (∑ d ∈ Finset.Icc (n + 1) (n + K),
        freeReplicaKernel d previous ⊥ x y) ≤
      hattedFreeReplicaKernel L previous ⊥ x y := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 L,
          freeReplicaKernel d previous ⊥ x y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro d hd hnot
          exact hnonneg d)
      _ ≤ hattedFreeReplicaKernel L previous ⊥ x y :=
        collisionWord_freeReplicaKernel_duration_sum_le (n := L) (L := L) le_rfl
          previous ⊥ x y
  have hκ : 0 ≤ lam / (L : ℝ) := by positivity
  have hexp : 1 ≤ Real.exp ((lam / (L : ℝ)) * ((n + K : ℕ) : ℝ)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hκ (by positivity))
  have hfreeNonneg :
      0 ≤ hattedFreeReplicaKernel L previous ⊥ x y :=
    hattedFreeReplicaKernel_nonneg L previous ⊥ x y
  calc
    _ = ∑ k ∈ Finset.range K,
        freeReplicaKernel (n + k + 1) previous ⊥ x y := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hconv k
    _ = ∑ d ∈ Finset.Icc (n + 1) (n + K),
        freeReplicaKernel d previous ⊥ x y := hshift
    _ ≤ hattedFreeReplicaKernel L previous ⊥ x y := hsum
    _ ≤ Real.exp ((lam / (L : ℝ)) * ((n + K : ℕ) : ℝ)) *
        hattedFreeReplicaKernel L previous ⊥ x y := by
          calc
            _ = 1 * hattedFreeReplicaKernel L previous ⊥ x y := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hexp hfreeNonneg

end Critical2DKPZ.SHF.Moments

end
