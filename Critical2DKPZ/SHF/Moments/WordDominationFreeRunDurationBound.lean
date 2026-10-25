/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFreeDurationSum
public import Critical2DKPZ.SHF.Moments.WordDominationRunLaplaceTruncation
public import Critical2DKPZ.SHF.Moments.WordDominationPairStratumFree
import Mathlib.Tactic

/-! # One-step damped duration contraction -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- A free interval followed by a pair run and a damped continuation of the
remaining duration is bounded by one hatted free transition and one hatted
interaction. This is the finite-duration contraction used at each letter of
the collision word. -/
theorem collisionWord_freeRunDuration_sum_le_hatted
    {h n k L : ℕ} (hk : 1 ≤ k) (hcut : n + k ≤ L)
    (β lam : ℝ) (hlam : 0 ≤ lam) (α : CollisionPair h)
    (x u v : LatticeConfiguration h) :
    (∑ s ∈ Finset.Icc 1 n,
      (∏ i, srwKernel s (u i - x i)) *
        ∑ r ∈ Finset.range (n - s + 1),
          collisionWordUndampedPairRunFactor β α r u v *
            Real.exp ((lam / (L : ℝ)) * ((n - s - r + k : ℕ) : ℝ))) ≤
      Real.exp ((lam / (L : ℝ)) * ((n + k : ℕ) : ℝ)) *
        hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
          (sigmaSq β * hattedInteractingReplicaKernelAbs L
            (lam / (L : ℝ)) β (pairPartition α) u v) := by
  let κ : ℝ := lam / (L : ℝ)
  have hLpos : 0 < L := by omega
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hfreeSum := collisionWord_freeReplicaKernel_duration_sum_le
    (n := n) (L := L) (by omega) ⊥ (pairPartition α) x u
  have hU : 0 ≤ sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
      (pairPartition α) u v :=
    mul_nonneg (sigmaSq_nonneg β)
      (hattedInteractingReplicaKernelAbs_nonneg L κ β
        (pairPartition α) u v)
  by_cases hu : u α.1.1 = u α.1.2
  · have hfreeEq (s : ℕ) :
        (∏ i, srwKernel s (u i - x i)) =
          freeReplicaKernel s ⊥ (pairPartition α) x u := by
      rw [freeReplicaKernel_bot_pair_eq]
      simp [hu]
    have hrun (s : ℕ) (hs : s ∈ Finset.Icc 1 n) :
        (∑ r ∈ Finset.range (n - s + 1),
          collisionWordUndampedPairRunFactor β α r u v *
            Real.exp (κ * ((n - s - r + k : ℕ) : ℝ))) ≤
          Real.exp (κ * ((n - s + k : ℕ) : ℝ)) *
            (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
              (pairPartition α) u v) := by
      have hsle : s ≤ n := (Finset.mem_Icc.mp hs).2
      have hdL : n - s ≤ L := by omega
      have hlap := collisionWord_pairRunFactor_laplace_sum_le_hatted
        β lam L (n - s) hdL α u v
      have htime (r : ℕ) (hr : r ∈ Finset.range (n - s + 1)) :
          Real.exp (κ * ((n - s - r + k : ℕ) : ℝ)) =
            Real.exp (κ * ((n - s + k : ℕ) : ℝ)) *
              Real.exp (-(κ * (r : ℝ))) := by
        have hrle : r ≤ n - s := by
          have := Finset.mem_range.mp hr
          omega
        have hnats : n - s - r + k + r = n - s + k := by omega
        rw [← Real.exp_add]
        congr 1
        push_cast [Nat.cast_add, Nat.cast_sub (by omega : r ≤ n - s)]
        dsimp [κ]
        ring
      have hsumRewrite :
          (∑ r ∈ Finset.range (n - s + 1),
            collisionWordUndampedPairRunFactor β α r u v *
              Real.exp (κ * ((n - s - r + k : ℕ) : ℝ))) =
            Real.exp (κ * ((n - s + k : ℕ) : ℝ)) *
              ∑ r ∈ Finset.range (n - s + 1),
                Real.exp (-(κ * (r : ℝ))) *
                  collisionWordUndampedPairRunFactor β α r u v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [htime r hr]
        ring
      have hExpNonneg :
          0 ≤ Real.exp (κ * ((n - s + k : ℕ) : ℝ)) := Real.exp_nonneg _
      calc
        _ = Real.exp (κ * ((n - s + k : ℕ) : ℝ)) *
            ∑ r ∈ Finset.range (n - s + 1),
              Real.exp (-(κ * (r : ℝ))) *
                collisionWordUndampedPairRunFactor β α r u v := hsumRewrite
        _ ≤ Real.exp (κ * ((n - s + k : ℕ) : ℝ)) *
            (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
              (pairPartition α) u v) :=
          mul_le_mul_of_nonneg_left hlap hExpNonneg
    have htime (s : ℕ) (hs : s ∈ Finset.Icc 1 n) :
        Real.exp (κ * ((n - s + k : ℕ) : ℝ)) ≤
          Real.exp (κ * ((n + k : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hκ
      have hsle : s ≤ n := (Finset.mem_Icc.mp hs).2
      exact_mod_cast (show n - s + k ≤ n + k by omega)
    have hfreeNonneg (s : ℕ) :
        0 ≤ freeReplicaKernel s ⊥ (pairPartition α) x u :=
      freeReplicaKernel_nonneg s ⊥ (pairPartition α) x u
    have hsumLe :
        (∑ s ∈ Finset.Icc 1 n,
          freeReplicaKernel s ⊥ (pairPartition α) x u *
            (∑ r ∈ Finset.range (n - s + 1),
              collisionWordUndampedPairRunFactor β α r u v *
                Real.exp (κ * ((n - s - r + k : ℕ) : ℝ)))) ≤
          (∑ s ∈ Finset.Icc 1 n,
            freeReplicaKernel s ⊥ (pairPartition α) x u) *
            (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
              (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                (pairPartition α) u v)) := by
      calc
        _ ≤ ∑ s ∈ Finset.Icc 1 n,
            freeReplicaKernel s ⊥ (pairPartition α) x u *
              (Real.exp (κ * ((n - s + k : ℕ) : ℝ)) *
                (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                  (pairPartition α) u v)) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left (hrun s hs) (hfreeNonneg s)
        _ ≤ _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro s hs
          apply mul_le_mul_of_nonneg_left _ (hfreeNonneg s)
          exact mul_le_mul_of_nonneg_right (htime s hs) hU
    have hfreeSum' :
        (∑ s ∈ Finset.Icc 1 n,
          freeReplicaKernel s ⊥ (pairPartition α) x u) ≤
          hattedFreeReplicaKernel L ⊥ (pairPartition α) x u := hfreeSum
    have hconstant :
        0 ≤ Real.exp (κ * ((n + k : ℕ) : ℝ)) *
          (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
            (pairPartition α) u v) := mul_nonneg (Real.exp_nonneg _) hU
    simp_rw [hfreeEq]
    calc
      _ ≤ (∑ s ∈ Finset.Icc 1 n,
            freeReplicaKernel s ⊥ (pairPartition α) x u) *
            (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
              (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                (pairPartition α) u v)) := hsumLe
      _ ≤ hattedFreeReplicaKernel L ⊥ (pairPartition α) x u *
            (Real.exp (κ * ((n + k : ℕ) : ℝ)) *
              (sigmaSq β * hattedInteractingReplicaKernelAbs L κ β
                (pairPartition α) u v)) :=
          mul_le_mul_of_nonneg_right hfreeSum' hconstant
      _ = _ := by ring
  · simp [collisionWordUndampedPairRunFactor, hu]
    exact mul_nonneg
      (mul_nonneg (Real.exp_nonneg _)
        (hattedFreeReplicaKernel_nonneg L ⊥ (pairPartition α) x u)) hU

end Critical2DKPZ.SHF.Moments

end
