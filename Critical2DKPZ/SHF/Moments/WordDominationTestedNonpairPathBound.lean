/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationNonpairTerminalMass
public import Critical2DKPZ.SHF.Moments.WordDominationCellProfile
import Mathlib.Tactic

/-! # Compact tested remainders as marked point-to-plane path sums -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Compact cell tests reduce the absolute tested remainder to a marked
point-to-plane expansion with exactly the cell normalization N to the minus h. -/
theorem abs_testedNonpairRemainder_le_markedPartitionSum
    (ϑ : ℝ) {h N : ℕ} (hN : 0 < N) (s t : ℝ)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφ : ∀ i p, |φ i p| ≤ M)
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R) :
    |testedNonpairRemainder ϑ N s t φ| ≤
      (4 * M / N) ^ h *
        ∑ x ∈ Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R),
          ∑ I ∈ collisionWordMarkedPartitionSequences h
            (evenCeil (N * t) - evenCeil (N * s)),
            (∏ j : Fin (evenCeil (N * t) - evenCeil (N * s)),
              |replicaPartitionDisorderMoment (criticalBeta ϑ N) (I j)|) *
              replicaPathWeight (List.ofFn I) x := by
  classical
  let X := Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R)
  let n := evenCeil (N * t) - evenCeil (N * s)
  let β := criticalBeta ϑ N
  let weight := fun x y : LatticeConfiguration h => ∏ i, cellTestWeight N (φ i) (x i) (y i)
  have hcell := abs_prod_cellTestWeight_le_scaledBallIndicators hN φ M R hM hR hφ hφR
  have hleft (x : LatticeConfiguration h) (hx : x ∉ X) (y : LatticeConfiguration h) :
      weight x y = 0 := by
    have hx' : ¬ ∀ i, x i ∈ collisionWordScaledBallSites N R := by
      simpa only [X, Fintype.mem_piFinset] using hx
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa [weight, hx'] using hcell x y
  have hright (x y : LatticeConfiguration h) (hy : y ∉ X) : weight x y = 0 := by
    have hy' : ¬ ∀ i, y i ∈ collisionWordScaledBallSites N R := by
      simpa only [X, Fintype.mem_piFinset] using hy
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa [weight, hy'] using hcell x y
  have hfinite : testedNonpairRemainder ϑ N s t φ =
      ∑ x ∈ X, ∑ y ∈ X, weight x y * nonpairCollisionRemainder β n h x y := by
    unfold testedNonpairRemainder
    rw [tsum_eq_sum (s := X)]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [tsum_eq_sum (s := X)]
      · intro y hy
        change weight x y * _ = 0
        rw [hright x y hy, zero_mul]
    · intro x hx
      have hz : ∀ y, weight x y * nonpairCollisionRemainder β n h x y = 0 := by
        intro y
        rw [hleft x hx y, zero_mul]
      change (∑' y, weight x y * nonpairCollisionRemainder β n h x y) = 0
      simp only [hz, tsum_zero]
  rw [hfinite, Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ X, |weight x y * nonpairCollisionRemainder β n h x y| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun x hx => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ x ∈ X, (4 * M / N) ^ h *
        ∑ I ∈ collisionWordMarkedPartitionSequences h n,
          (∏ j : Fin n, |replicaPartitionDisorderMoment β (I j)|) *
            replicaPathWeight (List.ofFn I) x := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' : ∀ i, x i ∈ collisionWordScaledBallSites N R := Fintype.mem_piFinset.mp hx
      calc
        _ ≤ ∑ y ∈ X, (4 * M / N) ^ h * nonpairCollisionRemainder β n h x y := by
          apply Finset.sum_le_sum
          intro y hy
          have hy' : ∀ i, y i ∈ collisionWordScaledBallSites N R := Fintype.mem_piFinset.mp hy
          rw [abs_mul, abs_of_nonneg (nonpairCollisionRemainder_nonneg β n h x y)]
          apply mul_le_mul_of_nonneg_right _ (nonpairCollisionRemainder_nonneg β n h x y)
          simpa [weight, hx', hy'] using hcell x y
        _ = (4 * M / N) ^ h * ∑ y ∈ X, nonpairCollisionRemainder β n h x y := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (collisionWord_sum_nonpairCollisionRemainder_le_markedPartitionSum β n h x X)
          (by positivity)

end Critical2DKPZ.SHF.Moments

end
