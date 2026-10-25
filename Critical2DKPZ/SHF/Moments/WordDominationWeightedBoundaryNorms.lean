/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationWeightedBoundaryProduct
import Mathlib.Tactic

/-! # Uniform norm choices for every nontrivial partition boundary -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Finite sums of the partition boundary norms provide common left and right
costs with the same diffusive product scaling. -/
theorem exists_collisionWord_weightedBoundary_norms (h : ℕ) (hh : 2 ≤ h)
    (B : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N L : ℕ}, 1 ≤ N → L ≤ B * N →
      ∀ s : Finset (LatticeConfiguration h), ∃ left right : ℝ,
        0 ≤ left ∧ 0 ≤ right ∧
        (∀ I : ReplicaPartition h, I ≠ ⊥ →
          finiteLpNorm s 2 (fun x => hattedReplicaBoundaryVector L I
            (collisionWordScaledBallSites N R)
            (fun y => if y ∈ collisionWordScaledBallSites N R then (1 : ℝ) else 0) x /
            replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) x) ≤ left) ∧
        (∀ J : ReplicaPartition h, J ≠ ⊥ →
          finiteLpNorm s 2 (fun x => replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) x *
            collisionIndicator J x) ≤ right) ∧
        left * right ≤ C * (N : ℝ) ^ h := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_collisionWord_weightedBoundary_product_le h hh B R hR
  let P : Finset (ReplicaPartition h) := Finset.univ.erase ⊥
  refine ⟨(P.card : ℝ) ^ 2 * C, by positivity, ?_⟩
  intro N L hN hL s
  let l := fun I : ReplicaPartition h => finiteLpNorm s 2
    (fun x => hattedReplicaBoundaryVector L I (collisionWordScaledBallSites N R)
      (fun y => if y ∈ collisionWordScaledBallSites N R then (1 : ℝ) else 0) x /
      replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) x)
  let r := fun J : ReplicaPartition h => finiteLpNorm s 2
    (fun x => replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) x * collisionIndicator J x)
  have hl : ∀ I, 0 ≤ l I := fun I => finiteLpNorm_nonneg _ _ _
  have hr : ∀ J, 0 ≤ r J := fun J => finiteLpNorm_nonneg _ _ _
  refine ⟨∑ I ∈ P, l I, ∑ J ∈ P, r J,
    Finset.sum_nonneg (fun I hI => hl I), Finset.sum_nonneg (fun J hJ => hr J), ?_, ?_, ?_⟩
  · intro I hI
    exact Finset.single_le_sum (fun J hJ => hl J) (by simp [P, hI])
  · intro J hJ
    exact Finset.single_le_sum (fun I hI => hr I) (by simp [P, hJ])
  · calc
      _ = ∑ I ∈ P, ∑ J ∈ P, l I * r J := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ _I ∈ P, ∑ _J ∈ P, C * (N : ℝ) ^ h := by
        apply Finset.sum_le_sum
        intro I hI
        apply Finset.sum_le_sum
        intro J hJ
        exact hbound hN hL s I J (Finset.mem_erase.mp hI).1 (Finset.mem_erase.mp hJ).1
      _ = _ := by simp; ring

end Critical2DKPZ.SHF.Moments

end
