/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonLeadingPairRows
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFinitePairing
public import Critical2DKPZ.MomentBounds.CCR25RunExpansionBase
import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
import Mathlib.Tactic

/-! # Summing the leading disjoint-pair time windows -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

attribute [local instance] Classical.propDecidable

/-- The zero-Laplace interaction is the finite sum of its run durations,
including its zero-duration atom. -/
theorem hattedInteracting_zero_eq_sum {h : ℕ} (L : ℕ) (β : ℝ) (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) :
    hattedInteractingReplicaKernelAbs L 0 β I z x =
      ∑ d ∈ Finset.range (L + 1), interactingReplicaKernelAbs β I d z x := by
  rw [Finset.sum_range_succ']
  have hzero : interactingReplicaKernelAbs β I 0 z x =
      if z = x ∧ IsCollisionConfiguration I x then (1 : ℝ) else 0 := by
    rw [interactingReplicaKernelAbs]
  simp only [hattedInteractingReplicaKernelAbs, zero_mul, neg_zero, Real.exp_zero, one_mul, hzero]
  ring

/-- Summing the first boundary, the first pair run and the next free interval
costs exactly two window-length factors and one free second moment. -/
theorem finiteThreeFactorPairing_hatted_pairs_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4)) :
    finiteThreeFactorPairing s (hattedReplicaBoundaryVector L (pairPartition α) S φ)
      (hattedInteractingReplicaKernelAbs L 0 β (pairPartition α))
      (hattedFreeReplicaKernel L (pairPartition α) (pairPartition δ)) ≤
        (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L * (B * ∑ y ∈ S, φ y) ^ 2 := by
  let R : ℕ → ℝ := fun d =>
    Renewal.renewalMass (fun r => Polymer.sigmaSq β * Renewal.returnWeight r) d
  let C := B * ∑ y ∈ S, φ y
  have heq :
      finiteThreeFactorPairing s (hattedReplicaBoundaryVector L (pairPartition α) S φ)
        (hattedInteractingReplicaKernelAbs L 0 β (pairPartition α))
        (hattedFreeReplicaKernel L (pairPartition α) (pairPartition δ)) =
      ∑ n ∈ Finset.range L, ∑ d ∈ Finset.range (L + 1), ∑ g ∈ Finset.range L,
        finiteThreeFactorPairing s (replicaBoundaryVector (n + 1) (pairPartition α) S φ)
          (interactingReplicaKernelAbs β (pairPartition α) d)
          (freeReplicaKernel (g + 1) (pairPartition α) (pairPartition δ)) := by
    change finiteThreeFactorPairing s
      (fun x => ∑ n ∈ Finset.range L, replicaBoundaryVector (n + 1) (pairPartition α) S φ x)
      (fun x y => hattedInteractingReplicaKernelAbs L 0 β (pairPartition α) x y)
      (fun y z => ∑ g ∈ Finset.range L, freeReplicaKernel (g + 1) (pairPartition α) (pairPartition δ) y z) = _
    simp_rw [hattedInteracting_zero_eq_sum]
    rw [finiteThreeFactorPairing_sum_left]
    simp_rw [finiteThreeFactorPairing_sum_middle, finiteThreeFactorPairing_sum_right]
  have hm : (∑ d ∈ Finset.range (L + 1), R d) = Renewal.freeSecondMoment β L := by
    dsimp only [R]
    rw [Renewal.freeSecondMoment_eq_renewalFunction]
    exact Renewal.sum_renewalMass_range _ _
  have htime :
      (∑ n ∈ Finset.range L, ∑ d ∈ Finset.range (L + 1), ∑ g ∈ Finset.range L,
        R d * C ^ 2) = (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L * C ^ 2 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hm]
    ring
  calc
    _ ≤ ∑ n ∈ Finset.range L, ∑ d ∈ Finset.range (L + 1), ∑ g ∈ Finset.range L,
        R d * C ^ 2 := by
      rw [heq]
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro g _
      exact sum_boundary_pair_run_free_le α δ hd β (n + 1) d (g + 1) S φ hB hφ hφB s
    _ = _ := htime

/-- The leading two-disjoint-pair operator word has the sharp quadratic
window-length bound, before the two distinguished disorder variance factors. -/
theorem leading_disjoint_pair_hatted_word_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4)) :
    (∑ x ∈ s, hattedReplicaBoundaryVector L (pairPartition α) S φ x *
      finiteKernelWordApply s
        [hattedInteractingReplicaKernelAbs L 0 β (pairPartition α),
          hattedFreeReplicaKernel L (pairPartition α) (pairPartition δ),
          hattedInteractingReplicaKernelAbs L 0 β (pairPartition δ)]
        (collisionIndicator (pairPartition δ)) x) ≤
      (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 * (B * ∑ y ∈ S, φ y) ^ 2 := by
  let E := Renewal.freeSecondMoment β L
  let U := hattedInteractingReplicaKernelAbs L 0 β (pairPartition α)
  let Q := hattedFreeReplicaKernel L (pairPartition α) (pairPartition δ)
  let V := hattedInteractingReplicaKernelAbs L 0 β (pairPartition δ)
  let A := hattedReplicaBoundaryVector L (pairPartition α) S φ
  have hE : 0 ≤ E := MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  have hr (z : LatticeConfiguration 4) :
      (∑ w ∈ s, V z w * collisionIndicator (pairPartition δ) w) ≤ E := by
    calc
      _ ≤ ∑ w ∈ s, V z w := by
        apply Finset.sum_le_sum
        intro w _
        apply mul_le_of_le_one_right (hattedInteractingReplicaKernelAbs_nonneg L 0 β _ z w)
        unfold collisionIndicator
        split_ifs <;> norm_num
      _ ≤ _ := sum_hattedInteracting_disjoint_pair_row_le δ α hd.symm β L s z
  have hx (x : LatticeConfiguration 4) :
      finiteKernelWordApply s [U, Q, V] (collisionIndicator (pairPartition δ)) x ≤
        E * ∑ y ∈ s, U x y * ∑ z ∈ s, Q y z := by
    change (∑ y ∈ s, U x y * ∑ z ∈ s, Q y z *
      ∑ w ∈ s, V z w * collisionIndicator (pairPartition δ) w) ≤ _
    calc
      _ ≤ ∑ y ∈ s, U x y * ∑ z ∈ s, Q y z * E := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (hattedInteractingReplicaKernelAbs_nonneg L 0 β _ x y)
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hr z) (hattedFreeReplicaKernel_nonneg L _ _ y z)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro z _
        ring
  calc
    _ ≤ ∑ x ∈ s, A x * (E * ∑ y ∈ s, U x y * ∑ z ∈ s, Q y z) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hx x) (hattedReplicaBoundaryVector_nonneg L _ S φ hφ x)
    _ = E * finiteThreeFactorPairing s A U Q := by
      unfold finiteThreeFactorPairing
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ E * ((L : ℝ) ^ 2 * E * (B * ∑ y ∈ S, φ y) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (finiteThreeFactorPairing_hatted_pairs_le α δ hd β L S φ hB hφ hφB s) hE
    _ = _ := by ring

/-- The bound applies to the actual two-run CCR word for arbitrary disjoint
pairs, preserving the library's boundary and terminal collision vectors. -/
theorem ccr25FiniteWordPairing_disjoint_pairs_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4)) (I : Fin 2 → ReplicaPartition 4)
    (hI0 : I 0 = pairPartition α) (hI1 : I 1 = pairPartition δ) :
    ccr25FiniteWordPairing (n := 1) s L 0 β I
      (fun J => hattedReplicaBoundaryVector L J S φ) collisionIndicator ≤
        (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 * (B * ∑ y ∈ S, φ y) ^ 2 := by
  have he : I = ![pairPartition α, pairPartition δ] := by
    funext i
    fin_cases i
    · exact hI0
    · exact hI1
  rw [he]
  exact leading_disjoint_pair_hatted_word_le α δ hd β L S φ hB hφ hφB s

/-- The same leading-word estimate with its two distinguished pair-disorder
factors included exactly. -/
theorem weighted_ccr25_disjoint_pair_word_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (β : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4)) (I : Fin 2 → ReplicaPartition 4)
    (hI0 : I 0 = pairPartition α) (hI1 : I 1 = pairPartition δ) :
    (∏ j : Fin 2, |replicaPartitionDisorderMoment β (I j)|) *
      ccr25FiniteWordPairing (n := 1) s L 0 β I
        (fun J => hattedReplicaBoundaryVector L J S φ) collisionIndicator ≤
      Polymer.sigmaSq β ^ 2 * (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 *
        (B * ∑ y ∈ S, φ y) ^ 2 := by
  have hcoef : (∏ j : Fin 2, |replicaPartitionDisorderMoment β (I j)|) = Polymer.sigmaSq β ^ 2 := by
    rw [Fin.prod_univ_two, hI0, hI1, SHF.Moments.pairPartition_disorderMoment_eq_sigmaSq,
      SHF.Moments.pairPartition_disorderMoment_eq_sigmaSq, abs_of_nonneg (sigmaSq_nonneg β)]
    ring
  rw [hcoef]
  have h := mul_le_mul_of_nonneg_left
    (ccr25FiniteWordPairing_disjoint_pairs_le α δ hd β L S φ hB hφ hφB s I hI0 hI1)
    (sq_nonneg (Polymer.sigmaSq β))
  simpa only [mul_assoc] using h

end Critical2DKPZ.Extensions.GffTangent
