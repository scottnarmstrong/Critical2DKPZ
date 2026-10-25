/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationLocalMoments
public import Critical2DKPZ.SHF.Moments.WordDominationPairPartitions
public import Critical2DKPZ.MomentBounds.PairCrossLabels
import Mathlib.Tactic

/-! # The pair part of the one-time active-label expansion -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

private theorem collisionWord_pairLabels_injective {h : ℕ} :
    Function.Injective (collisionPairLabels : CollisionPair h → Finset (Fin h)) := by
  intro α β he
  apply pairPartition_injective
  apply Setoid.ext
  intro i j
  have hmem (k : Fin h) :
      (k = α.1.1 ∨ k = α.1.2) ↔ (k = β.1.1 ∨ k = β.1.2) := by
    simpa only [collisionPairLabels, Finset.mem_insert, Finset.mem_singleton] using
      Finset.ext_iff.mp he k
  simp only [pairPartition_rel, hmem i, hmem j]

/-- Increasing collision pairs enumerate the two-element active label sets. -/
theorem collisionWord_pairLabels_image_eq_powersetCard_two (h : ℕ) :
    (Finset.univ : Finset (CollisionPair h)).image collisionPairLabels =
      (Finset.univ : Finset (Fin h)).powersetCard 2 := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨α, _, rfl⟩ := Finset.mem_image.mp hA
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    simp [collisionPairLabels, ne_of_lt α.2]
  · intro hA
    obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Finset.mem_image.mpr ⟨⟨(i, j), hlt⟩, Finset.mem_univ _, hAeq.symm⟩
    · refine Finset.mem_image.mpr ⟨⟨(j, i), hgt⟩, Finset.mem_univ _, ?_⟩
      simpa only [collisionPairLabels, Finset.pair_comm] using hAeq.symm

/-- The two-label contribution is precisely the one-edge pair potential. -/
theorem sum_powersetCard_two_collisionWordLocalVertexMoment (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    (∑ A ∈ (Finset.univ : Finset (Fin h)).powersetCard 2,
      collisionWordLocalVertexMoment β x A) =
      sigmaSq β * ∑ α : CollisionPair h, if x α.1.1 = x α.1.2 then (1 : ℝ) else 0 := by
  classical
  rw [← collisionWord_pairLabels_image_eq_powersetCard_two h,
    Finset.sum_image collisionWord_pairLabels_injective.injOn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [collisionPairLabels, collisionWordLocalVertexMoment_pair β x _ _ (ne_of_lt α.2)]
  split_ifs <;> ring

/-- Empty, singleton, and pair active sets contribute the free term and the
one-edge potential; singleton terms vanish by centering. -/
theorem sum_small_collisionWordLocalVertexMoment (β : ℝ) {h : ℕ} (x : Fin h → Site) :
    (∑ A ∈ (Finset.univ : Finset (Fin h)).powerset.filter (fun A => A.card ≤ 2),
      collisionWordLocalVertexMoment β x A) =
      1 + sigmaSq β * ∑ α : CollisionPair h,
        if x α.1.1 = x α.1.2 then (1 : ℝ) else 0 := by
  classical
  let U : Finset (Fin h) := Finset.univ
  have hsets : U.powerset.filter (fun A => A.card ≤ 2) =
      (U.powersetCard 0 ∪ U.powersetCard 1) ∪ U.powersetCard 2 := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hc⟩
      rcases (show A.card = 0 ∨ A.card = 1 ∨ A.card = 2 by omega) with hc | hc | hc
      · exact Or.inl (Or.inl ⟨hsub, hc⟩)
      · exact Or.inl (Or.inr ⟨hsub, hc⟩)
      · exact Or.inr ⟨hsub, hc⟩
    · rintro ((⟨hsub, hc⟩ | ⟨hsub, hc⟩) | ⟨hsub, hc⟩) <;> exact ⟨hsub, by omega⟩
  have h01 : Disjoint (U.powersetCard 0) (U.powersetCard 1) :=
    Finset.disjoint_powersetCard_of_ne (by decide) U U
  have h012 : Disjoint (U.powersetCard 0 ∪ U.powersetCard 1) (U.powersetCard 2) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_powersetCard_of_ne (by decide) U U,
        Finset.disjoint_powersetCard_of_ne (by decide) U U⟩
  change (∑ A ∈ U.powerset.filter (fun A => A.card ≤ 2), _) = _
  rw [hsets, Finset.sum_union h012, Finset.sum_union h01,
    Finset.powersetCard_zero, Finset.sum_singleton,
    collisionWordLocalVertexMoment_empty, Finset.powersetCard_one, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, collisionWordLocalVertexMoment_singleton,
    Finset.sum_const_zero, add_zero]
  rw [show (∑ A ∈ U.powersetCard 2, collisionWordLocalVertexMoment β x A) =
    sigmaSq β * ∑ α : CollisionPair h, if x α.1.1 = x α.1.2 then (1 : ℝ) else 0 from
      sum_powersetCard_two_collisionWordLocalVertexMoment β x]

/-- The local non-pair contribution is the sum over active sets containing at least three labels. -/
theorem exp_replicaPotential_eq_pair_add_nonpair (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    Real.exp (β ^ 2 * replicaPotential x) =
      (1 + sigmaSq β * ∑ α : CollisionPair h,
        if x α.1.1 = x α.1.2 then (1 : ℝ) else 0) +
      ∑ A ∈ (Finset.univ : Finset (Fin h)).powerset.filter (fun A => 3 ≤ A.card),
        collisionWordLocalVertexMoment β x A := by
  classical
  rw [exp_replicaPotential_eq_sum_collisionWordLocalVertexMoment,
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin h)).powerset) (fun A => A.card ≤ 2),
    sum_small_collisionWordLocalVertexMoment]
  congr 1
  apply Finset.sum_congr
  · ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    omega
  · intro A hA
    rfl

end Critical2DKPZ.SHF.Moments

end
