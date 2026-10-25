/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationLocalMoments
public import Critical2DKPZ.MomentBounds.CCR25RunExpansion
import Mathlib.Tactic

/-! # Local active moments in the canonical CCR partition convention -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer Critical2DKPZ.MomentBounds

/-- One-time chaos coordinates selected by an active label set. -/
def collisionWordLocalCoordinates {h : ℕ} (x : Fin h → Site) (A : Finset (Fin h)) :
    Fin h → Finset (ℕ × Site) :=
  fun i => if i ∈ A then {(0, x i)} else ∅

/-- The canonical CCR chaos choices realizing a one-time active set at time
zero; the zero-length paths leave every initial position unchanged. -/
def collisionWordLocalChaosChoices {h : ℕ} (A : Finset (Fin h)) :
    Fin h → Finset ℕ × (Fin 0 → Fin 4) :=
  fun i => (if i ∈ A then {0} else ∅, Fin.elim0)

/-- Local coordinates agree with the canonical mixed-start CCR coordinates. -/
theorem collisionWordLocalCoordinates_eq_run {h : ℕ} (x : Fin h → Site)
    (A : Finset (Fin h)) :
    collisionWordLocalCoordinates x A =
      ccr25RunReplicaChaosCoordinateSets 0 x (collisionWordLocalChaosChoices A) := by
  classical
  funext i
  by_cases hi : i ∈ A <;>
    simp [collisionWordLocalCoordinates, collisionWordLocalChaosChoices,
      ccr25RunReplicaChaosCoordinateSets, ccr25ChaosCoordinates, hi, walkPosition_zero]

private theorem collisionWordLocalProduct_eq_chaosProduct (β : ℝ) {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h)) (ω : Disorder) :
    collisionWordLocalVertexProduct β x A ω =
      ∏ i : Fin h, chaosMonomial β (collisionWordLocalCoordinates x A i) ω := by
  classical
  let f : Fin h → ℝ := fun i => chaosMonomial β (collisionWordLocalCoordinates x A i) ω
  have hout (i : Fin h) (hi : i ∉ A) : f i = 1 := by
    simp [f, collisionWordLocalCoordinates, chaosMonomial, hi]
  calc
    _ = ∏ i ∈ A, f i := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [f, collisionWordLocalCoordinates, chaosMonomial, hi]
    _ = ∏ i : Fin h, f i := Finset.prod_subset (Finset.subset_univ A)
      (by intro i hi hiA; exact hout i hiA)

/-- Local active-label moments factor into moments at their distinct
disorder coordinates, with multiplicities retained. -/
theorem collisionWordLocalVertexMoment_eq_gaussianMoments (β : ℝ) {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h)) :
    collisionWordLocalVertexMoment β x A =
      ∏ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
        gaussianDisorderMoment β (chaosOccurrenceCount (collisionWordLocalCoordinates x A) z) := by
  unfold collisionWordLocalVertexMoment
  simp_rw [collisionWordLocalProduct_eq_chaosProduct]
  exact integral_chaosMonomial_product_eq_gaussianMoments β _

/-- A singleton occupied disorder coordinate annihilates its local active
moment. -/
theorem collisionWordLocalVertexMoment_eq_zero_of_singleton (β : ℝ) {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h)) (z : ℕ × Site)
    (hz : z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A))
    (hcount : chaosOccurrenceCount (collisionWordLocalCoordinates x A) z = 1) :
    collisionWordLocalVertexMoment β x A = 0 := by
  unfold collisionWordLocalVertexMoment
  simp_rw [collisionWordLocalProduct_eq_chaosProduct]
  exact integral_chaosMonomial_product_eq_zero_of_singleton β _ z hz hcount

private theorem collisionWordLocalTimeCoordinates_eq_union {h : ℕ} (x : Fin h → Site)
    (A : Finset (Fin h)) :
    ccr25RunTimeCoordinates 0 0 x (collisionWordLocalChaosChoices A) =
      chaosOccurrenceUnion (collisionWordLocalCoordinates x A) := by
  classical
  have hselected (i : Fin h) : 0 ∈ (collisionWordLocalChaosChoices A i).1 ↔ i ∈ A := by
    by_cases hi : i ∈ A <;> simp [collisionWordLocalChaosChoices, hi]
  have hcoord (i : Fin h) (z : ℕ × Site) :
      z ∈ collisionWordLocalCoordinates x A i ↔ i ∈ A ∧ z = (0, x i) := by
    by_cases hi : i ∈ A <;> simp [collisionWordLocalCoordinates, hi]
  ext z
  simp only [ccr25RunTimeCoordinates, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, hselected, walkPosition_zero, Nat.zero_add,
    chaosOccurrenceUnion, Finset.mem_biUnion, hcoord]
  aesop

/-- Once singleton coordinates are excluded, the local active-label moment
is exactly the disorder moment of its canonical CCR collision partition. -/
theorem collisionWordLocalVertexMoment_eq_partitionMoment (β : ℝ) {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h))
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
      chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1) :
    collisionWordLocalVertexMoment β x A = replicaPartitionDisorderMoment β
      (ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A)) := by
  classical
  have hrunNoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets 0 x (collisionWordLocalChaosChoices A)),
      chaosOccurrenceCount
        (ccr25RunReplicaChaosCoordinateSets 0 x (collisionWordLocalChaosChoices A)) z ≠ 1 := by
    rw [← collisionWordLocalCoordinates_eq_run]
    exact hnoSingleton
  have htime := collisionWordLocalTimeCoordinates_eq_union x A
  rw [collisionWordLocalCoordinates_eq_run] at htime
  have hcollision := ccr25RunTimeCoordinates_eq_collisionCoordinates
    0 0 x (collisionWordLocalChaosChoices A) hrunNoSingleton
  rw [collisionWordLocalVertexMoment_eq_gaussianMoments, collisionWordLocalCoordinates_eq_run,
    ← htime, hcollision]
  rw [Finset.prod_image (by
    intro y hy z hz he
    exact congrArg Prod.snd he)]
  exact (replicaPartitionDisorderMoment_eq_prod_runCollisionSites
    β 0 0 x (collisionWordLocalChaosChoices A)).symm

end Critical2DKPZ.SHF.Moments

end
