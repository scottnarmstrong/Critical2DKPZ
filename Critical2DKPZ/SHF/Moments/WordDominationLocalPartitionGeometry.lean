/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationLocalPartitions
public import Critical2DKPZ.SHF.Moments.WordDominationNonpairMoment
import Mathlib.Tactic

/-! # The inverse local active-set and collision-partition maps -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Polymer Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose

private theorem zero_mem_local_chaos_times_iff_label_active {h : ℕ} (A : Finset (Fin h)) (i : Fin h) :
    0 ∈ (collisionWordLocalChaosChoices A i).1 ↔ i ∈ A := by
  classical
  by_cases hi : i ∈ A <;> simp [collisionWordLocalChaosChoices, hi]


/-- The configuration belongs to the exact CCR stratum induced by any local
active set. -/
theorem collisionWordLocalPartition_isCollisionConfiguration {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h)) :
    IsCollisionConfiguration (ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A)) x := by
  simpa only [walkPosition_zero] using
    ccr25RunTimePartition_path_isCollisionConfiguration 0 x (collisionWordLocalChaosChoices A)

/-- Under the no-singleton condition, the active set is recovered exactly
from the nonsingleton labels of its induced partition. -/
theorem collisionWordLocalPartition_collisionLabels_eq {h : ℕ}
    (x : Fin h → Site) (A : Finset (Fin h))
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
      chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1) :
    ccr25PartitionCollisionLabels (ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A)) = A := by
  classical
  have hrun : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets 0 x (collisionWordLocalChaosChoices A)),
      chaosOccurrenceCount
        (ccr25RunReplicaChaosCoordinateSets 0 x (collisionWordLocalChaosChoices A)) z ≠ 1 := by
    rw [← collisionWordLocalCoordinates_eq_run]
    exact hnoSingleton
  ext i
  simp only [ccr25PartitionCollisionLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (ccr25RunTimePartition_active_iff_inCollisionBlock
    0 0 x (collisionWordLocalChaosChoices A) hrun i).symm.trans (zero_mem_local_chaos_times_iff_label_active A i)



/-- The local active-set map is injective once singleton coordinates have
been excluded. -/
theorem collisionWordLocalPartition_injective_on_noSingleton {h : ℕ}
    (x : Fin h → Site) (A B : Finset (Fin h))
    (hA : ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x A),
      chaosOccurrenceCount (collisionWordLocalCoordinates x A) z ≠ 1)
    (hB : ∀ z ∈ chaosOccurrenceUnion (collisionWordLocalCoordinates x B),
      chaosOccurrenceCount (collisionWordLocalCoordinates x B) z ≠ 1)
    (he : ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices A) =
      ccr25RunTimePartition 0 x (collisionWordLocalChaosChoices B)) : A = B := by
  rw [← collisionWordLocalPartition_collisionLabels_eq x A hA,
    ← collisionWordLocalPartition_collisionLabels_eq x B hB, he]

end Critical2DKPZ.SHF.Moments

end
