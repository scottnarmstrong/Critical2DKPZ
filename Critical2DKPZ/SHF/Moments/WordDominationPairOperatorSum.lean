/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.AiiKDisorderMoment
public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
public import Critical2DKPZ.SHF.Moments.WordDominationPairPartitions
import Mathlib.Tactic

/-! # Geometric counting for CCR pair-partition words -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- A pair collision partition has exactly one nonsingleton block, so its
disorder factor is exactly one variance factor. -/
theorem pairPartition_disorderMoment_eq_sigmaSq {h : ℕ}
    (β : ℝ) (α : CollisionPair h) :
    replicaPartitionDisorderMoment β (pairPartition α) = Polymer.sigmaSq β := by
  classical
  let a := α.val.1
  let b := α.val.2
  have hab : a < b := α.property
  have hsize (r : Fin h) :
      replicaBlockSize (pairPartition α) r = if r = a ∨ r = b then 2 else 1 := by
    unfold replicaBlockSize
    have hclass :
        (Finset.univ.filter (fun j : Fin h => (pairPartition α).r r j)) =
          if r = a ∨ r = b then ({a, b} : Finset (Fin h)) else {r} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (r = j ∨ (r = a ∨ r = b) ∧ (j = a ∨ j = b)) ↔
        j ∈ (if r = a ∨ r = b then ({a, b} : Finset (Fin h)) else {r})
      by_cases hr : r = a ∨ r = b
      · rcases hr with hr | hr
        · subst r
          simp [hab.ne, eq_comm]
        · subst r
          simp [hab.ne, eq_comm]
          intro hj
          exact Or.inr hj
      · have hra : r ≠ a := fun h => hr (Or.inl h)
        have hrb : r ≠ b := fun h => hr (Or.inr h)
        simp [hra, hrb, eq_comm]
    rw [hclass]
    by_cases hr : r = a ∨ r = b <;> simp [hr, hab.ne]
  have hfilter :
      (replicaBlockRepresentatives (pairPartition α)).filter
          (fun r => 2 ≤ replicaBlockSize (pairPartition α) r) = {a} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hrmem, hs⟩
      rw [hsize] at hs
      by_cases hendpoint : r = a ∨ r = b
      · rcases hendpoint with hr | hr
        · exact hr
        · subst r
          have hleast := (Finset.mem_filter.mp hrmem).2 a
          have hrel : (pairPartition α).r b a := by
            change (b = a ∨ (b = a ∨ b = b) ∧ (a = a ∨ a = b))
            exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
          have hle := hleast hrel
          omega
      · simp [hendpoint] at hs
    · intro hr
      subst r
      refine ⟨?_, ?_⟩
      · simp only [replicaBlockRepresentatives, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro j hj
        have hj' : j = a ∨ j = b := by
          change (a = j ∨ (a = a ∨ a = b) ∧ (j = a ∨ j = b)) at hj
          rcases hj with h | ⟨_, hj⟩
          · exact Or.inl h.symm
          · exact hj
        rcases hj' with rfl | rfl <;> omega
      · rw [hsize]
        simp
  have hmoment :
      replicaPartitionDisorderMoment β (pairPartition α) =
        gaussianDisorderMoment β 2 := by
    unfold replicaPartitionDisorderMoment
    rw [← Finset.prod_filter]
    rw [hfilter]
    simp [hsize]
  rw [hmoment]
  change (∫ ω : Disorder, Polymer.xi β (0, 0) ω ^ 2 ∂disorderLaw) = _
  exact Polymer.integral_xi_sq β (0, 0)



end Critical2DKPZ.SHF.Moments

end
