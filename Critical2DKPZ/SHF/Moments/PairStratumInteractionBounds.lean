/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25InteractingRenewal
public import Critical2DKPZ.SHF.Moments.WordDominationPairOperatorSum
import Mathlib.Tactic

/-! # Pair collision strata in the CCR interaction kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

/-- For a single-pair partition, the CCR spectator kernel is exactly the
product of the free kernels of replicas outside the colliding pair. -/
theorem otherBlocksFreeKernel_pairPartition_eq {h : ℕ} (α : CollisionPair h)
    (m : ℕ) (z x : LatticeConfiguration h) :
    otherBlocksFreeKernel (pairPartition α) α.val.1 m z x =
      ∏ i : Fin h, if i = α.val.1 ∨ i = α.val.2 then 1 else
        Critical2DKPZ.srwKernel m (x i - z i) := by
  classical
  let a := α.val.1
  let b := α.val.2
  have hab : a < b := α.property
  let R : Finset (Fin h) :=
    (replicaBlockRepresentatives (pairPartition α)).filter
      (fun c => ¬ (pairPartition α).r c a)
  have hR : R = Finset.univ.filter (fun c : Fin h => c ≠ a ∧ c ≠ b) := by
    ext c
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hrep, hnot⟩
      have hnotA : c ≠ a := by
        intro hca
        subst c
        exact hnot (pairPartition_rel α a a |>.mpr (Or.inl rfl))
      have hnotB : c ≠ b := by
        intro hcb
        subst c
        exact hnot (pairPartition_rel α b a |>.mpr (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩))
      exact ⟨hnotA, hnotB⟩
    · rintro ⟨hca, hcb⟩
      refine ⟨?_, ?_⟩
      · simp only [replicaBlockRepresentatives, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro j hj
        have hj' : c = j ∨ (c = a ∨ c = b) ∧ (j = a ∨ j = b) :=
          (pairPartition_rel α c j).mp hj
        rcases hj' with rfl | ⟨hcab, hjab⟩
        · exact le_rfl
        · rcases hcab with hca' | hcb'
          · subst c
            rcases hjab with hja | hjb
            · subst j; exact le_rfl
            · subst j; exact le_of_lt hab
          · exact False.elim (hcb hcb')
      · intro hrel
        have hrel' := (pairPartition_rel α c a).mp hrel
        rcases hrel' with hca' | ⟨hcab, hja⟩
        · exact hca hca'
        · rcases hcab with hca' | hcb'
          · exact hca hca'
          · exact hcb hcb'
  unfold otherBlocksFreeKernel
  change (∏ c ∈ R, Critical2DKPZ.srwKernel m (x c - z c)) = _
  rw [hR]
  calc
    (∏ c ∈ Finset.univ.filter (fun c : Fin h => c ≠ a ∧ c ≠ b),
        Critical2DKPZ.srwKernel m (x c - z c)) =
      ∏ i : Fin h, if i ≠ a ∧ i ≠ b then
        Critical2DKPZ.srwKernel m (x i - z i) else 1 := by
          rw [Finset.prod_filter]
    _ = ∏ i : Fin h, if i = a ∨ i = b then 1 else
        Critical2DKPZ.srwKernel m (x i - z i) := by
          apply Finset.prod_congr rfl
          intro i hi
          by_cases hp : i = a ∨ i = b
          · rcases hp with hia | hib
            · subst i
              simp
            · subst i
              simp
          · have hia : i ≠ a := fun h => hp (Or.inl h)
            have hib : i ≠ b := fun h => hp (Or.inr h)
            simp [hia, hib]


end Critical2DKPZ.SHF.Moments

end
