/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansion
import Mathlib.Tactic

/-! # Low-order identities for collision-word expansions -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

private theorem collisionPair_subsingleton_of_le_two {h : ℕ} (hh : h ≤ 2) :
    Subsingleton (CollisionPair h) := by
  have hcases : h = 0 ∨ h = 1 ∨ h = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · refine ⟨fun α _ => ?_⟩
    exact (collisionPair_impossible (by norm_num) α).elim
  · refine ⟨fun α _ => ?_⟩
    exact (collisionPair_impossible (by norm_num) α).elim
  · exact collisionPair_two_subsingleton

private theorem pairSimple_of_subset_collisionEdges_of_le_two {h n : ℕ}
    (hh : h ≤ 2) (A : Finset (ℕ × CollisionPair h))
    (_hA : A ⊆ collisionEdges n h) : IsPairSimple A := by
  intro e he e' he' htime
  have hpair : e.2 = e'.2 := (collisionPair_subsingleton_of_le_two hh).elim _ _
  exact Prod.ext htime hpair

/-- With at most two particles, the non-pair collision remainder vanishes. -/
theorem nonpairCollisionRemainder_eq_zero_of_h_le_two (β : ℝ) {h n : ℕ}
    (hh : h ≤ 2) (x y : Fin h → Site) :
    nonpairCollisionRemainder β n h x y = 0 := by
  classical
  have hbad : (collisionEdges n h).powerset.filter (fun A => ¬ IsPairSimple A) = ∅ := by
    apply Finset.filter_false_of_mem
    intro A hpow hnot
    exact hnot (pairSimple_of_subset_collisionEdges_of_le_two hh A
      (Finset.mem_powerset.mp hpow))
  unfold nonpairCollisionRemainder
  rw [hbad]
  simp

/-- With at most two particles, the tested non-pair remainder vanishes. -/
theorem testedNonpairRemainder_eq_zero_of_h_le_two (ϑ : ℝ) (N : ℕ)
    {s t : ℝ} {h : ℕ} (hh : h ≤ 2)
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    testedNonpairRemainder ϑ N s t φ = 0 := by
  classical
  unfold testedNonpairRemainder
  simp only [nonpairCollisionRemainder_eq_zero_of_h_le_two
    (criticalBeta ϑ N) hh]
  simp

/-- With at most two particles, any sum over collision words of length at least two is zero. -/
theorem collisionWord_sum_eq_zero_of_h_le_two_of_two_le_length {h m : ℕ}
    (hh : h ≤ 2) (hm : 2 ≤ m) (f : CollisionWord h m → ℝ) :
    (∑ w : CollisionWord h m, f w) = 0 := by
  classical
  have hempty : ∀ w : CollisionWord h m, False := by
    have hcases : h = 0 ∨ h = 1 ∨ h = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · intro w
      exact (collisionPair_impossible (by norm_num)
        (w.1 ⟨0, by omega⟩)).elim
    · intro w
      exact (collisionPair_impossible (by norm_num)
        (w.1 ⟨0, by omega⟩)).elim
    · intro w
      have hneq := w.2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by norm_num)
      exact hneq (collisionPair_two_subsingleton.elim _ _)
  apply Finset.sum_eq_zero
  intro w hw
  exact (hempty w).elim

end Critical2DKPZ.SHF.Moments

end
