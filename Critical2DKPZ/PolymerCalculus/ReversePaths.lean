/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.TimeReversal
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Tactic

/-! Reversing a nearest-neighbour path and replacing its steps by their opposites reverses its sequence of visited sites. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

/-- Reverse a walk word and replace each step by its opposite. -/
def reverseSteps {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) : Fin 4 :=
  Polymer.oppositeStep (s i.rev)

/-- Reversing the sequence of path steps twice recovers the original sequence. -/
@[simp] theorem reverseSteps_reverseSteps {n : ℕ} (s : Fin n → Fin 4) :
    reverseSteps (reverseSteps s) = s := by
  funext i
  simp only [reverseSteps, Fin.rev_rev]
  exact (Polymer.oppositeStep.left_inv (s i))

/-- Reversing about the terminal site reverses the entire position chain. -/
theorem walkPosition_reverseSteps {n : ℕ} (w : Site) (s : Fin n → Fin 4)
    (j : ℕ) (hj : j ≤ n) :
    walkPosition (walkPosition w s n) (reverseSteps s) j = walkPosition w s (n - j) := by
  rw [Polymer.walkPosition_eq_sum_ite, Polymer.walkPosition_end,
    Polymer.walkPosition_eq_sum_ite]
  simp only [reverseSteps, Polymer.srwStep_opposite]
  rw [← (Equiv.sum_comp Fin.revPerm (fun i : Fin n =>
    if i.val < j then -srwStep (s i.rev) else (0 : Site)))]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have hs : (∑ i : Fin n, srwStep (s i)) +
      (∑ i : Fin n, if i.rev.val < j then -srwStep (s i) else 0) =
      ∑ i : Fin n, if i.val < n - j then srwStep (s i) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hv : i.rev.val = n - (i.val + 1) := rfl
    have he : i.rev.val < j ↔ ¬ i.val < n - j := by omega
    by_cases hi : i.val < n - j
    · rw [ite_eq_right (he.not.mpr (not_not.mpr hi)), ite_eq_left hi, add_zero]
    · rw [ite_eq_left (he.mpr hi), ite_eq_right hi, add_neg_cancel]
  rw [add_assoc, hs]

/-- Reversal with opposite increments is an involutive bijection on paths of fixed length. -/
def reverseStepsEquiv (n : ℕ) : (Fin n → Fin 4) ≃ (Fin n → Fin 4) :=
  Function.Involutive.toPerm reverseSteps reverseSteps_reverseSteps

/-- Reversing a nearest-neighbour path reindexes its interior disorder-energy sum. -/
theorem interiorEnergy_reverseSteps (β : ℝ) (L a n : ℕ) (hL : a + n ≤ L)
    (w : Site) (s : Fin n → Fin 4) (ω : Disorder) :
    interiorEnergy β (L - (a + n)) n
      (fun j => walkPosition (walkPosition w s n) (reverseSteps s) j)
      (reversedDisorder L ω) =
      interiorEnergy β a n (fun j => walkPosition w s j) ω := by
  have he : interiorEnergy β (L - (a + n)) n
      (fun j => walkPosition (walkPosition w s n) (reverseSteps s) j)
      (reversedDisorder L ω) =
      interiorEnergy β (L - (a + n)) n (fun j => walkPosition w s (n - j))
      (reversedDisorder L ω) := by
    unfold interiorEnergy
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [walkPosition_reverseSteps w s j (Finset.mem_Ioo.mp hj).2.le]
  rw [he, interiorEnergy_time_reversal β L a n hL]

end Critical2DKPZ.PolymerCalculus
