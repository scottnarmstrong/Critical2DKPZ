/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.ReversePaths
import Mathlib.Tactic

/-! Multiplying a terminal-inclusive polymer kernel by its initial disorder factor equals the reversed transpose multiplied by the original terminal disorder factor. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

/-- Reversal swaps the start and terminal site of every admissible walk. -/
theorem walkPosition_reverse_endpoint_iff {n : ℕ} (w z : Site) (s : Fin n → Fin 4) :
    walkPosition z (reverseSteps s) n = w ↔ walkPosition w s n = z := by
  have he := walkPosition_reverseSteps w s n le_rfl
  simp only [Nat.sub_self, Polymer.walkPosition_zero] at he
  constructor
  · intro h
    rw [Polymer.walkPosition_eq_start_add] at h he
    exact (add_right_cancel (h.trans he.symm)).symm
  · intro h
    rwa [h] at he

/-- The two terminal-inclusive energies differ by precisely their endpoint noises. -/
theorem pathEnergy_time_reversal (β : ℝ) (L a n : ℕ) (hL : a + n ≤ L)
    (w : Site) (s : Fin n → Fin 4) (ω : Disorder) :
    β * ω (a, w) + pathEnergy β a w s ω =
      β * ω (a + n, walkPosition w s n) +
        pathEnergy β (L - (a + n)) (walkPosition w s n) (reverseSteps s)
          (reversedDisorder L ω) := by
  by_cases hn : n = 0
  · subst n
    simp only [pathEnergy, Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      Finset.sum_empty, add_zero, Polymer.walkPosition_zero]
  · have hn1 : 1 ≤ n := by omega
    have he := walkPosition_reverseSteps w s n le_rfl
    simp only [Nat.sub_self, Polymer.walkPosition_zero] at he
    rw [pathEnergy_eq_interior_add_terminal β a n hn1,
      pathEnergy_eq_interior_add_terminal β (L - (a + n)) n hn1,
      interiorEnergy_reverseSteps β L a n hL, he]
    have ht : reflectedTime L (L - (a + n) + n) = a := by
      unfold reflectedTime
      split_ifs <;> omega
    simp only [reversedDisorder, Gaussian.reindexDisorder, timeReversalIndex,
      Equiv.coe_fn_mk, ht]
    ring

/-- Exact terminal-inclusive kernel transpose, including both endpoint multipliers. -/
theorem pointToPoint_time_reversal (β : ℝ) (L a n : ℕ) (hL : a + n ≤ L)
    (w z : Site) (ω : Disorder) :
    Real.exp (β * ω (a, w)) * pointToPoint β a n w z ω =
      Real.exp (β * ω (a + n, z)) *
        pointToPoint β (L - (a + n)) n z w (reversedDisorder L ω) := by
  conv_rhs =>
    rw [Polymer.pointToPoint_eq_sum,
      ← Equiv.sum_comp (reverseStepsEquiv n)]
  rw [Polymer.pointToPoint_eq_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change Real.exp (β * ω (a, w)) *
    ((4 : ℝ)⁻¹ ^ n * Real.exp (pathEnergy β a w s ω) *
      if walkPosition w s n = z then 1 else 0) =
    Real.exp (β * ω (a + n, z)) *
    ((4 : ℝ)⁻¹ ^ n * Real.exp (pathEnergy β (L - (a + n)) z (reverseSteps s)
      (reversedDisorder L ω)) * if walkPosition z (reverseSteps s) n = w then 1 else 0)
  by_cases hs : walkPosition w s n = z
  · rw [ite_eq_left hs, ite_eq_left ((walkPosition_reverse_endpoint_iff w z s).mpr hs),
      mul_one, mul_one]
    have he : Real.exp (β * ω (a, w)) * Real.exp (pathEnergy β a w s ω) =
        Real.exp (β * ω (a + n, z)) *
          Real.exp (pathEnergy β (L - (a + n)) z (reverseSteps s) (reversedDisorder L ω)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simpa only [hs] using pathEnergy_time_reversal β L a n hL w s ω
    calc
      _ = (4 : ℝ)⁻¹ ^ n * (Real.exp (β * ω (a, w)) *
          Real.exp (pathEnergy β a w s ω)) := by ring
      _ = _ := by rw [he]; ring
  · rw [ite_eq_right hs,
      ite_eq_right (fun h => hs ((walkPosition_reverse_endpoint_iff w z s).mp h)),
      mul_zero, mul_zero, mul_zero, mul_zero]

end Critical2DKPZ.PolymerCalculus
