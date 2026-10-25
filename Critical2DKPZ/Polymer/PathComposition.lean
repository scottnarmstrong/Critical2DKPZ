/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
import Mathlib.Tactic

/-! Concatenating two walk paths multiplies their Boltzmann weights and joins their endpoints. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- The walk displacement is the sum of its active increments. -/
theorem walkPosition_eq_sum_ite {n : ℕ} (w : Site) (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition w s j = w + ∑ i : Fin n, if i.val < j then srwStep (s i) else 0 := by
  rw [walkPosition, Finset.sum_filter]

/-- Before the joining time, the appended walk agrees with the first walk. -/
theorem walkPosition_append_le {n m : ℕ} (w : Site)
    (s : Fin n → Fin 4) (t : Fin m → Fin 4) (j : ℕ) (hj : j ≤ n) :
    walkPosition w (Fin.append s t) j = walkPosition w s j := by
  rw [walkPosition_eq_sum_ite, walkPosition_eq_sum_ite, Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.append_left, Fin.append_right]
  have hz : (∑ i : Fin m, if n + i.val < j then srwStep (t i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (by omega)]
  rw [hz, add_zero]

/-- After the joining time, the appended walk follows the second walk from the first endpoint. -/
theorem walkPosition_append_add {n m : ℕ} (w : Site)
    (s : Fin n → Fin 4) (t : Fin m → Fin 4) (j : ℕ) :
    walkPosition w (Fin.append s t) (n + j) =
      walkPosition (walkPosition w s n) t j := by
  rw [walkPosition_eq_sum_ite, Fin.sum_univ_add, walkPosition_eq_sum_ite,
    walkPosition_end w s]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.append_left, Fin.append_right,
    Nat.add_lt_add_iff_left]
  have hp : (∑ i : Fin n, if i.val < n + j then srwStep (s i) else 0) =
      ∑ i : Fin n, srwStep (s i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [ite_eq_left (by omega)]
  rw [hp, add_assoc]

/-- The endpoint of an appended walk is the endpoint of its second segment. -/
theorem walkPosition_append_end {n m : ℕ} (w : Site)
    (s : Fin n → Fin 4) (t : Fin m → Fin 4) :
    walkPosition w (Fin.append s t) (n + m) =
      walkPosition (walkPosition w s n) t m :=
  walkPosition_append_add w s t m

/-- A finite time-interval sum splits at an intermediate time. -/
theorem sum_Icc_split (n m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 (n + m), f j =
      (∑ j ∈ Finset.Icc 1 n, f j) + ∑ j ∈ Finset.Icc 1 m, f (n + j) := by
  induction m with
  | zero => simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.sum_empty, add_zero]
  | succ m ih =>
    rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_Icc_succ_top (by omega), Nat.add_succ, add_assoc]
    rfl

/-- The weight of an appended path is the product of its segment weights. -/
theorem pathWeight_append (β : ℝ) (a : ℕ) (w : Site) {n m : ℕ}
    (s : Fin n → Fin 4) (t : Fin m → Fin 4) (ω : Disorder) :
    pathWeight β a w (Fin.append s t) ω =
      pathWeight β a w s ω * pathWeight β (a + n) (walkPosition w s n) t ω := by
  unfold pathWeight
  rw [sum_Icc_split, Real.exp_add]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [walkPosition_append_le w s t j (Finset.mem_Icc.1 hj).2]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [walkPosition_append_add, Nat.add_assoc]

end Critical2DKPZ.Polymer
