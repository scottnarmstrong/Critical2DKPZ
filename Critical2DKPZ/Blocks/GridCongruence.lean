/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
public import Critical2DKPZ.Blocks.StringSum
import Mathlib.Tactic

/-! # Discrepancy identities under agreement on a finite time grid -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- A finite discrepancy string only uses the indicated prefix of its time grid. -/
theorem discrepancyString_congr_below (β : ℝ) (t s : ℕ → ℕ) (V u k : ℕ)
    (heq : ∀ i, i ≤ V → t i = s i) (huk : u + k ≤ V) :
    discrepancyString β t u k = discrepancyString β s u k := by
  revert huk
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro huk
    have hstr := ih (by omega)
    have hhi := heq (u + k) (by omega)
    have hlo := heq (u + k - 1) (by omega)
    funext x y ω
    simp only [discrepancyString, hstr, blockDiscrepancy, blockKernel, hhi, hlo]

/-- Closed discrepancy masses depend only on grid indices at most their final block. -/
theorem closedDiscrepancy_congr_below (β : ℝ) (t s : ℕ → ℕ) {u v : ℕ}
    (hu : 1 ≤ u) (huv : u ≤ v) (heq : ∀ i, i ≤ v → t i = s i) :
    closedDiscrepancy β t u v = closedDiscrepancy β s u v := by
  have hu0 : 0 < u := lt_of_lt_of_le Nat.zero_lt_one hu
  have hpred : u - 1 ≤ v := (Nat.sub_lt hu0 Nat.zero_lt_one).le.trans huv
  have hstr := discrepancyString_congr_below β t s v u (v - u) heq (by omega)
  funext ω
  simp only [closedDiscrepancy, heq (u - 1) hpred, heq (v - 1) (Nat.sub_le _ _),
    heq v le_rfl, hstr]

/-- A collision string depends only on the two endpoints of each of its occupied blocks. -/
theorem stringTail_congr (σ2 : ℝ) (t s : ℕ → ℕ) (is : List ℕ)
    (heq : ∀ i ∈ is, t (i - 1) = s (i - 1) ∧ t i = s i) :
    stringTail σ2 t is = stringTail σ2 s is := by
  revert heq
  induction is with
  | nil => intro _; rfl
  | cons i is ih =>
    intro heq
    have hcur := heq i List.mem_cons_self
    have htail := ih (fun j hj => heq j (List.mem_cons_of_mem i hj))
    funext b y
    simp only [stringTail, hcur.1, hcur.2, htail]

/-- The collision sum also depends only on the grid prefix through the final block. -/
theorem closedStringSum_congr_below (σ2 : ℝ) (t s : ℕ → ℕ) {u v : ℕ}
    (huv : u ≤ v) (heq : ∀ i, i ≤ v → t i = s i) :
    closedStringSum σ2 t u v = closedStringSum σ2 s u v := by
  unfold closedStringSum
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.1 hS
  have hlist (i : ℕ) (hi : i ∈ S.sort (· ≤ ·) ++ [v]) : i ≤ v := by
    rcases List.mem_append.1 hi with hi | hi
    · exact (Finset.mem_Ioo.1 (hsub ((Finset.mem_sort _).1 hi))).2.le
    · have hiv : i = v := List.mem_singleton.1 hi
      exact hiv ▸ le_rfl
  have htail := stringTail_congr σ2 t s (S.sort (· ≤ ·) ++ [v])
    (fun i hi => ⟨heq (i - 1) ((Nat.sub_le _ _).trans (hlist i hi)), heq i (hlist i hi)⟩)
  simp only [heq (u - 1) ((Nat.sub_le _ _).trans huv), heq u huv, htail]

/-- A grid monotone through `v` becomes globally monotone by holding its last value fixed. -/
theorem monotone_cappedGrid {t : ℕ → ℕ} {v : ℕ}
    (ht : MonotoneOn t (Set.Iic v)) : Monotone (fun i => t (min i v)) := by
  intro i j hij
  exact ht (min_le_right i v) (min_le_right j v) (min_le_min_right v hij)

end Critical2DKPZ.Blocks
