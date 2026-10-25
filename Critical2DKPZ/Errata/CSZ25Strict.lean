/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic
public import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.Tactic

/-! # Renewal cutoffs and overlap sums -/

public section

namespace Critical2DKPZ.Errata.CSZ25

open Critical2DKPZ Critical2DKPZ.Renewal

/-- At `R_L = L = 2` and `a₊ = k = 1`, the ceiling cutoff holds while the Markov threshold fails. -/
theorem csz25_08_ceiling_does_not_give_markov_threshold :
    (1 : ℤ) ≤ Int.ceil ((2 : ℝ) / (4 * 1)) ∧
      ¬ (1 : ℝ) * (1 : ℝ) ≤ (2 : ℝ) / 4 := by
  norm_num [Int.ceil]

/-- A floor cutoff implies the overlap threshold. -/
theorem csz25_08_floor_gives_markov_threshold {k : ℤ} {aPlus L : ℝ}
    (ha : 0 < aPlus)
    (hk : k ≤ Int.floor (L / (4 * aPlus))) :
    aPlus * (k : ℝ) ≤ L / 4 := by
  have hx : (k : ℝ) ≤ L / (4 * aPlus) := by
    have hk' : (k : ℝ) ≤ (Int.floor (L / (4 * aPlus)) : ℝ) := by exact_mod_cast hk
    exact hk'.trans (Int.floor_le _)
  calc
    aPlus * (k : ℝ) ≤ aPlus * (L / (4 * aPlus)) :=
      mul_le_mul_of_nonneg_left hx ha.le
    _ = L / 4 := by field_simp

/-- The actual one-step mean for the CSZ25 truncated return law. -/
noncomputable def truncatedRenewalStepMean (L : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) L, (n : ℝ) * returnWeight n) / replicaOverlap L

/-- The renewal mean with unit cutoff exceeds the ceiling-based bound used in CSZ25 Lemma 5.4. -/
theorem truncatedRenewalStepMean_one : truncatedRenewalStepMean 1 = 1 := by
  have hR : replicaOverlap 1 = returnWeight 1 := by
    simp [replicaOverlap, returnWeight]
  have hq : 0 < returnWeight 1 := by
    rw [← hR]
    exact replicaOverlap_pos (by norm_num)
  unfold truncatedRenewalStepMean
  rw [show (∑ n ∈ Finset.Icc (1 : ℕ) 1, (n : ℝ) * returnWeight n) = returnWeight 1 by simp]
  rw [hR]
  simp [hq.ne']

/-- For the return-weight renewal law at unit cutoff, the mean at the positive ceiling index exceeds one quarter. -/
theorem csz25_08_actual_L1_ceiling_bound_false (aPlus : ℝ) (ha : 0 < aPlus) :
    ¬ ((Nat.ceil (replicaOverlap 1 / (4 * aPlus)) : ℕ) : ℝ) *
        truncatedRenewalStepMean 1 ≤ (1 : ℝ) / 4 := by
  have hratio : 0 < replicaOverlap 1 / (4 * aPlus) :=
    div_pos (replicaOverlap_pos (by norm_num)) (by positivity)
  have hceil : 0 < Nat.ceil (replicaOverlap 1 / (4 * aPlus)) :=
    Nat.ceil_pos.mpr hratio
  rw [truncatedRenewalStepMean_one]
  intro hbound
  have hcast : (1 : ℝ) ≤ (Nat.ceil (replicaOverlap 1 / (4 * aPlus)) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hceil)
  nlinarith

end Critical2DKPZ.Errata.CSZ25

