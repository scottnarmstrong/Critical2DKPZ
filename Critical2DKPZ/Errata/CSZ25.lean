/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # The Markov cutoff rounding in CSZ25, Lemma 5.4

Source: arXiv:2504.06128v2, proof of Lemma 5.4.
-/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata

/-- A ceiling cutoff admits `k = 1` when the real threshold is `1/4`. -/
theorem csz25_ceiling_threshold_false :
    (1 : ℕ) ≤ ⌈(1 : ℝ) / (4 * 1)⌉₊ ∧
      ¬ ((1 : ℝ) / 1 * 1 * 1 ≤ 1 / 4) := by
  norm_num

/-- A floor cutoff implies the deterministic Markov threshold. -/
theorem csz25_floor_markov_threshold {R a L : ℝ} {k : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hL : 0 ≤ L) (hk : k ≤ ⌊R / (4 * a)⌋₊) :
    (k : ℝ) / R * a * L ≤ L / 4 := by
  have hkR : (k : ℝ) ≤ R / (4 * a) :=
    (by exact_mod_cast hk : (k : ℝ) ≤ (⌊R / (4 * a)⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  have hratio : (k : ℝ) * (4 * a) / R ≤ 1 :=
    (div_le_one hR).mpr ((le_div_iff₀ (by positivity : 0 < 4 * a)).mp hkR)
  calc
    _ = ((k : ℝ) * (4 * a) / R) * (L / 4) := by ring
    _ ≤ 1 * (L / 4) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = L / 4 := one_mul _

end Critical2DKPZ.Errata
