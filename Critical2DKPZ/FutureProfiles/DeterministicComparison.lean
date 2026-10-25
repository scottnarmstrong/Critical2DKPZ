/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.Basic
import Mathlib.Tactic

/-! # Deterministic comparison of probability profiles -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

/-- The total variation of two probability profiles is controlled by its part in a set and the
tail of the comparison profile. -/
theorem smoothed_l1_le_ball_add_tail (μ μ' : Site → ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (hμ' : ∀ w, 0 ≤ μ' w) (hμ1 : HasSum μ 1) (hμ'1 : HasSum μ' 1) (B : Set Site) :
    ∑' y, |μ y - μ' y| ≤ 2 * ∑' y, B.indicator (fun y => |μ y - μ' y|) y +
      2 * ∑' y, Bᶜ.indicator μ' y := by
  let d : Site → ℝ := fun y => |μ y - μ' y|
  have hμs : Summable μ := hμ1.summable
  have hμ's : Summable μ' := hμ'1.summable
  have hμBs : Summable (B.indicator μ) := by
    apply hμs.of_norm_bounded
    intro y
    by_cases hy : y ∈ B
    · simp [Set.indicator, hy, abs_of_nonneg (hμ y)]
    · simpa [Set.indicator, hy] using hμ y
  have hμBcs : Summable (Bᶜ.indicator μ) := by
    apply hμs.of_norm_bounded
    intro y
    by_cases hy : y ∈ B
    · simpa [Set.indicator, hy] using hμ y
    · simp [Set.indicator, hy, abs_of_nonneg (hμ y)]
  have hμ'Bs : Summable (B.indicator μ') := by
    apply hμ's.of_norm_bounded
    intro y
    by_cases hy : y ∈ B
    · simp [Set.indicator, hy, abs_of_nonneg (hμ' y)]
    · simpa [Set.indicator, hy] using hμ' y
  have hμ'Bcs : Summable (Bᶜ.indicator μ') := by
    apply hμ's.of_norm_bounded
    intro y
    by_cases hy : y ∈ B
    · simpa [Set.indicator, hy] using hμ' y
    · simp [Set.indicator, hy, abs_of_nonneg (hμ' y)]
  have hds : Summable d := by
    apply (hμs.add hμ's).of_norm_bounded
    intro y
    dsimp [d]
    calc
      abs (abs (μ y - μ' y)) = abs (μ y - μ' y) := abs_abs _
      _ = |μ y + -μ' y| := by rw [sub_eq_add_neg]
      _ ≤ |μ y| + |-μ' y| := abs_add_le _ _
      _ = μ y + μ' y := by simp [abs_of_nonneg (hμ y), abs_of_nonneg (hμ' y)]
  have hdBs : Summable (B.indicator d) := by
    apply hds.of_norm_bounded
    intro y
    by_cases hy : y ∈ B <;> simp [d, Set.indicator, hy]
  have hdBcs : Summable (Bᶜ.indicator d) := by
    apply hds.of_norm_bounded
    intro y
    by_cases hy : y ∈ B <;> simp [d, Set.indicator, hy]
  have hdecomp (f : Site → ℝ) (y : Site) :
      B.indicator f y + Bᶜ.indicator f y = f y := by
    by_cases hy : y ∈ B <;> simp [Set.indicator, hy]
  have hmassμ : (∑' y, B.indicator μ y) + (∑' y, Bᶜ.indicator μ y) = 1 := by
    calc
      _ = ∑' y, μ y := by
        rw [← hμBs.tsum_add hμBcs]
        exact tsum_congr fun y => hdecomp μ y
      _ = 1 := hμ1.tsum_eq
  have hmassμ' : (∑' y, B.indicator μ' y) + (∑' y, Bᶜ.indicator μ' y) = 1 := by
    calc
      _ = ∑' y, μ' y := by
        rw [← hμ'Bs.tsum_add hμ'Bcs]
        exact tsum_congr fun y => hdecomp μ' y
      _ = 1 := hμ'1.tsum_eq
  have hdiffB :
      (∑' y, B.indicator μ y) - (∑' y, B.indicator μ' y) ≤ ∑' y, B.indicator d y := by
    calc
      _ = ∑' y, (B.indicator μ y - B.indicator μ' y) :=
        (hμBs.tsum_sub hμ'Bs).symm
      _ ≤ ∑' y, B.indicator d y := by
        apply (hμBs.sub hμ'Bs).tsum_le_tsum
        · intro y
          by_cases hy : y ∈ B
          · simpa [Set.indicator, d, hy] using (le_abs_self (μ y - μ' y))
          · simp [Set.indicator, hy]
        · exact hdBs
  have hdiffB' :
      (∑' y, B.indicator μ' y) - (∑' y, B.indicator μ y) ≤ ∑' y, B.indicator d y := by
    calc
      _ = ∑' y, (B.indicator μ' y - B.indicator μ y) :=
        (hμ'Bs.tsum_sub hμBs).symm
      _ ≤ ∑' y, B.indicator d y := by
        apply (hμ'Bs.sub hμBs).tsum_le_tsum
        · intro y
          by_cases hy : y ∈ B
          · simpa [Set.indicator, d, hy, abs_sub_comm] using
              (le_abs_self (μ' y - μ y))
          · simp [Set.indicator, hy]
        · exact hdBs
  have htailMass :
      ∑' y, Bᶜ.indicator μ y ≤ ∑' y, Bᶜ.indicator μ' y + ∑' y, B.indicator d y := by
    linarith [hmassμ, hmassμ', hdiffB']
  have htailAbs :
      ∑' y, Bᶜ.indicator d y ≤ ∑' y, Bᶜ.indicator μ y + ∑' y, Bᶜ.indicator μ' y := by
    calc
      _ ≤ ∑' y, (Bᶜ.indicator μ y + Bᶜ.indicator μ' y) := by
        apply hdBcs.tsum_le_tsum
        · intro y
          by_cases hy : y ∈ B
          · simp [Set.indicator, hy]
          · simpa [Set.indicator, hy, d, sub_eq_add_neg,
              abs_of_nonneg (hμ y), abs_of_nonneg (hμ' y)] using
              (abs_add_le (μ y) (-μ' y))
        · exact hμBcs.add hμ'Bcs
      _ = _ := hμBcs.tsum_add hμ'Bcs
  calc
    _ = (∑' y, B.indicator d y) + ∑' y, Bᶜ.indicator d y := by
      rw [← hdBs.tsum_add hdBcs]
      exact tsum_congr fun y => (hdecomp d y).symm
    _ ≤ 2 * ∑' y, B.indicator d y + 2 * ∑' y, Bᶜ.indicator μ' y := by
      linarith [htailAbs, htailMass]

end Critical2DKPZ.FutureProfiles
