/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The cubic comparison in §3 of the four-results note -/

@[expose] public section

namespace Critical2DKPZ.Extensions.Skewness

/-- The cubic whose critical points are the two crossing values. -/
noncomputable def cubicP (a₁ a₂ y : ℝ) : ℝ :=
  y ^ 3 - 3 / 2 * (a₁ + a₂) * y ^ 2 + 3 * a₁ * a₂ * y

variable {a₁ a₂ y z : ℝ}

/-- The left-region polynomial remainder (note §3, case (a)). -/
theorem cubicP_left_remainder (a₁ a₂ y z : ℝ) :
    cubicP a₁ a₂ y - cubicP a₁ a₂ z - (y - z) ^ 3 =
      3 / 2 * (y - z) ^ 2 * ((a₁ - y) + (a₂ - y)) +
        3 * (y - z) * (a₁ - y) * (a₂ - y) := by
  unfold cubicP
  ring

/-- The middle-region polynomial remainder (note §3, case (b)). -/
theorem cubicP_middle_remainder (a₁ a₂ y z : ℝ) :
    2 * (cubicP a₁ a₂ y - cubicP a₁ a₂ z) - (z - y) ^ 3 =
      3 * (z - y) ^ 2 * ((y - a₁) + (a₂ - z)) +
        6 * (z - y) * (y - a₁) * (a₂ - z) := by
  unfold cubicP
  ring

/-- The right-region polynomial remainder (note §3, case (c)). -/
theorem cubicP_right_remainder (a₁ a₂ y z : ℝ) :
    cubicP a₁ a₂ y - cubicP a₁ a₂ z - (y - z) ^ 3 =
      3 / 2 * (y - z) ^ 2 * ((z - a₁) + (z - a₂)) +
        3 * (y - z) * (z - a₁) * (z - a₂) := by
  unfold cubicP
  ring

/-- The outer left region gives the stronger coefficient one. -/
theorem cubicP_sub_left (h : a₁ < a₂) (hzy : z ≤ y) (hy : y ≤ a₁) :
    (y - z) ^ 3 ≤ cubicP a₁ a₂ y - cubicP a₁ a₂ z := by
  have hd := sub_nonneg.mpr hzy
  have h₁ := sub_nonneg.mpr hy
  have h₂ := sub_nonneg.mpr (hy.trans h.le)
  have hp : 0 ≤ 3 / 2 * (y - z) ^ 2 * ((a₁ - y) + (a₂ - y)) +
      3 * (y - z) * (a₁ - y) * (a₂ - y) := by positivity
  rw [← cubicP_left_remainder] at hp
  exact sub_nonneg.mp hp

/-- The middle region gives coefficient one half. -/
theorem cubicP_sub_middle (_h : a₁ < a₂) (h1 : a₁ ≤ y) (hyz : y ≤ z)
    (hz : z ≤ a₂) :
    (z - y) ^ 3 ≤ 2 * (cubicP a₁ a₂ y - cubicP a₁ a₂ z) := by
  have hd := sub_nonneg.mpr hyz
  have h₁ := sub_nonneg.mpr h1
  have h₂ := sub_nonneg.mpr hz
  have hp : 0 ≤ 3 * (z - y) ^ 2 * ((y - a₁) + (a₂ - z)) +
      6 * (z - y) * (y - a₁) * (a₂ - z) := by positivity
  rw [← cubicP_middle_remainder] at hp
  exact sub_nonneg.mp hp

/-- The outer right region gives the stronger coefficient one. -/
theorem cubicP_sub_right (h : a₁ < a₂) (h2 : a₂ ≤ z) (hzy : z ≤ y) :
    (y - z) ^ 3 ≤ cubicP a₁ a₂ y - cubicP a₁ a₂ z := by
  have hd := sub_nonneg.mpr hzy
  have h₁ := sub_nonneg.mpr (h.le.trans h2)
  have h₂ := sub_nonneg.mpr h2
  have hp : 0 ≤ 3 / 2 * (y - z) ^ 2 * ((z - a₁) + (z - a₂)) +
      3 * (y - z) * (z - a₁) * (z - a₂) := by positivity
  rw [← cubicP_right_remainder] at hp
  exact sub_nonneg.mp hp

/-- Quantitative cubic comparison in the three crossing configurations. -/
theorem cubic_comparison (h : a₁ < a₂)
    (hc : (z ≤ y ∧ y ≤ a₁) ∨ (a₁ ≤ y ∧ y ≤ z ∧ z ≤ a₂) ∨ (a₂ ≤ z ∧ z ≤ y)) :
    1 / 2 * |y - z| ^ 3 ≤ cubicP a₁ a₂ y - cubicP a₁ a₂ z := by
  rcases hc with ⟨hzy, hy⟩ | ⟨h1, hyz, hz⟩ | ⟨h2, hzy⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hzy)]
    have hp := cubicP_sub_left h hzy hy
    have hn : 0 ≤ (y - z) ^ 3 := pow_nonneg (sub_nonneg.mpr hzy) _
    linarith only [hp, hn]
  · rw [abs_of_nonpos (sub_nonpos.mpr hyz), neg_sub]
    have hp := cubicP_sub_middle h h1 hyz hz
    linarith only [hp]
  · rw [abs_of_nonneg (sub_nonneg.mpr hzy)]
    have hp := cubicP_sub_right h h2 hzy
    have hn : 0 ≤ (y - z) ^ 3 := pow_nonneg (sub_nonneg.mpr hzy) _
    linarith only [hp, hn]

end Critical2DKPZ.Extensions.Skewness
