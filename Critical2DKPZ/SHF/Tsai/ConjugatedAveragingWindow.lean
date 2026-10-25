/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # A rate-dependent time window for uniform Laplace averaging -/

@[expose] public section

namespace Critical2DKPZ.SHF.Tsai

/-- With `λ = rate + 1/t` and `δ = 1/(λ-c)`, the averaging window stays in
`[t,2t]`, its exponential cost is at most three extra units, and its inverse
length cancels the common endpoint rate factor. -/
theorem conjugated_averaging_window_bounds {c rate t : ℝ} (hc : 0 ≤ c)
    (hrate : 2 * c ≤ rate) (ht : 0 < t) :
    0 < rate + 1 / t - c ∧
      0 < 1 / (rate + 1 / t - c) ∧
      1 / (rate + 1 / t - c) ≤ t ∧
      (rate + 1 / t) * (1 / (rate + 1 / t - c)) ≤ 2 ∧
      (rate + 1 / t) * (t + 1 / (rate + 1 / t - c)) ≤ rate * t + 3 := by
  have hinv : 0 < 1 / t := one_div_pos.mpr ht
  have hrc : 0 ≤ rate - c := by linarith only [hrate, hc]
  have hlower : 1 / t ≤ rate + 1 / t - c := by linarith only [hrc]
  have hden : 0 < rate + 1 / t - c := lt_of_lt_of_le hinv hlower
  have hδ : 0 < 1 / (rate + 1 / t - c) := one_div_pos.mpr hden
  have hδt : 1 / (rate + 1 / t - c) ≤ t := by
    have h := (inv_le_inv₀ hden hinv).mpr hlower
    simpa only [one_div, inv_inv] using h
  have hfactor : (rate + 1 / t) * (1 / (rate + 1 / t - c)) ≤ 2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hrate, hinv]
  refine ⟨hden, hδ, hδt, hfactor, ?_⟩
  have heq : (rate + 1 / t) * t = rate * t + 1 := by
    rw [add_mul, one_div_mul_cancel ht.ne']
  calc
    _ = (rate + 1 / t) * t + (rate + 1 / t) * (1 / (rate + 1 / t - c)) := mul_add _ _ _
    _ ≤ (rate * t + 1) + 2 := add_le_add heq.le hfactor
    _ = rate * t + 3 := by ring

end Critical2DKPZ.SHF.Tsai

end
