/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Scalar product estimates for Laplace-averaged collision diagrams -/

@[expose] public section

namespace Critical2DKPZ.SHF.Tsai

/-- The time comparison, endpoint cancellation, and collision resolvents
leave an exponential word-length majorant with one logarithmic gain per
continuation. All quantities here are scalar. -/
theorem scalar_averaged_diagram_le {n m : ℕ} {P S J D L E rate t : ℝ}
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hL : 0 < L)
    (hD : 1 ≤ D) (hDL : L / 2 ≤ D) (hExp : E ≤ Real.exp 3 * Real.exp (rate * t)) :
    E * (2 : ℝ) ^ (n * (2 * (m + 1) + 1)) * P * (J / D) * (S * J / D) ^ m ≤
      (P * Real.exp 3 * (2 : ℝ) ^ (3 * n) * J) *
        (((2 : ℝ) ^ (2 * n + 1) * S * J) / L) ^ m * Real.exp (rate * t) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hInitial : J / D ≤ J := div_le_self hJ hD
  have hLD : L ≤ 2 * D := by linarith only [hDL]
  have hDiv : S * J / D ≤ (2 * S * J) / L := by
    apply (div_le_div_iff₀ hD0 hL).mpr
    calc
      (S * J) * L ≤ (S * J) * (2 * D) :=
        mul_le_mul_of_nonneg_left hLD (mul_nonneg hS hJ)
      _ = (2 * S * J) * D := by ring
  have hBase : 0 ≤ S * J / D := div_nonneg (mul_nonneg hS hJ) hD0.le
  have hPow := pow_le_pow_left₀ hBase hDiv m
  have hPrefix := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hExp (by positivity : 0 ≤ (2 : ℝ) ^ (n * (2 * (m + 1) + 1)))) hP
  have hPrefixJ := mul_le_mul hPrefix hInitial (div_nonneg hJ hD0.le) (by positivity)
  have hAll := mul_le_mul hPrefixJ hPow (pow_nonneg hBase m) (by positivity)
  have hCost : (2 : ℝ) ^ (n * (2 * (m + 1) + 1)) =
      (2 : ℝ) ^ (3 * n) * ((2 : ℝ) ^ (2 * n)) ^ m := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hB : (2 : ℝ) ^ (2 * n) * ((2 * S * J) / L) =
      ((2 : ℝ) ^ (2 * n + 1) * S * J) / L := by
    rw [pow_succ]
    ring
  calc
    _ ≤ ((Real.exp 3 * Real.exp (rate * t)) *
        (2 : ℝ) ^ (n * (2 * (m + 1) + 1)) * P * J) * ((2 * S * J) / L) ^ m := hAll
    _ = (P * Real.exp 3 * (2 : ℝ) ^ (3 * n) * J) *
        (((2 : ℝ) ^ (2 * n)) ^ m * ((2 * S * J) / L) ^ m) * Real.exp (rate * t) := by
      rw [hCost]
      ring
    _ = _ := by rw [← mul_pow, hB]

end Critical2DKPZ.SHF.Tsai

end
