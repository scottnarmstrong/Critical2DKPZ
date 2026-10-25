/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationScaledBall
import Mathlib.Tactic

/-! # Diffusive scaling of the two weighted boundary costs -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

/-- The combined initial-indicator and terminal-collision costs have an `O(N^h)` bound, matching the reciprocal cell normalization. -/
theorem collisionWord_weightedBoundary_cardinality_scale {h : ℕ} (hh : 1 ≤ h)
    (N K c a : ℝ) (hN : 0 ≤ N) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hacard : a ≤ K * N) :
    a * Real.sqrt a ^ (h - 1) * (c * Real.sqrt N) ^ (h - 1) ≤
      K * (Real.sqrt K * c) ^ (h - 1) * N ^ h := by
  have hsqrt : Real.sqrt a ≤ Real.sqrt K * Real.sqrt N := by
    rw [← Real.sqrt_mul hK]
    exact Real.sqrt_le_sqrt hacard
  have hbase : (Real.sqrt K * Real.sqrt N) * (c * Real.sqrt N) =
      (Real.sqrt K * c) * N := by
    calc
      _ = Real.sqrt K * c * Real.sqrt N ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hN]
  have hpow : N ^ h = N * N ^ (h - 1) := by
    calc
      N ^ h = N ^ ((h - 1) + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ (K * N) * (Real.sqrt K * Real.sqrt N) ^ (h - 1) *
        (c * Real.sqrt N) ^ (h - 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
      exact mul_le_mul hacard (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt _)
        (pow_nonneg (Real.sqrt_nonneg _) _) (mul_nonneg hK hN)
    _ = K * N * ((Real.sqrt K * Real.sqrt N) * (c * Real.sqrt N)) ^ (h - 1) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hbase, mul_pow, hpow]; ring

end Critical2DKPZ.SHF.Moments

end
