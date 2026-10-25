/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! # Scalar cancellation in the Laplace-averaged diagram bound -/

@[expose] public section

open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The inverse window length cancels the endpoint product. The remaining
nonnegative extended-real coefficient is the literal real scalar majorant. -/
theorem ennreal_average_endpoint_cancel {O I : ℝ≥0∞} {P S J den E K : ℝ} (m : ℕ)
    (hden : 0 < den) (hP : 0 ≤ P) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hEndpoint : O * I = ENNReal.ofReal (P / den)) :
    (ENNReal.ofReal den * ENNReal.ofReal E * ENNReal.ofReal K) *
      (O * (ENNReal.ofReal J * ((ENNReal.ofReal S * ENNReal.ofReal J) ^ m * I))) =
        ENNReal.ofReal (E * K * P * J * (S * J) ^ m) := by
  have hcancel : ENNReal.ofReal den * (O * I) = ENNReal.ofReal P := by
    rw [hEndpoint, ← ENNReal.ofReal_mul hden.le]
    congr 1
    field_simp
  calc
    _ = ENNReal.ofReal E * ENNReal.ofReal K * (ENNReal.ofReal den * (O * I)) *
        ENNReal.ofReal J * (ENNReal.ofReal S * ENNReal.ofReal J) ^ m := by ac_rfl
    _ = ENNReal.ofReal E * ENNReal.ofReal K * ENNReal.ofReal P *
        ENNReal.ofReal J * ENNReal.ofReal ((S * J) ^ m) := by
      rw [hcancel, ← ENNReal.ofReal_mul hS, ← ENNReal.ofReal_pow (mul_nonneg hS hJ) m]
    _ = _ := by
      rw [← ENNReal.ofReal_mul hE,
        ← ENNReal.ofReal_mul (mul_nonneg hE hK),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hE hK) hP),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hE hK) hP) hJ)]

end Critical2DKPZ.SHF.Tsai

end
