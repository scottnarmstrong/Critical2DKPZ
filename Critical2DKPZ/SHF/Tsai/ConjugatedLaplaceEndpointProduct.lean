/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceWordConstants
import Mathlib.Tactic

/-! # Exact cancellation of complementary Laplace endpoint powers -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The positive scalar coefficient left by the two complementary endpoints. -/
def conjugatedEndpointProductConstant (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) : ℝ :=
  conjugatedEndpointShift n hp ha ^ 2 * Real.Gamma (1 / p) * Real.Gamma (1 - 1 / p)

/-- Complementary endpoint powers multiply to exactly one reciprocal rate,
the factor cancelled by the adjustable Laplace averaging interval. -/
theorem conjugatedEndpointLaplaceFactor_mul_complement {n : ℕ} {p a rate : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) (hrate : conjugatedEndpointShift n hp ha < rate) :
    conjugatedEndpointLaplaceFactor n hp ha rate (1 / p) *
      conjugatedEndpointLaplaceFactor n hp ha rate (1 - 1 / p) =
        ENNReal.ofReal (conjugatedEndpointProductConstant n hp ha *
          (1 / (rate - conjugatedEndpointShift n hp ha))) := by
  let c : ℝ := conjugatedEndpointShift n hp ha
  let r : ℝ := 1 / (rate - c)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hc : 0 ≤ c := zero_le_one.trans (conjugatedEndpointShift_ge_one n hp ha)
  have hr : 0 < r := one_div_pos.mpr (sub_pos.mpr hrate)
  have hGamma : 0 ≤ Real.Gamma (1 / p) := (Real.Gamma_pos_of_pos (by positivity)).le
  have hOut : 0 ≤ c * Real.Gamma (1 / p) * r ^ (1 / p) :=
    mul_nonneg (mul_nonneg hc hGamma) (Real.rpow_nonneg hr.le _)
  change ENNReal.ofReal (c * Real.Gamma (1 / p) * r ^ (1 / p)) *
      ENNReal.ofReal (c * Real.Gamma (1 - 1 / p) * r ^ (1 - 1 / p)) =
        ENNReal.ofReal ((c ^ 2 * Real.Gamma (1 / p) * Real.Gamma (1 - 1 / p)) * r)
  rw [← ENNReal.ofReal_mul hOut]
  congr 1
  calc
    _ = (c ^ 2 * Real.Gamma (1 / p) * Real.Gamma (1 - 1 / p)) *
        (r ^ (1 / p) * r ^ (1 - 1 / p)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hr, show 1 / p + (1 - 1 / p) = 1 by ring, Real.rpow_one]

/-- The endpoint product coefficient is strictly positive for every
finite exponent strictly larger than one. -/
theorem conjugatedEndpointProductConstant_pos (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    0 < conjugatedEndpointProductConstant n hp ha := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hinv : 1 / p < 1 := (div_lt_iff₀ hp0).mpr (by simpa only [one_mul] using hp)
  have hc : 0 < conjugatedEndpointShift n hp ha :=
    lt_of_lt_of_le zero_lt_one (conjugatedEndpointShift_ge_one n hp ha)
  unfold conjugatedEndpointProductConstant
  exact mul_pos
    (mul_pos (sq_pos_of_pos hc) (Real.Gamma_pos_of_pos (one_div_pos.mpr hp0)))
    (Real.Gamma_pos_of_pos (sub_pos.mpr hinv))

end Critical2DKPZ.SHF.Tsai

end
