/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Scalar estimate for the endpoint perturbation -/

@[expose] public section

namespace Critical2DKPZ.NonGaussian

/-- For `|a| ≤ 1` and `0 < ε ≤ 1/2`, one has `|ε⁻¹ log (1 + ε a) − a| ≤ 2ε`. -/
theorem abs_inv_mul_log_one_add_sub_le {ε a : ℝ} (hε : 0 < ε) (hε₂ : ε ≤ 1 / 2)
    (ha : |a| ≤ 1) :
    |ε⁻¹ * Real.log (1 + ε * a) - a| ≤ 2 * ε := by
  let q : ℝ := |ε * a|
  have hq_nonneg : 0 ≤ q := abs_nonneg _
  have hq_le : q ≤ ε := by
    dsimp [q]
    rw [abs_mul, abs_of_pos hε]
    calc
      ε * |a| ≤ ε * 1 := mul_le_mul_of_nonneg_left ha hε.le
      _ = ε := by ring
  have hq_lt : q < 1 := lt_of_le_of_lt hq_le (by linarith)
  have hseries := Real.abs_log_sub_add_sum_range_le (x := -(ε * a)) (by
    simpa [q] using hq_lt) 1
  have hlog : |Real.log (1 + ε * a) - ε * a| ≤ q ^ 2 / (1 - q) := by
    simpa [q, Finset.sum_range_one, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg] using hseries
  have hden : 0 < 1 - q := by linarith
  have hdenε : 0 < 1 - ε := by linarith
  have hq_sq : q ^ 2 ≤ ε ^ 2 := by nlinarith [hq_nonneg, hq_le]
  have hquot : q ^ 2 / (1 - q) ≤ ε ^ 2 / (1 - ε) := by
    rw [div_le_div_iff₀ hden hdenε]
    have hfactor : 1 - ε ≤ 1 - q := by linarith
    calc
      q ^ 2 * (1 - ε) ≤ ε ^ 2 * (1 - ε) :=
        mul_le_mul_of_nonneg_right hq_sq (by linarith)
      _ ≤ ε ^ 2 * (1 - q) :=
        mul_le_mul_of_nonneg_left hfactor (sq_nonneg ε)
  have hbound : ε⁻¹ * (q ^ 2 / (1 - q)) ≤ 2 * ε := by
    calc
      ε⁻¹ * (q ^ 2 / (1 - q)) ≤ ε⁻¹ * (ε ^ 2 / (1 - ε)) :=
        mul_le_mul_of_nonneg_left hquot (inv_nonneg.mpr hε.le)
      _ = ε / (1 - ε) := by field_simp
      _ ≤ 2 * ε := by
        rw [div_le_iff₀ hdenε]
        nlinarith [hε₂]
  calc
    |ε⁻¹ * Real.log (1 + ε * a) - a| =
        ε⁻¹ * |Real.log (1 + ε * a) - ε * a| := by
          rw [show ε⁻¹ * Real.log (1 + ε * a) - a =
            ε⁻¹ * (Real.log (1 + ε * a) - ε * a) by field_simp,
            abs_mul, abs_of_pos (inv_pos.mpr hε)]
    _ ≤ ε⁻¹ * (q ^ 2 / (1 - q)) :=
      mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hε.le)
    _ ≤ 2 * ε := hbound

end Critical2DKPZ.NonGaussian

end
