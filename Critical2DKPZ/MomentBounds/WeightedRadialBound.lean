/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.WeightedShellSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Uniform parameter dependence of the weighted radial bound -/

public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- A real power of a square root equals the power with half the exponent. -/
theorem sqrt_rpow_eq_half_exponent {L : ℝ} (hL : 0 ≤ L) (u : ℝ) :
    (Real.sqrt L) ^ u = L ^ (u / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  congr 1
  ring

/-- For `0 < b < 1`, the positive-half-line radial integral is at most `L ^ (-b) / (2 * b * (1 - b))`. -/
theorem integral_weighted_radial_bound {L b : ℝ} (hL : 0 < L) (hb : 0 < b) (hb1 : b < 1) :
    (∫ x in Ioi 0, radialIntegrand L (1 - 2 * b) x) ≤
      L ^ (-b) / (2 * b * (1 - b)) := by
  have hγlo : -1 < 1 - 2 * b := by linarith only [hb1]
  have hγhi : 1 - 2 * b < 1 := by linarith only [hb]
  have h := integral_radialIntegrand_le hL hγlo hγhi (Real.sqrt_pos.mpr hL)
  have hnear : (Real.sqrt L) ^ ((1 - 2 * b) + 1) = L * L ^ (-b) := by
    rw [sqrt_rpow_eq_half_exponent hL.le,
      show ((1 - 2 * b) + 1) / 2 = 1 + -b by ring,
      Real.rpow_add hL, Real.rpow_one]
  have htail : (Real.sqrt L) ^ ((1 - 2 * b) - 1) = L ^ (-b) := by
    rw [sqrt_rpow_eq_half_exponent hL.le]
    congr 1
    ring
  refine h.trans_eq ?_
  rw [hnear, htail, show (1 - 2 * b) + 1 = 2 * (1 - b) by ring,
    show 1 - (1 - 2 * b) = 2 * b by ring]
  have hbne := ne_of_gt hb
  have hbne1 : 1 - b ≠ 0 := (sub_pos.mpr hb1).ne'
  field_simp
  ring

/-- A finite scalar-shell bound with constants uniform in b in (0,1). -/
theorem sum_weighted_radial_bound {L b : ℝ} (hL : 0 < L) (hb : 0 < b) (hb1 : b < 1)
    (K : ℕ) :
    (∑ j ∈ Finset.range K, radialIntegrand L (1 - 2 * b) ((j : ℝ) + 1)) ≤
      4 * L ^ (-b) / (b * (1 - b)) := by
  calc
    _ ≤ 8 * ∫ x in Ioi 0, radialIntegrand L (1 - 2 * b) x :=
      sum_radialIntegrand_le_integral hL (by linarith only [hb1]) (by linarith only [hb]) K
    _ ≤ 8 * (L ^ (-b) / (2 * b * (1 - b))) :=
      mul_le_mul_of_nonneg_left (integral_weighted_radial_bound hL hb hb1) (by norm_num)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end Critical2DKPZ.MomentBounds
