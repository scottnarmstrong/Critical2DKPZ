/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitUniformSingleMass

/-! # Free-spectator smoothing of a future collision gap -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- A free spectator turns a summable nonnegative future-gap profile into a
uniform bound with the reciprocal free-time scale. -/
theorem exists_srwKernel_gap_smoothing_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Site) (F : Site → ℝ),
      (∀ z, 0 ≤ F z) → Summable F →
      (∑' z : Site, srwKernel m (z - a) * F z) ≤
        (C / ((m : ℝ) + 1)) * ∑' z : Site, F z := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := srwKernel_gaussianBound_all_times
  refine ⟨C, hC, fun m a F hF hsum => ?_⟩
  have hwalk (z : Site) : srwKernel m (z - a) ≤ C / ((m : ℝ) + 1) := by
    have he : Real.exp (-c * ‖siteToPlane (z - a)‖ ^ 2 / ((m : ℝ) + 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _))
        (by positivity)
    exact (hgauss m (z - a)).trans (mul_le_of_le_one_right (by positivity) he)
  have hprod : Summable (fun z : Site => srwKernel m (z - a) * F z) := by
    apply summable_of_ne_finset_zero (s := endpoints a m)
    intro z hz
    rw [srwKernel_eq_zero_of_not_mem m a z hz, zero_mul]
  calc
    _ ≤ ∑' z : Site, (C / ((m : ℝ) + 1)) * F z :=
      Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_right (hwalk z) (hF z))
        hprod (hsum.mul_left _)
    _ = _ := tsum_mul_left


end Critical2DKPZ.SHF.Moments
