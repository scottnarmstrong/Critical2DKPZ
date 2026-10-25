/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceStrip
import Mathlib.Tactic

/-! # Entrance bounds with the reciprocal spectator smoothing time -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

private theorem square_exp_decay_le_four {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-u) ≤ 4 := by
  have hv : (u / 2) * Real.exp (-(u / 2)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hv0 : 0 ≤ (u / 2) * Real.exp (-(u / 2)) := by positivity
  have hs := mul_self_le_mul_self hv0 hv
  have hid : u ^ 2 * Real.exp (-u) =
      4 * ((u / 2) * Real.exp (-(u / 2))) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(u / 2)) = -u by ring]
    ring
  rw [hid]
  nlinarith only [hs]

/-- A second use of Gaussian decay trades another inverse displacement square
for one factor of elapsed time. -/
theorem srwKernel_inverse_fourth_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ z : Site, 0 < ‖siteToPlane z‖ →
      srwKernel n z ≤ C * ((n : ℝ) + 1) / ‖siteToPlane z‖ ^ 4 := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := srwKernel_gaussianBound_all_times
  refine ⟨4 * C / c ^ 2, by positivity, fun n z hz => ?_⟩
  let u := c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have he := square_exp_decay_le_four hu
  calc
    _ ≤ C / ((n : ℝ) + 1) * Real.exp (-u) := by
      simpa only [u, neg_div, neg_mul] using hgauss n z
    _ = (C * ((n : ℝ) + 1) / (c ^ 2 * ‖siteToPlane z‖ ^ 4)) *
        (u ^ 2 * Real.exp (-u)) := by
      dsimp only [u]
      field_simp [hc.ne', hz.ne']
    _ ≤ (C * ((n : ℝ) + 1) / (c ^ 2 * ‖siteToPlane z‖ ^ 4)) * 4 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- The inverse free-spectator time can be absorbed into off-diagonal
entrance decay, leaving a bound linear in the number of entrance slices. -/
theorem sum_weighted_entrance_le_inverse_fourth :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : Site), 0 < ‖siteToPlane z‖ →
      (∑ s ∈ Finset.Icc 1 n, srwKernel (2 * s) z / ((s : ℝ) + 1)) ≤
        C * n / ‖siteToPlane z‖ ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := srwKernel_inverse_fourth_bound
  refine ⟨2 * C, by positivity, fun n z hz => ?_⟩
  have hs (s : ℕ) : srwKernel (2 * s) z / ((s : ℝ) + 1) ≤
      2 * C / ‖siteToPlane z‖ ^ 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < s + 1)).mpr
    have hb := hbound (2 * s) z hz
    push_cast at hb
    calc
      _ ≤ C * (2 * (s : ℝ) + 1) / ‖siteToPlane z‖ ^ 4 := hb
      _ ≤ C * (2 * ((s : ℝ) + 1)) / ‖siteToPlane z‖ ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hC.le
        linarith
      _ = _ := by ring
  calc
    _ ≤ ∑ _s ∈ Finset.Icc 1 n, 2 * C / ‖siteToPlane z‖ ^ 4 :=
      Finset.sum_le_sum (fun s _ => hs s)
    _ = _ := by simp [mul_div_assoc]; ring

end Critical2DKPZ.SHF.Moments
