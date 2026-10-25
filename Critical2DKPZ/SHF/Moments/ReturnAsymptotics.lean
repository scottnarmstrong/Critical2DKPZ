/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Estimates
import Mathlib.Tactic

/-! # Return asymptotics at every accessible fixed gap -/

public section

namespace Critical2DKPZ.SHF.Moments

/-- For a nonnegative argument the distance from its negative exponential to one is at most the argument. -/
theorem abs_exp_neg_sub_one_le {u : ℝ} (hu : 0 ≤ u) :
    |Real.exp (-u) - 1| ≤ u := by
  have hupper : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith only [Real.add_one_le_exp (-u)]

/-- The planar heat kernel at a fixed lattice gap differs from its value at zero by an inverse squared time bound. -/
theorem heatKernel_fixed_gap_error {n : ℝ} (hn : 0 < n) (z : Site) :
    |2 * heatKernel n (siteToPlane z) - (1 / Real.pi) * n⁻¹| ≤
      (‖siteToPlane z‖ ^ 2 / (2 * Real.pi)) / n ^ 2 := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : 2 * heatKernel n (siteToPlane z) - (1 / Real.pi) * n⁻¹ =
      ((1 / Real.pi) * n⁻¹) * (Real.exp (- (‖siteToPlane z‖ ^ 2 / (2 * n))) - 1) := by
    rw [heatKernel, neg_div]
    field_simp
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / Real.pi) * n⁻¹)]
  calc
    _ ≤ ((1 / Real.pi) * n⁻¹) * (‖siteToPlane z‖ ^ 2 / (2 * n)) :=
      mul_le_mul_of_nonneg_left (abs_exp_neg_sub_one_le (by positivity)) (by positivity)
    _ = _ := by field_simp

/-- The same `1/π` return constant at every fixed even gap, with a summable error. -/
theorem srwKernel_even_gap_localCLT (z : Site) (hz : Even (z 0 + z 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |srwKernel (2 * n) z - (1 / Real.pi) * (n : ℝ)⁻¹| ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := srwKernel_localCLT
  refine ⟨C + ‖siteToPlane z‖ ^ 2 / (2 * Real.pi), by positivity, fun n hn => ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hphase : Even (z 0 + z 1 + (2 * n : ℕ)) := by
    apply hz.add
    refine ⟨(n : ℤ), ?_⟩
    push_cast
    ring
  have he := h (2 * n) (by omega) z hphase
  have ht : ((2 * n : ℕ) : ℝ) / 2 = n := by push_cast; ring
  rw [ht] at he
  calc
    _ ≤ |srwKernel (2 * n) z - 2 * heatKernel (n : ℝ) (siteToPlane z)| +
        |2 * heatKernel (n : ℝ) (siteToPlane z) - (1 / Real.pi) * (n : ℝ)⁻¹| :=
      abs_sub_le _ _ _
    _ ≤ C / ((2 * n : ℕ) : ℝ) ^ 2 +
        (‖siteToPlane z‖ ^ 2 / (2 * Real.pi)) / (n : ℝ) ^ 2 :=
      add_le_add he (heatKernel_fixed_gap_error hnr z)
    _ ≤ C / (n : ℝ) ^ 2 +
        (‖siteToPlane z‖ ^ 2 / (2 * Real.pi)) / (n : ℝ) ^ 2 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_left hC.le (by positivity)
      push_cast
      nlinarith only [sq_nonneg (n : ℝ)]
    _ = _ := by rw [add_div]

end Critical2DKPZ.SHF.Moments
