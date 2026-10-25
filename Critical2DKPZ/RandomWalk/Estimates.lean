/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.KernelBridge
public import Critical2DKPZ.RandomWalk.GaussianBridge
import Critical2DKPZ.RandomWalk.Port.Walk.PairedLocalCLT
import Critical2DKPZ.RandomWalk.Port.Walk.SRWGaussBound

/-! # Local central limit theorem and Gaussian upper bound for the simple walk kernel -/

public section

namespace Critical2DKPZ

/-- The additive local central limit theorem, uniformly on the allowed parity. -/
theorem srwKernel_localCLT :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site, Even (z 0 + z 1 + n) →
      |srwKernel n z - 2 * heatKernel (n / 2) (siteToPlane z)| ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := LatticeProb.LocalCLT.exists_abs_srwHeat_sub_le (d := 2) (by decide)
  refine ⟨C, hC, fun n hn z hz => ?_⟩
  have ht : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have he := h n hn z (graphNorm_parity_of_even hz)
  rw [← srwKernel_eq_srwHeat, ctGauss_two_eq_heatKernel ht] at he
  norm_num at he
  simpa only [div_eq_mul_inv] using he

/-- Gaussian decay, with an absolute positive rate independent of time and site. -/
theorem srwKernel_gaussianBound :
    ∃ C c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site,
      srwKernel n z ≤ C / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) := by
  refine ⟨9 * LatticeProb.greenConst 2, 1 / 40, by norm_num, fun n hn z => ?_⟩
  have h := LatticeProb.srwHeat_gaussian (d := 2) (by decide) hn z
  rw [← srwKernel_eq_srwHeat] at h
  norm_num [Real.rpow_neg_one] at h
  have ht : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he := gaussian_exponent_le ht (sq_nonneg ‖siteToPlane z‖)
    (norm_siteToPlane_sq_le_graphNorm_sq z)
  calc srwKernel n z
      ≤ 9 * LatticeProb.greenConst 2 * (n : ℝ)⁻¹ *
          Real.exp (-(LatticeProb.graphNorm z : ℝ) ^ 2 / (8 * ((n : ℝ) + 4))) := h
    _ ≤ 9 * LatticeProb.greenConst 2 * (n : ℝ)⁻¹ *
          Real.exp (-(1 / 40 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (mul_nonneg (mul_nonneg (by norm_num) (LatticeProb.greenConst_nonneg 2))
          (inv_nonneg.mpr (Nat.cast_nonneg n)))
    _ = _ := by simp only [div_eq_mul_inv]

end Critical2DKPZ
