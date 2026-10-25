/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCellProfiles
public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
import Mathlib.Tactic

/-! # Weighted cell-profile bounds at the CCR exponential scale -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The finite real exponent-two norm squares to the usual quadratic sum. -/
theorem finiteLpNorm_two_sq (S : Finset Site) (F : Site → ℝ) :
    finiteLpNorm S 2 F ^ 2 = ∑ w ∈ S, F w ^ 2 := by
  have he : finiteLpNorm S 2 F = Real.sqrt (∑ w ∈ S, F w ^ 2) := by
    simp only [finiteLpNorm, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]
  rw [he, Real.sq_sqrt (Finset.sum_nonneg (fun w _ => sq_nonneg (F w)))]

/-- The weighted mass is bounded uniformly in the lattice scale for every
nonnegative profile dominated by the absolute cell masses. -/
theorem sum_weighted_dominated_cell_profile_le (N : ℕ) (f : TestFn) (φ : Site → ℝ)
    (hφ : ∀ w, 0 ≤ φ w) (hdom : ∀ w, φ w ≤ absoluteCellProfile N f w)
    {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ x ∈ tsupport f, ‖x‖ ≤ R) :
    (∑ w ∈ fixedHorizonCellSites N f,
      φ w * Real.exp (fourthWeightScale N * ‖siteToPlane w‖)) ≤
        Real.exp (R + 2) * ∫ x : Plane, |f x| := by
  calc
    _ ≤ ∑ w ∈ fixedHorizonCellSites N f, φ w * Real.exp (R + 2) :=
      Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left
        (exp_fourthWeightScale_site_le N f hR hfR hw) (hφ w))
    _ = Real.exp (R + 2) * ∑ w ∈ fixedHorizonCellSites N f, φ w := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dominated_cell_profile_le N f φ hdom) (Real.exp_nonneg _)

/-- The weighted L2 norm of the actual cell profile is of order the lattice
weight scale. This applies to both signs of the signed cell coefficients. -/
theorem finiteLpNorm_weighted_dominated_cell_profile_le (N : ℕ) (hN : 0 < N)
    (f : TestFn) (φ : Site → ℝ) (hφ : ∀ w, 0 ≤ φ w)
    (hdom : ∀ w, φ w ≤ absoluteCellProfile N f w)
    {C R : ℝ} (hC : 0 ≤ C) (hfC : ∀ x : Plane, |f x| ≤ C)
    (hR : 0 ≤ R) (hfR : ∀ x ∈ tsupport f, ‖x‖ ≤ R) :
    finiteLpNorm (fixedHorizonCellSites N f) 2
      (fun w => φ w * Real.exp (fourthWeightScale N * ‖siteToPlane w‖)) ≤
      Real.sqrt (2 * C * Real.exp (R + 2) ^ 2 * (∫ x : Plane, |f x|)) * fourthWeightScale N := by
  let F : Site → ℝ := fun w => φ w * Real.exp (fourthWeightScale N * ‖siteToPlane w‖)
  let U := (4 * C / (N : ℝ)) * Real.exp (R + 2)
  let K := 2 * C * Real.exp (R + 2) ^ 2 * (∫ x : Plane, |f x|)
  have hF (w : Site) : 0 ≤ F w := mul_nonneg (hφ w) (Real.exp_nonneg _)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hL1 : 0 ≤ ∫ x : Plane, |f x| := integral_nonneg (fun _ => abs_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hFU (w : Site) (hw : w ∈ fixedHorizonCellSites N f) : F w ≤ U := by
    exact mul_le_mul ((hdom w).trans (absoluteCellProfile_le N hN f hC hfC w))
      (exp_fourthWeightScale_site_le N f hR hfR hw) (Real.exp_nonneg _) (by positivity)
  have hsq : (∑ w ∈ fixedHorizonCellSites N f, F w ^ 2) ≤
      U * (Real.exp (R + 2) * ∫ x : Plane, |f x|) := by
    calc
      _ ≤ ∑ w ∈ fixedHorizonCellSites N f, U * F w := by
        apply Finset.sum_le_sum
        intro w hw
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hFU w hw) (hF w)
      _ = U * ∑ w ∈ fixedHorizonCellSites N f, F w := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_weighted_dominated_cell_profile_le N f φ hφ hdom hR hfR) hU
  have hrhs : (Real.sqrt K * fourthWeightScale N) ^ 2 =
      U * (Real.exp (R + 2) * ∫ x : Plane, |f x|) := by
    rw [mul_pow, Real.sq_sqrt hK, fourthWeightScale_sq hN]
    dsimp only [K, U]
    ring
  apply (sq_le_sq₀ (finiteLpNorm_nonneg _ _ _) (mul_nonneg (Real.sqrt_nonneg K)
    (fourthWeightScale_nonneg N))).mp
  rw [finiteLpNorm_two_sq, hrhs]
  exact hsq

end Critical2DKPZ.Extensions.GffTangent
