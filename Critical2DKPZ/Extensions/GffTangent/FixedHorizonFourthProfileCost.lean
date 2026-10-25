/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthNormModel
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCellProfileWeights
import Mathlib.Tactic

/-! # Uniform boundary-cost products for the actual cell profiles -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.MomentBounds
open scoped BigOperators Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The collision-vector cost scales as the inverse cube of the spatial weight. -/
theorem fourthCollisionCost_mul_cube {t : ℝ} (ht : 0 < t) :
    fourthCollisionCost t * t ^ 3 = fourthCollisionConstant ^ ((3 : ℝ) / 2) := by
  have hC : 0 ≤ fourthCollisionConstant := zero_le_one.trans fourth_norm_constants_pos.2.2.2.1
  have hpow : (t ^ 2) ^ ((3 : ℝ) / 2) = t ^ 3 := by
    calc
      _ = (t ^ (2 : ℝ)) ^ ((3 : ℝ) / 2) := by rw [Real.rpow_two]
      _ = t ^ ((2 : ℝ) * (3 / 2)) := (Real.rpow_mul ht.le _ _).symm
      _ = _ := by norm_num
  unfold fourthCollisionCost
  rw [Real.div_rpow hC (sq_nonneg t), hpow]
  exact div_mul_cancel₀ _ (pow_ne_zero 3 ht.ne')

/-- A weighted L2 bound proportional to t cancels the collision-vector cost.
Consequently the product of the two boundary costs is uniformly bounded. -/
theorem fourth_boundary_collision_cost_le (t : ℝ) (ht : 0 < t) (L : ℕ)
    (S : Finset Site) (φ : Site → ℝ) (hφ : ∀ y, 0 ≤ φ y)
    {D M K : ℝ} (hM : 0 ≤ M) (_hK : 0 ≤ K)
    (hD : t ^ 2 * L ≤ D)
    (hmass : (∑ y ∈ S, φ y * Real.exp (t * ‖siteToPlane y‖)) ≤ M)
    (hnorm : finiteLpNorm S 2 (fun y => φ y * Real.exp (t * ‖siteToPlane y‖)) ≤ K * t) :
    fourthBoundaryCost t L S φ * fourthCollisionCost t ≤
      fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * D) * 2 * M * K ^ 3 *
        fourthCollisionConstant ^ ((3 : ℝ) / 2) := by
  let P := finiteLpNorm S 2 (fun y => φ y * Real.exp (t * ‖siteToPlane y‖))
  let A := ∑ y ∈ S, φ y * Real.exp (t * ‖siteToPlane y‖)
  have hP : 0 ≤ P := finiteLpNorm_nonneg _ _ _
  have hA : 0 ≤ A := Finset.sum_nonneg (fun y _ => mul_nonneg (hφ y) (Real.exp_nonneg _))
  have hcB : 0 ≤ fourthBoundaryConstant := zero_le_one.trans fourth_norm_constants_pos.1
  have hcC : 0 ≤ fourthCollisionConstant := zero_le_one.trans fourth_norm_constants_pos.2.2.2.1
  have hc : 0 ≤ fourthCollisionCost t := Real.rpow_nonneg (div_nonneg hcC (sq_nonneg t)) _
  have hexp : Real.exp (fourthBoundaryConstant * t ^ 2 * L) ≤
      Real.exp (fourthBoundaryConstant * D) := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hD hcB
  have hcoef : fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * t ^ 2 * L) * 2 * A ≤
      fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * D) * 2 * M :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hcB) (by norm_num))
      hmass hA (by positivity)
  have hpcost : P ^ 3 * fourthCollisionCost t ≤ K ^ 3 * fourthCollisionConstant ^ ((3 : ℝ) / 2) := by
    calc
      _ ≤ (K * t) ^ 3 * fourthCollisionCost t :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP hnorm 3) hc
      _ = K ^ 3 * (fourthCollisionCost t * t ^ 3) := by ring
      _ = _ := by rw [fourthCollisionCost_mul_cube ht]
  calc
    _ = (fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * t ^ 2 * L) * 2 * A) *
        (P ^ 3 * fourthCollisionCost t) := by unfold fourthBoundaryCost; ring
    _ ≤ (fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * D) * 2 * M) *
        (K ^ 3 * fourthCollisionConstant ^ ((3 : ℝ) / 2)) :=
      mul_le_mul hcoef hpcost (mul_nonneg (pow_nonneg hP _) hc) (by positivity)
    _ = _ := by ring

/-- Along a moving macroscopic horizon, the boundary-cost product is bounded
for every family dominated by the actual absolute compact cell profile. -/
theorem eventually_fourth_cell_profile_cost_bounded (f : TestFn) (φ : ℕ → Site → ℝ)
    (hφ : ∀ N w, 0 ≤ φ N w) (hdom : ∀ N w, φ N w ≤ absoluteCellProfile N f w)
    {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      fourthBoundaryCost (fourthWeightScale N) (m N) (fixedHorizonCellSites N f) (φ N) *
        fourthCollisionCost (fourthWeightScale N) ≤ C := by
  obtain ⟨Cf, hCf⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hCf0 : 0 ≤ Cf := (norm_nonneg (f 0)).trans (hCf 0)
  have hfC (x : Plane) : |f x| ≤ Cf := by simpa only [Real.norm_eq_abs] using hCf x
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp f.hasCompactSupport.isBounded
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hfR (x : Plane) (hx : x ∈ tsupport f) : ‖x‖ ≤ R := by
    have h0 : ‖x‖ ≤ R₀ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR₀ hx
    exact h0.trans (le_max_left _ _)
  let M := Real.exp (R + 2) * ∫ x : Plane, |f x|
  let K := Real.sqrt (2 * Cf * Real.exp (R + 2) ^ 2 * (∫ x : Plane, |f x|))
  let D := 2 * |c| + 1
  have hM : 0 ≤ M := mul_nonneg (Real.exp_nonneg _) (integral_nonneg (fun _ => abs_nonneg _))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  let C := fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * D) * 2 * M * K ^ 3 *
    fourthCollisionConstant ^ ((3 : ℝ) / 2)
  have hcB : 0 ≤ fourthBoundaryConstant := zero_le_one.trans fourth_norm_constants_pos.1
  have hcC : 0 ≤ fourthCollisionConstant := zero_le_one.trans fourth_norm_constants_pos.2.2.2.1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hupper : 2 * c < D := by dsimp [D]; linarith only [le_abs_self c]
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_fourthWeightScale_sq_mul hm).eventually (gt_mem_nhds hupper)] with N hN hDN
  exact fourth_boundary_collision_cost_le (fourthWeightScale N) (fourthWeightScale_pos (by omega))
    (m N) (fixedHorizonCellSites N f) (φ N) (hφ N) hM hK hDN.le
    (sum_weighted_dominated_cell_profile_le N f (φ N) (hφ N) (hdom N) hR hfR)
    (finiteLpNorm_weighted_dominated_cell_profile_le N (by omega) f (φ N) (hφ N) (hdom N) hCf0 hfC hR hfR)

end Critical2DKPZ.Extensions.GffTangent
