/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CoordinateSum
public import Critical2DKPZ.MomentBounds.PairGeometry
public import Critical2DKPZ.MomentBounds.WeightedLatticeSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # The two free-coordinate sum in the LZ21 collision estimate -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The final two-coordinate summand after the other collision coordinates are peeled. -/
def twoCoordinateKernel (L a p : ℝ) (u : Site) (v : Site × Site) : ℝ :=
  (L + ‖siteToPlane (v.1 - u)‖ ^ 2 + ‖siteToPlane (v.2 - u)‖ ^ 2) ^ (-2 : ℝ) *
    (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p)

/-- The pair kernel after the linear change of the two active coordinates. -/
def transformedPairKernel (L a p : ℝ) (v : Site × Site) : ℝ :=
  (L + ‖siteToPlane v.1‖ ^ 2 + ‖siteToPlane v.2‖ ^ 2) ^ (-2 : ℝ) *
    (1 + ‖siteToPlane v.1‖ ^ (2 * a)) ^ (-p)


/-- The two-coordinate kernel is bounded by four times the transformed pair kernel. -/
theorem twoCoordinateKernel_le_transformed {L a p : ℝ} (hL : 0 < L)
    (u : Site) (v : Site × Site) :
    twoCoordinateKernel L a p u v ≤
      4 * transformedPairKernel L a p (pairSumDifference u v) := by
  let w := v.1 - v.2
  let z := v.1 + v.2 - u - u
  have hR : 0 < L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2 := by positivity
  have hD : 0 < (L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) / 2 := by positivity
  have hden :
      (L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) / 2 ≤
        L + ‖siteToPlane (v.1 - u)‖ ^ 2 + ‖siteToPlane (v.2 - u)‖ ^ 2 := by
    have hid := pair_sum_difference_norm_identity v.1 v.2 u
    dsimp [w, z] at hid ⊢
    nlinarith only [hL, hid]
  have hpow := Real.rpow_le_rpow_of_nonpos hD hden (by norm_num : (-2 : ℝ) ≤ 0)
  have hhalf : ((L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) / 2) ^ (-2 : ℝ) =
      4 * (L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ) := by
    have hpos : 0 < L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2 := hR
    rw [show (L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) / 2 =
      (L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) * (2 : ℝ)⁻¹ by ring,
      Real.mul_rpow hpos.le (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two, inv_pow,
      Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
    norm_num
    field_simp
  unfold twoCoordinateKernel transformedPairKernel
  dsimp [w, z] at hpow hhalf
  calc
    _ ≤ ((L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) / 2) ^ (-2 : ℝ) *
        (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
    _ = 4 * ((L + ‖siteToPlane w‖ ^ 2 + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ) *
        (1 + ‖siteToPlane (v.1 - v.2)‖ ^ (2 * a)) ^ (-p)) := by rw [hhalf]; ring
    _ = _ := by rfl

end

end Critical2DKPZ.MomentBounds
