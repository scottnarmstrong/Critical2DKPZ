/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LatticeShells
public import Critical2DKPZ.MomentBounds.PowerComparison
import Mathlib.Tactic

/-! # Pointwise reductions for the weighted LZ21 lattice kernel -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- The positive rational-power kernel in LZ21 Lemma A.1, with Gaussian-free lattice conventions. -/
def weightedLatticeKernel (L r a p : ℝ) (z : Site) : ℝ :=
  (L + ‖siteToPlane z‖ ^ 2) ^ (-r) * (1 + ‖siteToPlane z‖ ^ (2 * a)) ^ (-p)

/-- The weighted lattice kernel is nonnegative. -/
theorem weightedLatticeKernel_nonneg {L : ℝ} (hL : 0 ≤ L) (r a p : ℝ) (z : Site) :
    0 ≤ weightedLatticeKernel L r a p z :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

/-- Embedding the lattice origin into the plane gives the planar origin. -/
theorem siteToPlane_zero : siteToPlane (0 : Site) = 0 := by
  ext i
  simp only [siteToPlane, Pi.zero_apply, Int.cast_zero, PiLp.zero_apply]

/-- The weighted lattice kernel has the stated value at the origin. -/
theorem weightedLatticeKernel_origin (L r a p : ℝ) (ha : 0 < a) :
    weightedLatticeKernel L r a p 0 = L ^ (-r) := by
  simp only [weightedLatticeKernel, siteToPlane_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero, Real.zero_rpow (by positivity : 2 * a ≠ 0),
    Real.one_rpow, mul_one]

/-- Dropping the additive one in the weight, without losing its exact exponent. -/
theorem weight_rpow_le {u a p : ℝ} (hu : 0 < u) (hp : 0 < p) :
    (1 + u ^ (2 * a)) ^ (-p) ≤ u ^ (-(2 * (a * p))) := by
  have ht : 0 < u ^ (2 * a) := Real.rpow_pos_of_pos hu _
  calc
    _ ≤ (u ^ (2 * a)) ^ (-p) := Real.rpow_le_rpow_of_nonpos ht
      (le_add_of_nonneg_left zero_le_one) (by linarith only [hp])
    _ = _ := by
      rw [← Real.rpow_mul hu.le]
      congr 1
      ring

/-- On a shell, the spatial weight is bounded by the negative shell-radius power. -/
theorem weight_le_shell {a p : ℝ} (ha : 0 < a) (hp : 0 < p)
    {z : Site} {k : ℕ} (hz : z ∈ latticeShell k) :
    (1 + ‖siteToPlane z‖ ^ (2 * a)) ^ (-p) ≤ ((k : ℝ) + 1) ^ (-(2 * (a * p))) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hnorm : (k : ℝ) + 1 ≤ ‖siteToPlane z‖ := by
    have hh := norm_sq_ge_of_mem_latticeShell hz
    push_cast at hh
    nlinarith only [hh, norm_nonneg (siteToPlane z), hk]
  exact (weight_rpow_le (hk.trans_le hnorm) hp).trans
    (Real.rpow_le_rpow_of_nonpos hk hnorm
      (neg_nonpos.mpr (mul_nonneg (by norm_num) (mul_nonneg ha.le hp.le))))

/-- Peel every exponent beyond the endpoint r=1 before summing the spatial kernel. -/
theorem weightedLatticeKernel_le_scaled_one {L r : ℝ} (hL : 0 < L) (hr : 1 ≤ r)
    (a p : ℝ) (z : Site) :
    weightedLatticeKernel L r a p z ≤ L ^ (1 - r) * weightedLatticeKernel L 1 a p z := by
  have hD : 0 < L + ‖siteToPlane z‖ ^ 2 := by positivity
  have he : (L + ‖siteToPlane z‖ ^ 2) ^ (-r) =
      (L + ‖siteToPlane z‖ ^ 2) ^ (1 - r) * (L + ‖siteToPlane z‖ ^ 2) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hD]
    congr 1
    ring
  unfold weightedLatticeKernel
  rw [he, mul_assoc]
  apply mul_le_mul_of_nonneg_right
  · exact Real.rpow_le_rpow_of_nonpos hL (le_add_of_nonneg_right (sq_nonneg _))
      (by linarith only [hr])
  · exact mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (by positivity) _)

end Critical2DKPZ.MomentBounds
