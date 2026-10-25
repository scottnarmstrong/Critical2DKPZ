/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Critical2DKPZ.SHF.Moments.TimeRounding
import Mathlib.Tactic

/-! # The exponential weight at the exact cell-representative scale -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The weight scale is the lattice representative's spatial scaling factor. -/
def fourthWeightScale (N : ℕ) : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹

/-- The cell weight scale is nonnegative at every lattice scale. -/
theorem fourthWeightScale_nonneg (N : ℕ) : 0 ≤ fourthWeightScale N :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- The cell weight scale is strictly positive away from the zero lattice scale. -/
theorem fourthWeightScale_pos {N : ℕ} (hN : 0 < N) : 0 < fourthWeightScale N :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

/-- Its square is exactly two divided by the lattice scale. -/
theorem fourthWeightScale_sq {N : ℕ} (hN : 0 < N) : fourthWeightScale N ^ 2 = 2 / (N : ℝ) := by
  unfold fourthWeightScale
  rw [inv_pow, Real.sq_sqrt (by positivity), inv_div]

/-- The weight lies in the domain of the collision-vector bound above scale two. -/
theorem fourthWeightScale_le_one {N : ℕ} (hN : 2 ≤ N) : fourthWeightScale N ≤ 1 := by
  unfold fourthWeightScale
  rw [inv_le_one₀ (Real.sqrt_pos.mpr (by positivity : 0 < (N : ℝ) / 2))]
  apply Real.one_le_sqrt.mpr
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- The squared weight times a moving macroscopic horizon has a finite limit. -/
theorem tendsto_fourthWeightScale_sq_mul {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => fourthWeightScale N ^ 2 * m N) atTop (𝓝 (2 * c)) := by
  apply (hm.const_mul 2).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [fourthWeightScale_sq hN]
  ring

/-- The exponential weight of every sampled point in a fixed bounded set is
bounded independently of N. -/
theorem fourthWeightScale_norm_latticePoint_le {R : ℝ} (hR : 0 ≤ R)
    {x : Plane} (hx : ‖x‖ ≤ R) (N : ℕ) :
    fourthWeightScale N * ‖siteToPlane (latticePoint N x)‖ ≤ R + 2 := by
  have he : fourthWeightScale N * ‖siteToPlane (latticePoint N x)‖ = ‖cellSample N x‖ := by
    rw [cellSample, latticeRepresentative, norm_smul, Real.norm_eq_abs]
    change fourthWeightScale N * ‖siteToPlane (latticePoint N x)‖ =
      |fourthWeightScale N| * ‖siteToPlane (latticePoint N x)‖
    rw [abs_of_nonneg (fourthWeightScale_nonneg N)]
  rw [he]
  exact norm_cellSample_le hR hx N

end Critical2DKPZ.Extensions.GffTangent
