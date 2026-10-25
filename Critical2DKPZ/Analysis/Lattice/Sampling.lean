/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Positivity

/-! Sampling each lattice cell at its representative gives a measurable map that converges pointwise to the identity as the mesh tends to zero. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Critical2DKPZ

/-- The continuum location of the lattice site at diffusive scale `N`. -/
def latticeRepresentative (N : ℕ) (z : Site) : Plane :=
  (Real.sqrt (N / 2))⁻¹ • siteToPlane z

/-- Each point is mapped to the representative of its nearest-even-lattice cell. -/
def cellSample (N : ℕ) (x : Plane) : Plane := latticeRepresentative N (latticePoint N x)

/-- Sampling the representative of a lattice cell is measurable. -/
theorem measurable_cellSample (N : ℕ) : Measurable (cellSample N) :=
  (measurable_of_countable (latticeRepresentative N)).comp (measurable_latticePoint N)

/-- Cell sampling is constant on each cell and equals its representative. -/
theorem cellSample_eq_of_mem_cell {N : ℕ} {z : Site} {x : Plane} (hx : x ∈ cell N z) :
    cellSample N x = latticeRepresentative N z := by
  rw [cellSample, (mem_cell_iff N z x).mp hx]

/-- Cell sampling at zero scale is the zero point. -/
@[simp] theorem cellSample_zero (x : Plane) : cellSample 0 x = 0 := by
  simp only [cellSample, latticeRepresentative, Nat.cast_zero, zero_div, Real.sqrt_zero,
    inv_zero, zero_smul]

/-- The distance from a point to its sampled cell representative is bounded by the mesh size. -/
theorem dist_cellSample_le {N : ℕ} (hN : 0 < N) (x : Plane) :
    dist (cellSample N x) x ≤ (Real.sqrt (N / 2))⁻¹ := by
  rw [dist_comm, dist_eq_norm]
  exact norm_sub_latticePoint_le hN x

/-- A uniform coarse bound, useful for domination on compact supports. -/
theorem dist_cellSample_le_two {N : ℕ} (hN : 0 < N) (x : Plane) :
    dist (cellSample N x) x ≤ 2 := by
  have hscale : 0 < Real.sqrt (N / 2) := Real.sqrt_pos.mpr (by positivity)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt (N / 2) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith only [hN'])
  apply (dist_cellSample_le hN x).trans
  rw [inv_le_iff_one_le_mul₀ hscale]
  linarith only [hhalf]

/-- The mesh radius tends to zero at positive integer scales. -/
theorem tendsto_lattice_mesh :
    Tendsto (fun N : ℕ => (Real.sqrt (N / 2))⁻¹) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ) / 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).atTop_div_const
      (by norm_num)
  exact (Real.tendsto_sqrt_atTop.comp hn).inv_tendsto_atTop

/-- Sampling converges pointwise to the identity. -/
theorem tendsto_cellSample (x : Plane) : Tendsto (fun N : ℕ => cellSample N x) atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [tendsto_lattice_mesh.eventually (gt_mem_nhds hε),
    eventually_gt_atTop 0] with N hmesh hN
  exact (dist_cellSample_le hN x).trans_lt hmesh

/-- Sampling stays in one fixed ball above any bounded set, at every scale including zero. -/
theorem norm_cellSample_le {R : ℝ} (hR : 0 ≤ R) {x : Plane} (hx : ‖x‖ ≤ R) (N : ℕ) :
    ‖cellSample N x‖ ≤ R + 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [cellSample_zero, norm_zero]
    linarith only [hR]
  · calc
      ‖cellSample N x‖ ≤ ‖cellSample N x - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
      _ ≤ 2 + R := add_le_add (dist_cellSample_le_two hN x) hx
      _ = R + 2 := add_comm _ _

end Critical2DKPZ

end
