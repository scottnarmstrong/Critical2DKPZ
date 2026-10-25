/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LongWordLimitCellIntegral
public import Critical2DKPZ.SHF.Moments.SinglePairWordUniform
public import Critical2DKPZ.SHF.Moments.WordDominationPairWordProfiles
public import Critical2DKPZ.SHF.Moments.LongWordLimitCellBounds
import Mathlib.Tactic

/-! # Uniform approximation of normalized compact cell tests -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The normalized cell test converges uniformly over its terminal site,
when its initial cell is sampled at a fixed continuum point. -/
theorem eventually_normalized_cellTestWeight_close (φ : C_c(Plane × Plane, ℝ))
    (x : Plane) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ y : Site, y ∈ evenLattice →
      |(N / 4 : ℝ) * cellTestWeight N φ (latticePoint N x) y -
        φ (x, latticeRepresentative N y)| ≤ ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactlySupportedContinuousMapClass.uniformContinuous φ) (ε / 2) (half_pos hε)
  filter_upwards [eventually_cellTestWeight_close_to_frozen_sample φ (half_pos hε),
    (tendsto_cellSample x).eventually (Metric.ball_mem_nhds x hδ),
    eventually_gt_atTop 0] with N hcell hsample hN
  intro y hy
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc := hcell (latticePoint N x) y (latticePoint_mem_evenLattice N x) hy
  have hc' : |(N / 4 : ℝ) * cellTestWeight N φ (latticePoint N x) y -
      φ (cellSample N x, latticeRepresentative N y)| ≤ ε / 2 := by
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ (N / 4 : ℝ) by positivity)
    rw [← abs_of_nonneg (show 0 ≤ (N / 4 : ℝ) by positivity), ← abs_mul] at hh
    simp only [abs_of_nonneg (show 0 ≤ (N / 4 : ℝ) by positivity)] at hh
    convert hh using 1 <;> (try dsimp only [cellSample]) <;> field_simp
  have hp : dist (cellSample N x, latticeRepresentative N y)
      (x, latticeRepresentative N y) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hsample
  have hm := (hmod hp).le
  rw [Real.dist_eq] at hm
  calc
    _ ≤ |(N / 4 : ℝ) * cellTestWeight N φ (latticePoint N x) y -
          φ (cellSample N x, latticeRepresentative N y)| +
        |φ (cellSample N x, latticeRepresentative N y) -
          φ (x, latticeRepresentative N y)| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hc' hm
    _ = ε := add_halves ε

/-- The whole finite product of normalized cell tests converges uniformly
in accessible terminal configurations. -/
theorem eventually_prod_normalized_cellTestWeight_close {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) (x : Configuration h)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ y : Fin h → Site, (∀ i, y i ∈ evenLattice) →
      |(∏ i, (N / 4 : ℝ) * cellTestWeight N (φ i) (latticePoint N (x i)) (y i)) -
        ∏ i, φ i (x i, latticeRepresentative N (y i))| ≤ ε := by
  obtain ⟨M, _R, hM, _hR, hφ, _hφR⟩ := exists_collisionWord_compactTest_bounds φ
  have hprod : Continuous (fun v : Fin h → ℝ => ∏ i, v i) := by fun_prop
  have huc := (isCompact_closedBall (0 : Fin h → ℝ) M).uniformContinuousOn_of_continuous
    hprod.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ i : Fin h, ∀ y : Site, y ∈ evenLattice →
      |(N / 4 : ℝ) * cellTestWeight N (φ i) (latticePoint N (x i)) y -
        φ i (x i, latticeRepresentative N y)| ≤ δ / 2 := by
    rw [Filter.eventually_all]
    intro i
    exact eventually_normalized_cellTestWeight_close (φ i) (x i) (half_pos hδ)
  filter_upwards [hclose, eventually_gt_atTop 0] with N hcloseN hN
  intro y hy
  let a : Fin h → ℝ := fun i => (N / 4 : ℝ) *
    cellTestWeight N (φ i) (latticePoint N (x i)) (y i)
  let b : Fin h → ℝ := fun i => φ i (x i, latticeRepresentative N (y i))
  have ha (i : Fin h) : |a i| ≤ M :=
    abs_normalized_cellTestWeight_le hN (φ i) M hM (hφ i) _ _
  have hb (i : Fin h) : |b i| ≤ M := hφ i _
  have ham : a ∈ Metric.closedBall 0 M := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hM).mpr (fun i => by simpa only [Real.norm_eq_abs] using ha i)
  have hbm : b ∈ Metric.closedBall 0 M := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hM).mpr (fun i => by simpa only [Real.norm_eq_abs] using hb i)
  have hab : dist a b < δ := by
    have hh : ‖a - b‖ ≤ δ / 2 := (pi_norm_le_iff_of_nonneg (half_pos hδ).le).mpr
      (fun i => by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcloseN i (y i) (hy i))
    rw [dist_eq_norm]
    exact hh.trans_lt (half_lt_self hδ)
  exact (show dist (∏ i, a i) (∏ i, b i) < ε from hmod a ham b hbm hab).le

end Critical2DKPZ.SHF.Moments
