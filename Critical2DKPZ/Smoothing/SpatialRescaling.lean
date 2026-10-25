/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Volume
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Exact diffusive rescaling of the cells -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ.Smoothing

/-- Planar change of variables at diffusive scale, valid for every integrand. -/
theorem integral_plane_sqrt_scale {a : ℝ} (ha : 0 < a) (f : Plane → ℝ) :
    (∫ x, f x) = a * ∫ y, f (Real.sqrt a • y) := by
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have h := Measure.integral_comp_smul_of_nonneg volume f (Real.sqrt a)
    (hR := Real.sqrt_nonneg a)
  simp only [hd, Real.sq_sqrt ha.le, smul_eq_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- Changing the continuum scale preserves the exact nearest-even representative. -/
theorem latticePoint_rescale {N M : ℕ} (hN : 0 < N) (y : Plane) :
    latticePoint N (Real.sqrt ((M : ℝ) / N) • y) = latticePoint M y := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : Real.sqrt ((N : ℝ) / 2) * Real.sqrt ((M : ℝ) / N) = Real.sqrt ((M : ℝ) / 2) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ N / 2)]
    congr 1
    field_simp
  simp only [latticePoint, smul_smul, he]

/-- Cell averaging commutes with the exact diffusive coordinate change. -/
theorem cellAverage_rescale {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (u : Plane → ℝ) (z : Site) :
    cellAverage N u z = cellAverage M (fun y => u (Real.sqrt ((M : ℝ) / N) • y)) z := by
  by_cases hz : z ∈ evenLattice
  · have ha : 0 < (M : ℝ) / N := by positivity
    have hi : (fun y : Plane => (cell N z).indicator u (Real.sqrt ((M : ℝ) / N) • y)) =
        (cell M z).indicator (fun y => u (Real.sqrt ((M : ℝ) / N) • y)) := by
      funext y
      have hm : (Real.sqrt ((M : ℝ) / N) • y) ∈ cell N z ↔ y ∈ cell M z := by
        simp only [cell, mem_preimage, mem_singleton_iff, latticePoint_rescale hN]
      by_cases hy : y ∈ cell M z
      · rw [indicator_of_mem (hm.mpr hy), indicator_of_mem hy]
      · rw [indicator_of_notMem (fun h => hy (hm.mp h)), indicator_of_notMem hy]
    have hs := integral_plane_sqrt_scale ha ((cell N z).indicator u)
    rw [hi, integral_indicator (measurableSet_cell M z),
      integral_indicator (measurableSet_cell N z)] at hs
    rw [cellAverage, cellAverage, volume_cell_toReal hN hz, volume_cell_toReal hM hz, hs]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  · simp only [cellAverage, cell_eq_empty_of_not_even hz, measure_empty,
      ENNReal.toReal_zero, inv_zero, zero_mul]

end Critical2DKPZ.Smoothing

end
