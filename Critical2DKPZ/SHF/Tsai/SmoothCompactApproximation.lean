/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-! # Smooth compact approximations with a common support

A fixed smooth cutoff equals one on the original compact support. Multiplying
uniform smooth approximations by this cutoff preserves the uniform error and
puts every approximating support inside a single compact set.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Topology ContDiff CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- A compact continuous test admits uniform smooth approximations in one common compact window. -/
theorem exists_smoothCompactTest_uniform_approx {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : C_c(E, ℝ)) :
    ∃ K : Set E, IsCompact K ∧ ∀ ε : ℝ, 0 < ε → ∃ g : C_c(E, ℝ),
      ContDiff ℝ ∞ g ∧ tsupport (g : E → ℝ) ⊆ K ∧ ∀ x, |g x - f x| < ε := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall (0 : E)
  let φ : ContDiffBump (0 : E) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  have hφone (x) (hx : x ∈ tsupport (f : E → ℝ)) : φ x = 1 := by
    apply φ.one_of_mem_closedBall
    exact Metric.closedBall_subset_closedBall
      (show R ≤ |R| + 1 by linarith [le_abs_self R]) (hR hx)
  have hφf (x) : φ x * f x = f x := by
    by_cases hx : x ∈ tsupport (f : E → ℝ)
    · rw [hφone x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  refine ⟨tsupport (φ : E → ℝ), φ.hasCompactSupport, fun ε hε => ?_⟩
  obtain ⟨h, hhc, hh⟩ := (CompactlySupportedContinuousMapClass.uniformContinuous f).exists_contDiff_dist_le hε
  let g : C_c(E, ℝ) := ⟨⟨fun x => φ x * h x, φ.continuous.mul hhc.continuous⟩,
    φ.hasCompactSupport.mul_right⟩
  refine ⟨g, φ.contDiff.mul hhc, tsupport_mul_subset_left, fun x => ?_⟩
  have hident : g x - f x = φ x * (h x - f x) := by
    change φ x * h x - f x = _
    rw [mul_sub, hφf]
  rw [hident, abs_mul]
  have hφabs : |φ x| ≤ 1 := by rw [abs_of_nonneg φ.nonneg]; exact φ.le_one
  calc
    |φ x| * |h x - f x| ≤ 1 * |h x - f x| :=
      mul_le_mul_of_nonneg_right hφabs (abs_nonneg _)
    _ < ε := by simpa only [one_mul, Real.dist_eq] using hh x

end Critical2DKPZ.SHF.Tsai

end
