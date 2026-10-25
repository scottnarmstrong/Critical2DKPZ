/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PlanarDilation
public import Critical2DKPZ.Definitions.TestFn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-! # Smooth averages are dominated by the centered maximal function -/

public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A test function admits a positive support radius and a positive uniform bound. -/
theorem exists_testFn_envelope (φ : TestFn) : ∃ K M : ℝ,
    0 < K ∧ 0 < M ∧ tsupport (φ : Plane → ℝ) ⊆ ball (0 : Plane) K ∧
      ∀ z : Plane, ‖φ z‖ ≤ M := by
  obtain ⟨K, hK, hs⟩ := φ.hasCompactSupport.isBounded.subset_ball_lt 0 (0 : Plane)
  have hc := φ.hasCompactSupport.isCompact_range φ.continuous
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  refine ⟨K, max 1 M, hK, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hs, fun z => ?_⟩
  exact (hM _ (mem_range_self z)).trans (le_max_right _ _)


/-- Deterministic domination with a chosen support ball and uniform bound. -/
theorem maximal_domination_of_bound (φ : TestFn) {K M : ℝ} (hK : 0 < K) (hM : 0 ≤ M)
    (hs : tsupport (φ : Plane → ℝ) ⊆ ball (0 : Plane) K)
    (hb : ∀ z : Plane, ‖φ z‖ ≤ M) (g : Plane → ℝ) (y : Plane)
    {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal |∫ z, φ z * g (y + r • z)| ≤
      ENNReal.ofReal (M * (volume (ball (0 : Plane) K)).toReal) * maximalFn g y := by
  have hpoint (z : Plane) : ‖φ z * g (y + r • z)‖ₑ ≤ ENNReal.ofReal M *
      (ball (0 : Plane) K).indicator (fun z => ‖g (y + r • z)‖ₑ) z := by
    by_cases hz : z ∈ ball (0 : Plane) K
    · rw [indicator_of_mem hz, enorm_mul]
      apply mul_le_mul' _ le_rfl
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb z)
    · have hzero : φ z = 0 := by
        by_contra hne
        exact hz (hs (subset_closure (show z ∈ Function.support (φ : Plane → ℝ) from hne)))
      rw [hzero, zero_mul, enorm_zero, indicator_of_notMem hz, mul_zero]
  rw [← Real.norm_eq_abs, ofReal_norm]
  calc
    ‖∫ z, φ z * g (y + r • z)‖ₑ ≤ ∫⁻ z, ‖φ z * g (y + r • z)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z, ENNReal.ofReal M *
        (ball (0 : Plane) K).indicator (fun z => ‖g (y + r • z)‖ₑ) z := lintegral_mono hpoint
    _ = ENNReal.ofReal M * ∫⁻ z in ball (0 : Plane) K, ‖g (y + r • z)‖ₑ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball]
    _ = (ENNReal.ofReal M * volume (ball (0 : Plane) K)) * ballAverage g y (r * K) := by
      rw [setLIntegral_norm_add_smul_eq_average g y hr hK, mul_assoc]
    _ ≤ (ENNReal.ofReal M * volume (ball (0 : Plane) K)) * maximalFn g y :=
      mul_le_mul' le_rfl (le_iSup_of_le ⟨r * K, mul_pos hr hK⟩ le_rfl)
    _ = ENNReal.ofReal (M * (volume (ball (0 : Plane) K)).toReal) * maximalFn g y := by
      rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_toReal measure_ball_lt_top.ne]

/-- Smooth averaging at every center and scale is dominated by the maximal
function, with a positive constant depending only on the test function.
For locally integrable inputs, `integrable_smooth_average` supplies integrability. -/
theorem maximal_domination (φ : TestFn) : ∃ A : ℝ, 0 < A ∧
    ∀ (g : Plane → ℝ) (y : Plane) (r : ℝ), 0 < r →
      ENNReal.ofReal |∫ z, φ z * g (y + r • z)| ≤ ENNReal.ofReal A * maximalFn g y := by
  obtain ⟨K, M, hK, hM, hs, hb⟩ := exists_testFn_envelope φ
  refine ⟨M * (volume (ball (0 : Plane) K)).toReal, ?_, fun g y r hr => ?_⟩
  · exact mul_pos hM (ENNReal.toReal_pos (measure_ball_pos volume 0 hK).ne' measure_ball_lt_top.ne)
  · exact maximal_domination_of_bound φ hK hM.le hs hb g y hr

end Critical2DKPZ.Extensions.ScaleLimit

end
