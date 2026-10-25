/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HardyLittlewood
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Planar dilations and centered averages -/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Scaling a planar Lebesgue integral contributes the inverse square Jacobian. -/
theorem lintegral_comp_smul_plane (f : Plane → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z, f (r • z)) = (ENNReal.ofReal (r ^ 2))⁻¹ * ∫⁻ z, f z := by
  let e : Plane ≃ᵐ Plane := (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv
  change (∫⁻ z, f (e z)) = _
  rw [← lintegral_map_equiv f e]
  change (∫⁻ z, f z ∂Measure.map (fun z : Plane => r • z) volume) = _
  rw [volume.map_addHaar_smul hr.ne', lintegral_smul_measure]
  simp only [Plane, finrank_euclideanSpace, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)), ENNReal.ofReal_inv_of_pos (sq_pos_of_pos hr), smul_eq_mul]

/-- The same scaling identity after translating the center. -/
theorem lintegral_comp_add_smul_plane (f : Plane → ℝ≥0∞) (y : Plane)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z, f (y + r • z)) = (ENNReal.ofReal (r ^ 2))⁻¹ * ∫⁻ z, f z := by
  rw [lintegral_comp_smul_plane (fun z => f (y + z)) hr, lintegral_add_left_eq_self]

/-- A centered dilation maps the reference ball to the corresponding spatial ball. -/
theorem add_smul_mem_ball_iff (y z : Plane) {r : ℝ} (hr : 0 < r) (K : ℝ) :
    y + r • z ∈ ball y (r * K) ↔ z ∈ ball (0 : Plane) K := by
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, sub_zero]
  exact mul_lt_mul_iff_of_pos_left hr

/-- The restricted inverse-square change of variables. -/
theorem setLIntegral_norm_add_smul (g : Plane → ℝ) (y : Plane)
    {r : ℝ} (hr : 0 < r) (K : ℝ) :
    (∫⁻ z in ball (0 : Plane) K, ‖g (y + r • z)‖ₑ) =
      (ENNReal.ofReal (r ^ 2))⁻¹ * ∫⁻ z in ball y (r * K), ‖g z‖ₑ := by
  let F := (ball y (r * K)).indicator (fun z => ‖g z‖ₑ)
  have he : (fun z => (ball (0 : Plane) K).indicator (fun z => ‖g (y + r • z)‖ₑ) z) =
      fun z => F (y + r • z) := by
    funext z
    by_cases hz : z ∈ ball (0 : Plane) K
    · rw [indicator_of_mem hz]
      exact (indicator_of_mem ((add_smul_mem_ball_iff y z hr K).mpr hz) (fun z => ‖g z‖ₑ)).symm
    · rw [indicator_of_notMem hz]
      exact (indicator_of_notMem (fun h => hz ((add_smul_mem_ball_iff y z hr K).mp h)) (fun z => ‖g z‖ₑ)).symm
  rw [← lintegral_indicator measurableSet_ball, he, lintegral_comp_add_smul_plane F y hr]
  rw [lintegral_indicator measurableSet_ball]

/-- Integrating over a reference ball is its volume times the corresponding
centered average. -/
theorem setLIntegral_norm_add_smul_eq_average (g : Plane → ℝ) (y : Plane)
    {r K : ℝ} (hr : 0 < r) (hK : 0 < K) :
    (∫⁻ z in ball (0 : Plane) K, ‖g (y + r • z)‖ₑ) =
      volume (ball (0 : Plane) K) * ballAverage g y (r * K) := by
  have hv : volume (ball y (r * K)) = ENNReal.ofReal (r ^ 2) * volume (ball (0 : Plane) K) := by
    rw [volume.addHaar_ball_mul_of_pos y hr K]
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hr0 : ENNReal.ofReal (r ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)).ne'
  have hB0 : volume (ball (0 : Plane) K) ≠ 0 := (measure_ball_pos volume 0 hK).ne'
  rw [setLIntegral_norm_add_smul g y hr K]
  dsimp [ballAverage]
  rw [hv, ENNReal.mul_inv (Or.inl hr0) (Or.inl ENNReal.ofReal_ne_top)]
  calc
    (ENNReal.ofReal (r ^ 2))⁻¹ * (∫⁻ z in ball y (r * K), ‖g z‖ₑ) =
        (volume (ball (0 : Plane) K) * (volume (ball (0 : Plane) K))⁻¹) *
          ((ENNReal.ofReal (r ^ 2))⁻¹ * ∫⁻ z in ball y (r * K), ‖g z‖ₑ) := by
      rw [ENNReal.mul_inv_cancel hB0 measure_ball_lt_top.ne, one_mul]
    _ = volume (ball (0 : Plane) K) *
        ((ENNReal.ofReal (r ^ 2))⁻¹ * (volume (ball (0 : Plane) K))⁻¹ *
          ∫⁻ z in ball y (r * K), ‖g z‖ₑ) := by ac_rfl

end Critical2DKPZ.Extensions.ScaleLimit

end
