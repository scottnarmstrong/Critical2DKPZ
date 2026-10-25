/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.HeatPairFactor
public import Critical2DKPZ.SHF.Flow.HeatConvolutionENN
import Mathlib.Tactic

/-! # Integrating the two-particle entrance collision center -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped ENNReal

/-- The collision center convolution separates the incoming gap from the
center heat kernel at the full horizon. This is the spatial step in the
identification with the two-particle delta-Bose diagram. -/
theorem pairTwo_entrance_center_convolution
    {T u : ℝ} (hu : 0 < u) (huT : u < T) (a₀ a₁ b : Plane) :
    Integrable (fun z : Plane =>
      (heatKernel u (z - a₀) * heatKernel u (z - a₁)) *
        heatKernel ((T - u) / 2) (b - z)) ∧
    (∫ z : Plane, (heatKernel u (z - a₀) * heatKernel u (z - a₁)) *
        heatKernel ((T - u) / 2) (b - z)) =
      heatKernel (2 * u) (a₁ - a₀) *
        heatKernel (T / 2) (b - (1 / 2 : ℝ) • (a₀ + a₁)) := by
  let a : Plane := (1 / 2 : ℝ) • (a₀ + a₁)
  let q : ℝ := (T - u) / 2
  have hq : 0 < q := half_pos (sub_pos.mpr huT)
  have hhalf : 0 < u / 2 := half_pos hu
  have hi : Integrable (fun z : Plane => heatKernel (u / 2) (z - a) * heatKernel q (b - z)) := by
    have hmajor := ((integrable_heatKernel hhalf).comp_sub_right a).mul_const
      ((2 * Real.pi * q)⁻¹)
    apply hmajor.mono'
      ((((continuous_heatKernel (u / 2)).comp (continuous_id.sub continuous_const)).mul
        ((continuous_heatKernel q).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    apply Eventually.of_forall
    intro z
    change ‖heatKernel (u / 2) (z - a) * heatKernel q (b - z)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hhalf.le _),
      abs_of_nonneg (heatKernel_nonneg hq.le _)]
    exact mul_le_mul_of_nonneg_left (heatKernel_le_at_zero hq.le _) (heatKernel_nonneg hhalf.le _)
  have he : (∫ z : Plane, heatKernel (u / 2) (z - a) * heatKernel q (b - z)) =
      heatKernel (T / 2) (b - a) := by
    have hm : Measurable (fun z : Plane => ENNReal.ofReal (heatKernel (u / 2) (z - a)) *
        ENNReal.ofReal (heatKernel q (b - z))) := by
      exact (((measurable_heatKernel (u / 2)).comp (measurable_id.sub_const a)).ennreal_ofReal).mul
        (((measurable_heatKernel q).comp (measurable_const.sub measurable_id)).ennreal_ofReal)
    have hreal := integral_toReal (μ := (volume : Measure Plane)) hm.aemeasurable (Eventually.of_forall fun z =>
      lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
    rw [SHF.Flow.lintegral_heatKernel_initialProduct hhalf hq a b] at hreal
    rw [show u / 2 + q = T / 2 by dsimp [q]; ring] at hreal
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (heatKernel_nonneg hhalf.le _),
      ENNReal.toReal_ofReal (heatKernel_nonneg hq.le _),
      ENNReal.toReal_ofReal (heatKernel_nonneg (half_pos (hu.trans huT)).le _)] using hreal

  have hpoint (z : Plane) :
      (heatKernel u (z - a₀) * heatKernel u (z - a₁)) * heatKernel q (b - z) =
        heatKernel (2 * u) (a₁ - a₀) * (heatKernel (u / 2) (z - a) * heatKernel q (b - z)) := by
    rw [SHF.Flow.heatKernel_pair_factor hu]
    dsimp [a]
    ring
  constructor
  · change Integrable (fun z : Plane =>
      (heatKernel u (z - a₀) * heatKernel u (z - a₁)) * heatKernel q (b - z))
    simpa only [hpoint] using hi.const_mul (heatKernel (2 * u) (a₁ - a₀))
  · change (∫ z : Plane, (heatKernel u (z - a₀) * heatKernel u (z - a₁)) * heatKernel q (b - z)) = _
    simp only [hpoint, integral_const_mul, he]
    rfl

end Critical2DKPZ.SHF.Moments
