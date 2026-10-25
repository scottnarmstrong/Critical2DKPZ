/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Tonelli forms of the planar heat convolution identities -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Tonelli's nonnegative form of the planar heat semigroup identity. -/
theorem lintegral_heatKernel_mul_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Plane) :
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel s y) *
      ENNReal.ofReal (heatKernel t (x - y))) = ENNReal.ofReal (heatKernel (s + t) x) := by
  have hInt : Integrable (fun y : Plane => heatKernel s y * heatKernel t (x - y)) := by
    apply (integrable_heatKernel hs).mul_bdd
      ((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    filter_upwards [] with y
    change ‖heatKernel t (x - y)‖ ≤ (2 * Real.pi * t)⁻¹
    rw [Real.norm_eq_abs, abs_of_pos (heatKernel_pos ht _)]
    exact heatKernel_le_at_zero ht.le _
  have hnonneg : ∀ y : Plane, 0 ≤ heatKernel s y * heatKernel t (x - y) := by
    intro y
    exact mul_nonneg (heatKernel_nonneg hs.le _) (heatKernel_nonneg ht.le _)
  calc
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel s y) *
        ENNReal.ofReal (heatKernel t (x - y))) =
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel s y * heatKernel t (x - y)) := by
          apply lintegral_congr
          intro y
          rw [← ENNReal.ofReal_mul (heatKernel_nonneg hs.le y)]
    _ = ENNReal.ofReal (∫ y : Plane, heatKernel s y * heatKernel t (x - y)) :=
          (ofReal_integral_eq_lintegral_ofReal hInt
            (Filter.Eventually.of_forall hnonneg)).symm
    _ = ENNReal.ofReal (heatKernel (s + t) x) := by
          rw [integral_heatKernel_mul_sub hs ht x]

/-- The translated initial-terminal heat convolution, in Tonelli form. -/
theorem lintegral_heatKernel_initialProduct {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : Plane) :
    (∫⁻ z : Plane, ENNReal.ofReal (heatKernel s (z - x)) *
      ENNReal.ofReal (heatKernel t (y - z))) =
        ENNReal.ofReal (heatKernel (s + t) (y - x)) := by
  let F : Plane → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (heatKernel s z * heatKernel t ((y - x) - z))
  have hF : Measurable F := by
    dsimp [F]
    exact (((measurable_heatKernel s).mul
      ((measurable_heatKernel t).comp (measurable_const.sub measurable_id))).ennreal_ofReal)
  have hmp : MeasurePreserving (fun z : Plane => z - x) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-x)
  calc
    (∫⁻ z : Plane, ENNReal.ofReal (heatKernel s (z - x)) *
        ENNReal.ofReal (heatKernel t (y - z))) = ∫⁻ z : Plane, F (z - x) := by
          apply lintegral_congr
          intro z
          dsimp [F]
          rw [← ENNReal.ofReal_mul (heatKernel_nonneg hs.le _)]
          rw [show y - z = (y - x) - (z - x) by abel]
    _ = ∫⁻ z : Plane, F z := hmp.lintegral_comp hF
    _ = ENNReal.ofReal (heatKernel (s + t) (y - x)) := by
          calc
            ∫⁻ z : Plane, F z =
                ∫⁻ z : Plane, ENNReal.ofReal (heatKernel s z) *
                  ENNReal.ofReal (heatKernel t ((y - x) - z)) := by
                    apply lintegral_congr
                    intro z
                    dsimp [F]
                    rw [← ENNReal.ofReal_mul (heatKernel_nonneg hs.le _)]
            _ = ENNReal.ofReal (heatKernel (s + t) (y - x)) :=
                  lintegral_heatKernel_mul_sub hs ht (y - x)

end Critical2DKPZ.SHF.Flow

end
