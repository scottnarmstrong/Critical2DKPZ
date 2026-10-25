/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatStartMeanFormula
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The heat semigroup expression for heat-start means -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.NonGaussian

/-- Convolving two translated heat kernels adds their time parameters. -/
theorem integral_heatKernel_shift_mul_sub {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) (x y : Plane) :
    (∫ z, heatKernel δ (z - x) * heatKernel u (y - z)) = heatKernel (δ + u) (y - x) := by
  let F : Plane → ℝ := fun z => heatKernel δ z * heatKernel u ((y - x) - z)
  calc
    _ = ∫ z, F (z - x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp [F]
        rw [show (y - x) - (z - x) = y - z by abel]
    _ = ∫ z, F z := by
      simpa only [sub_eq_add_neg] using integral_add_right_eq_self F (-x)
    _ = _ := integral_heatKernel_mul_sub hδ hu (y - x)

/-- The expected heat-start pairing against a nonnegative bounded terminal is the ordinary
heat-semigroup action at time `δ + t - s`. -/
theorem heatStart_integral_eq_semigroup (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y) :
    (∫ ω, shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω ∂P) =
      ∫ y, heatKernel (δ + (t - s)) (y - x) * g y := by
  have hMean := integrable_and_heatStart_integral_eq ϑ P Z hZ hs hst hδ x g hg
  have hProd : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2 *
      heatKernel (t - s) (p.2 - p.1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hMean.1
  rw [hMean.2, Measure.volume_eq_prod, integral_prod _ hProd, integral_integral_swap hProd]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    calc
      (∫ z, heatKernel δ (z - x) * g y * heatKernel (t - s) (y - z)) =
          g y * ∫ z, heatKernel δ (z - x) * heatKernel (t - s) (y - z) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => by ring
      _ = _ := by rw [integral_heatKernel_shift_mul_sub hδ (sub_pos.mpr hst), mul_comm]

end Critical2DKPZ.NonGaussian

end
