/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadGaussian
public import Critical2DKPZ.SHF.Tsai.BlockMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Deterministic middle-block estimate -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- A heat block of duration `τ` paired with two Gaussian connectors of width `ε`
is bounded by `(2πτ)⁻¹`, uniformly over positive connector widths and endpoints. -/
theorem lintegral_heatBlock_two_connectors_le {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (a b : Plane) :
    (∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel ε (p.1 - a)) *
      ENNReal.ofReal (heatKernel ε (b - p.2)) ∂heatBlock τ) ≤
        ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) := by
  have hden : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel τ (p.2 - p.1))) :=
    ((measurable_heatKernel τ).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have hEnds : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel ε (p.1 - a)) *
      ENNReal.ofReal (heatKernel ε (b - p.2))) :=
    (((measurable_heatKernel ε).comp (measurable_fst.sub measurable_const)).ennreal_ofReal).mul
      (((measurable_heatKernel ε).comp (measurable_const.sub measurable_snd)).ennreal_ofReal)
  have hProduct : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (heatKernel ε (p.1 - a)) *
        (ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * ENNReal.ofReal (heatKernel ε (b - p.2)))) :=
    (((measurable_heatKernel ε).comp (measurable_fst.sub measurable_const)).ennreal_ofReal).mul
      (hden.mul (((measurable_heatKernel ε).comp (measurable_const.sub measurable_snd)).ennreal_ofReal))
  have hIdentity : (∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel ε (p.1 - a)) *
      ENNReal.ofReal (heatKernel ε (b - p.2)) ∂heatBlock τ) =
      ENNReal.ofReal (heatKernel (ε + τ + ε) (b - a)) := by
    unfold heatBlock
    rw [lintegral_withDensity_eq_lintegral_mul volume hden hEnds]
    calc
      _ = ∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel ε (p.1 - a)) *
          (ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * ENNReal.ofReal (heatKernel ε (b - p.2))) :=
        lintegral_congr (fun _ => by ac_rfl)
      _ = ∫⁻ z : Plane, ENNReal.ofReal (heatKernel ε (z - a)) *
          (∫⁻ z' : Plane, ENNReal.ofReal (heatKernel τ (z' - z)) *
            ENNReal.ofReal (heatKernel ε (b - z'))) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hProduct.aemeasurable]
        apply lintegral_congr
        intro z
        dsimp only
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := lintegral_heatKernel_three_shifted hε hτ hε a b
  rw [hIdentity]
  apply ENNReal.ofReal_le_ofReal
  have hWidth : 0 < ε + τ + ε := by positivity
  calc
    heatKernel (ε + τ + ε) (b - a) ≤ (2 * Real.pi * (ε + τ + ε))⁻¹ :=
      heatKernel_le_at_zero hWidth.le _
    _ ≤ (2 * Real.pi * τ)⁻¹ := by
      apply inv_anti₀ (by positivity : 0 < 2 * Real.pi * τ)
      exact mul_le_mul_of_nonneg_left (by linarith only [hε]) (by positivity)

end Critical2DKPZ.NonGaussian

end
