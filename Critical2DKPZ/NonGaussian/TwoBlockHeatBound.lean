/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatBlockMarginals
public import Critical2DKPZ.SHF.Tsai.Products
import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The unit-mass bound for a heat-averaged two-block chain -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Averaging the final heat block of a Gaussian-smoothed product gives at most its initial mass
when the final test is bounded by one, including infinite initial mass. -/
theorem lintegral_smoothedProduct_heatBlock_le
    (μ : Measure (Plane × Plane)) [SigmaFinite μ]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (hg1 : ∀ y, g y ≤ 1)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫⁻ p, f p.1 * g p.2 ∂smoothedProductMeasure μ (heatKernel ε) (heatBlock τ)) ≤
      ∫⁻ p, f p.1 ∂μ := by
  have hF : Measurable (fun p : Plane × Plane => f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have hJ : Measurable (fun o : (Plane × Plane) × (Plane × Plane) =>
      ENNReal.ofReal (heatKernel ε (o.1.2 - o.2.1)) * (f o.1.1 * g o.2.2)) :=
    (((measurable_heatKernel ε).comp (measurable_fst.snd.sub measurable_snd.fst)).ennreal_ofReal).mul
      ((hf.comp measurable_fst.fst).mul (hg.comp measurable_snd.snd))
  let : IsLocallyFiniteMeasure (heatBlock τ) := locallyFinite_heatBlock τ
  rw [lintegral_smoothedProductMeasure μ (heatKernel ε) (heatBlock τ) (measurable_heatKernel ε)
    (fun p => f p.1 * g p.2) hF, lintegral_prod _ hJ.aemeasurable]
  apply lintegral_mono
  intro p
  dsimp only
  calc
    _ ≤ ∫⁻ q : Plane × Plane, f p.1 * ENNReal.ofReal (heatKernel ε (q.1 - p.2)) ∂heatBlock τ := by
      apply lintegral_mono
      intro q
      dsimp only
      have hsymm : heatKernel ε (p.2 - q.1) = heatKernel ε (q.1 - p.2) := by
        rw [show p.2 - q.1 = -(q.1 - p.2) by abel, heatKernel_neg]
      rw [hsymm]
      calc
        _ ≤ ENNReal.ofReal (heatKernel ε (q.1 - p.2)) * (f p.1 * 1) := by
          gcongr
          exact hg1 q.2
        _ = _ := by rw [mul_one, mul_comm]
    _ = f p.1 := by
      have hHeat : Measurable (fun q : Plane × Plane => ENNReal.ofReal (heatKernel ε (q.1 - p.2))) :=
        ((measurable_heatKernel ε).comp (measurable_fst.sub measurable_const)).ennreal_ofReal
      rw [lintegral_const_mul _ hHeat,
        lintegral_heatBlock_gaussian_fst_eq_one hτ hε p.2, mul_one]

end Critical2DKPZ.NonGaussian

end
