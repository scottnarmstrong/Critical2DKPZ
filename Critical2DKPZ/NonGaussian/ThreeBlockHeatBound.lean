/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ConditionalHeatBound
import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
import Mathlib.Tactic

/-! # The sharp averaged three-block bound -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- A nonnegative three-block pairing averaged over a middle heat block of duration `τ`
is bounded by `(2πτ)⁻¹` times the product of the two outer masses, including infinite outer masses. -/
theorem lintegral_threeBlock_heat_le
    (μ ν : Measure (Plane × Plane)) [SigmaFinite μ] [SigmaFinite ν]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫⁻ q : Plane × Plane, ∫⁻ o : (Plane × Plane) × (Plane × Plane),
      (f o.1.1 * g o.2.2) *
        (ENNReal.ofReal (heatKernel ε (q.1 - o.1.2)) *
          ENNReal.ofReal (heatKernel ε (o.2.1 - q.2))) ∂μ.prod ν ∂heatBlock τ) ≤
      ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) *
        (∫⁻ p, f p.1 ∂μ) * (∫⁻ p, g p.2 ∂ν) := by
  let J (q : Plane × Plane) (o : (Plane × Plane) × (Plane × Plane)) :=
    (f o.1.1 * g o.2.2) *
      (ENNReal.ofReal (heatKernel ε (q.1 - o.1.2)) *
        ENNReal.ofReal (heatKernel ε (o.2.1 - q.2)))
  have hJ : Measurable (Function.uncurry J) :=
    ((hf.comp measurable_snd.fst.fst).mul (hg.comp measurable_snd.snd.snd)).mul
      ((((measurable_heatKernel ε).comp (measurable_fst.fst.sub measurable_snd.fst.snd)).ennreal_ofReal).mul
        (((measurable_heatKernel ε).comp (measurable_snd.snd.fst.sub measurable_fst.snd)).ennreal_ofReal))
  have hConnector (o : (Plane × Plane) × (Plane × Plane)) : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (heatKernel ε (q.1 - o.1.2)) *
        ENNReal.ofReal (heatKernel ε (o.2.1 - q.2))) :=
    (((measurable_heatKernel ε).comp (measurable_fst.sub measurable_const)).ennreal_ofReal).mul
      (((measurable_heatKernel ε).comp (measurable_const.sub measurable_snd)).ennreal_ofReal)
  let : IsLocallyFiniteMeasure (heatBlock τ) := locallyFinite_heatBlock τ
  calc
    _ = ∫⁻ o, ∫⁻ q, J q o ∂heatBlock τ ∂μ.prod ν :=
      lintegral_lintegral_swap hJ.aemeasurable
    _ ≤ ∫⁻ o : (Plane × Plane) × (Plane × Plane),
        (f o.1.1 * g o.2.2) * ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) ∂μ.prod ν := by
      apply lintegral_mono
      intro o
      dsimp only [J]
      rw [lintegral_const_mul _ (hConnector o)]
      gcongr
      exact lintegral_heatBlock_two_connectors_le hτ hε o.1.2 o.2.1
    _ = ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) *
        (∫⁻ p, f p.1 ∂μ) * (∫⁻ p, g p.2 ∂ν) := by
      have hfg : Measurable (fun o : (Plane × Plane) × (Plane × Plane) => f o.1.1 * g o.2.2) :=
        (hf.comp measurable_fst.fst).mul (hg.comp measurable_snd.snd)
      rw [lintegral_mul_const _ hfg,
        lintegral_prod_mul (f := fun p : Plane × Plane => f p.1)
          (g := fun p : Plane × Plane => g p.2)
          (hf.comp measurable_fst).aemeasurable (hg.comp measurable_snd).aemeasurable]
      ac_rfl

end Critical2DKPZ.NonGaussian

end
