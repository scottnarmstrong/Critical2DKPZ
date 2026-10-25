/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms
import Mathlib.MeasureTheory.Integral.Prod

/-! # Positive and real forms of bounded configuration kernels

The finite form bound supplies absolute integrability and almost-everywhere
finiteness of the literal kernel. Nonnegative `L²` data therefore permit
conversion between the extended positive form and the actual real form.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Positive `L²` forms equal the positive real integral; absolute integrability is supplied by
`configurationKernel_real_form_bound`. -/
theorem lintegral_configurationKernel_ofReal {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (F G : Configuration n → ℝ) (hF : MemLp F 2) (hG : MemLp G 2)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ y, 0 ≤ G y) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F x) * K x y * ENNReal.ofReal (G y)) =
      ENNReal.ofReal (∫ x, ∫ y, F x * (K x y).toReal * G y) := by
  have hI := (configurationKernel_real_form_bound hK hc hKF F G hF hG).1
  rw [← integral_prod _ hI, ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun xy => mul_nonneg
      (mul_nonneg (hF0 _) ENNReal.toReal_nonneg) (hG0 _))]
  have hPos : AEMeasurable (fun xy : Configuration n × Configuration n =>
      ENNReal.ofReal (F xy.1) * K xy.1 xy.2 * ENNReal.ofReal (G xy.2)) (volume.prod volume) :=
    (hF.aestronglyMeasurable.aemeasurable.ennreal_ofReal.comp_fst.mul hK.aemeasurable).mul
      hG.aestronglyMeasurable.aemeasurable.ennreal_ofReal.comp_snd
  rw [← lintegral_prod _ hPos]
  apply lintegral_congr_ae
  filter_upwards [configurationKernel_ne_top_of_formBound hK hc hKF] with xy hxy
  rw [ENNReal.ofReal_mul (mul_nonneg (hF0 _) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (hF0 _), ENNReal.ofReal_toReal hxy]

end Critical2DKPZ.SHF.Tsai

end
