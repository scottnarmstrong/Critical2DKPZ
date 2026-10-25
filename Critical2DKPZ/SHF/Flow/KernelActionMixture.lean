/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2

/-! # Positive kernel actions commute with positive mixtures -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Tonelli moves a nonnegative test through a measurable mixture of kernels. -/
theorem lintegral_kernelMixture_action {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure A) (ν : Measure X)
    [SFinite μ] [SFinite ν] {K : A → X → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ a, K a x ∂μ) * f x ∂ν) = ∫⁻ a, ∫⁻ x, K a x * f x ∂ν ∂μ := by
  have hm : Measurable (fun p : X × A => K p.2 p.1 * f p.1) :=
    (hK.comp (measurable_snd.prodMk measurable_fst)).mul (hf.comp measurable_fst)
  calc
    _ = ∫⁻ x, ∫⁻ a, K a x * f x ∂μ ∂ν := by
      apply lintegral_congr
      intro x
      exact (lintegral_mul_const _
        (hK.comp (measurable_id.prodMk measurable_const))).symm
    _ = _ := lintegral_lintegral_swap hm.aemeasurable

end Critical2DKPZ.SHF.Flow

end
