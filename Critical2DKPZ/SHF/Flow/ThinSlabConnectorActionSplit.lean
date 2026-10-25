/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSemigroupAction
import Mathlib.Tactic

/-! # The semigroup correction after an arbitrary measurable connector -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- Inserting a measurable connector preserves the free-plus-correction
splitting of a positive two-particle action. -/
theorem connector_momentKernel_two_action_split_of {θ v b : ℝ}
    (hSG : MomentKernelTwoSemigroup θ) (hv : 0 < v) (hb : 0 < b)
    (K : Configuration 2 → Configuration 2 → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) {f : Configuration 2 → ℝ≥0∞}
    (hf : Measurable f) (a : Configuration 2) :
    (∫⁻ y, K a y * (∫⁻ z, momentKernel 2 θ (v + b) y z * f z)) =
      (∫⁻ y, K a y * (∫⁻ z, ENNReal.ofReal (freeKernel 2 v y z) *
        (∫⁻ q, momentKernel 2 θ b z q * f q))) +
      ∫⁻ y, K a y * (∫⁻ z, twoParticleCorrection θ v y z *
        (∫⁻ q, momentKernel 2 θ b z q * f q)) := by
  have hQB : Measurable (Function.uncurry (momentKernel 2 θ b)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, b), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  have hP : Measurable (fun p : Configuration 2 × Configuration 2 => ENNReal.ofReal (freeKernel 2 v p.1 p.2)) :=
    ((measurable_freeKernel 2).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hB := measurable_kernelAction volume hQB hf
  have hPB := measurable_kernelAction volume
    (K := fun x y => ENNReal.ofReal (freeKernel 2 v x y)) hP hB
  have hSplit := momentKernel_two_action_free_add_correction_of hSG hv hb hf
  calc
    _ = ∫⁻ y, K a y *
        ((∫⁻ z, ENNReal.ofReal (freeKernel 2 v y z) * (∫⁻ q, momentKernel 2 θ b z q * f q)) +
          ∫⁻ z, twoParticleCorrection θ v y z * (∫⁻ q, momentKernel 2 θ b z q * f q)) := by
      apply lintegral_congr_ae
      filter_upwards [hSplit] with y hy
      rw [hy]
    _ = ∫⁻ y,
        K a y * (∫⁻ z, ENNReal.ofReal (freeKernel 2 v y z) * (∫⁻ q, momentKernel 2 θ b z q * f q)) +
          K a y * (∫⁻ z, twoParticleCorrection θ v y z * (∫⁻ q, momentKernel 2 θ b z q * f q)) := by
      apply lintegral_congr
      intro y
      exact mul_add _ _ _
    _ = _ := lintegral_add_left ((hK.comp (measurable_const.prodMk measurable_id)).mul hPB) _

end Critical2DKPZ.SHF.Flow
end
