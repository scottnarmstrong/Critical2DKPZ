/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedEndpointIntegral
import Mathlib.Tactic

/-! # Positive connector forms in the continuum moment law -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- The positive endpoint form of two moment kernels joined by a connector. -/
def slabPositiveConnectorForm (θ a b : ℝ)
    (F K : Configuration 2 → Configuration 2 → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, momentKernel 2 θ a x y *
    (∫⁻ z, K y z * (∫⁻ q, momentKernel 2 θ b z q * F x q))

/-- The two-block endpoint law is the positive connector form after grouping
its external and middle coordinates. -/
theorem lintegral_slabSeparatedMomentPiMeasure_sourceForm (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (F K : Configuration 2 → Configuration 2 → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) (hK : Measurable (Function.uncurry K)) :
    (∫⁻ z, F (z 0).1 (z 1).2 * K (z 0).2 (z 1).1 ∂slabSeparatedMomentPiMeasure θ a b) =
      slabPositiveConnectorForm θ a b F K := by
  have hQ (t : ℝ) : Measurable (Function.uncurry (momentKernel 2 θ t)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, t), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ z, K (z 0).2 (z 1).1 * F (z 0).1 (z 1).2 ∂slabSeparatedMomentPiMeasure θ a b := by
      apply lintegral_congr
      intro z
      exact mul_comm _ _
    _ = ∫⁻ x, ∫⁻ y, spatialKernelComp volume (momentKernel 2 θ a)
        (spatialKernelComp volume K (momentKernel 2 θ b)) x y * F x y :=
      lintegral_slabSeparatedMomentPiMeasure_endpoint θ ha hb hK hF
    _ = _ := by
      unfold slabPositiveConnectorForm
      apply lintegral_congr
      intro x
      have hFx : Measurable (F x) := hF.comp (measurable_const.prodMk measurable_id)
      rw [spatialKernelComp_action_eq volume volume (hQ a)
        (measurable_spatialKernelComp volume hK (hQ b)) hFx x]
      apply lintegral_congr
      intro y
      exact congrArg (fun q : ℝ≥0∞ => momentKernel 2 θ a x y * q)
        (spatialKernelComp_action_eq volume volume hK (hQ b) hFx y)

end Critical2DKPZ.SHF.Flow
end
