/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabPositiveFormTensor
public import Critical2DKPZ.SHF.Flow.ThinSlabUnweightedActions
public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedCancellationForm
import Mathlib.Tactic

/-! # Uniform inverse-log bounds on positive smoothed correction forms -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- A separated endpoint majorant bounds the correction form by the explicit
zero-weight bilinear action controlled by the uniform mollifier estimate. -/
theorem slabPositiveCorrectionForm_le_bilinear (θ r b v e : ℝ)
    (hr : 0 < r) (hb : 0 < b) (w : Plane → ℝ) (hw : Continuous w)
    (f g : Configuration 2 → ℝ≥0∞) (hf : Measurable f)
    (F : Configuration 2 → Configuration 2 → ℝ≥0∞)
    (hF : ∀ x z, F x z ≤ g x * f z) :
    slabPositiveConnectorForm θ r b F
      (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v)) ≤
      ∫⁻ x, twoParticleWeightedAction θ 0 r
        (slabMollifierWeightedAction 0 e w
          (twoParticleCorrectionWeightedAction θ 0 v (twoParticleWeightedAction θ 0 b f))) x * g x := by
  have hW : Measurable (Function.uncurry (slabMollifierTensorKernel 2 e w)) := by
    apply measurable_connectorKernel
    intro i
    apply Continuous.measurable
    fun_prop
  have hC : Measurable (Function.uncurry (twoParticleCorrection θ v)) :=
    (measurable_diagramKernel [pairTwo]).comp
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, v), p))
      (measurable_const.prodMk measurable_id)
  have hWC := measurable_spatialKernelComp volume hW hC
  have hMono : slabPositiveConnectorForm θ r b F
      (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v)) ≤
      slabPositiveConnectorForm θ r b (fun x z => g x * f z)
        (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v)) := by
    apply lintegral_mono
    intro x
    apply lintegral_mono
    intro y
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro z
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro q
    exact mul_le_mul' le_rfl (hF x q)
  apply hMono.trans
  rw [slabPositiveConnectorForm_tensor_source θ r b _ hWC f g hf]
  apply le_of_eq
  have hQB : Measurable (Function.uncurry (momentKernel 2 θ b)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, b), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  have hB : Measurable (fun z => ∫⁻ q, momentKernel 2 θ b z q * f q) :=
    measurable_kernelAction volume hQB hf
  have hAction (y : Configuration 2) := spatialKernelComp_action_eq volume volume hW hC hB y
  simp only [twoParticleWeightedAction_zeroWeight (θ := θ) hr,
    twoParticleWeightedAction_zeroWeight (θ := θ) hb,
    slabMollifierWeightedAction_zero_weight, twoParticleCorrectionWeightedAction_zeroWeight]
  simp_rw [hAction]

/-- The correction form has one inverse-logarithmic bound uniform over the
mollifier scale and the positive time parameters in a fixed bounded window. -/
theorem exists_slabPositiveCorrectionForm_bound (B T : ℝ)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (θ r b v e : ℝ), θ ≤ B →
      0 < r → r ≤ T → 0 < b → b ≤ T → 0 < v → v ≤ 1 / 2 → 0 < e → e ≤ 1 →
      ∀ f g : Configuration 2 → ℝ≥0∞, Measurable f → Measurable g →
      ∀ F : Configuration 2 → Configuration 2 → ℝ≥0∞, (∀ x z, F x z ≤ g x * f z) →
      slabPositiveConnectorForm θ r b F
        (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v)) ≤
        D * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨D, hD, hBound⟩ := exists_slabSmoothed_cancellation_bilinear_bound B 0 T le_rfl w hw hwc
  refine ⟨D, hD, ?_⟩
  intro θ r b v e hθ hr hrT hb hbT hv hvhalf he he1 f g hf hg F hF
  exact (slabPositiveCorrectionForm_le_bilinear θ r b v e hr hb w hw f g hf F hF).trans
    (hBound θ r b v e hθ hr.le hrT hb.le hbT hv hvhalf he he1 f g hf hg)


end Critical2DKPZ.SHF.Flow
end
