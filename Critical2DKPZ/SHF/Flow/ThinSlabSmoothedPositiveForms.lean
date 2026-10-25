/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSignedConnectorForm
public import Critical2DKPZ.SHF.Flow.ThinSlabTensorConnector
public import Critical2DKPZ.SHF.Flow.ThinSlabPositiveFormSplit
import Mathlib.Tactic

/-! # The explicit smoothed thin-slab positive-form identity -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- The full smoothed moment form equals its heat-smoothed slab form plus
its explicit one-collision correction form. -/
theorem slabSmoothedPositiveForm_eq_heat_add_correction {θ r v b e : ℝ}
    (hSG : MomentKernelTwoSemigroup θ) (hv : 0 < v) (hb : 0 < b) (he : 0 < e)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (F : Configuration 2 → Configuration 2 → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) :
    slabPositiveConnectorForm θ r (v + b) F (slabMollifierTensorKernel 2 e w) =
      slabPositiveConnectorForm θ r b F (slabConnectorTensorKernel (slabSmoothedHeatConnector v e w)) +
      slabPositiveConnectorForm θ r b F
        (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v)) := by
  have hW : Measurable (Function.uncurry (slabMollifierTensorKernel 2 e w)) := by
    apply measurable_connectorKernel
    intro i
    apply Continuous.measurable
    fun_prop
  have h := slabPositiveConnectorForm_free_add_correction_of (r := r) hSG hv hb F
    (slabMollifierTensorKernel 2 e w) hF hW
  have hTensor : slabConnectorTensorKernel (slabSmoothedHeatConnector v e w) =
      spatialKernelComp volume (slabMollifierTensorKernel 2 e w)
        (fun x y => ENNReal.ofReal (freeKernel 2 v x y)) := by
    funext x y
    exact slabSmoothedHeatTensor_eq_spatialKernelComp hv he w hw hwc hw0 x y
  rw [← hTensor] at h
  exact h

/-- For finite signed source parts, subtraction of the heat-smoothed form
leaves exactly the signed one-collision correction. -/
theorem slabSignedSmoothedForm_sub_eq_correction {θ r v b e : ℝ}
    (hSG : MomentKernelTwoSemigroup θ) (hv : 0 < v) (hb : 0 < b) (he : 0 < e)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (F G : Configuration 2 → Configuration 2 → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hFi : slabPositiveConnectorForm θ r (v + b) F (slabMollifierTensorKernel 2 e w) ≠ ⊤)
    (hGi : slabPositiveConnectorForm θ r (v + b) G (slabMollifierTensorKernel 2 e w) ≠ ⊤) :
    ((slabPositiveConnectorForm θ r (v + b) F (slabMollifierTensorKernel 2 e w)).toReal -
      (slabPositiveConnectorForm θ r (v + b) G (slabMollifierTensorKernel 2 e w)).toReal) -
    ((slabPositiveConnectorForm θ r b F (slabConnectorTensorKernel (slabSmoothedHeatConnector v e w))).toReal -
      (slabPositiveConnectorForm θ r b G (slabConnectorTensorKernel (slabSmoothedHeatConnector v e w))).toReal) =
    (slabPositiveConnectorForm θ r b F
      (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v))).toReal -
    (slabPositiveConnectorForm θ r b G
      (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v))).toReal := by
  have hSplitF := slabSmoothedPositiveForm_eq_heat_add_correction (r := r) hSG hv hb he w hw hwc hw0 F hF
  have hSplitG := slabSmoothedPositiveForm_eq_heat_add_correction (r := r) hSG hv hb he w hw hwc hw0 G hG
  have hFFinite := hFi
  have hGFinite := hGi
  rw [hSplitF] at hFFinite
  rw [hSplitG] at hGFinite
  have hFparts := ENNReal.add_ne_top.mp hFFinite
  have hGparts := ENNReal.add_ne_top.mp hGFinite
  rw [hSplitF, hSplitG, ENNReal.toReal_add hFparts.1 hFparts.2,
    ENNReal.toReal_add hGparts.1 hGparts.2]
  ring

end Critical2DKPZ.SHF.Flow
end
