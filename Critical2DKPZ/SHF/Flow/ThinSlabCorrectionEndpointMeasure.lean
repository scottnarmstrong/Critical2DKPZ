/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabUniformCorrectionForm
public import Critical2DKPZ.SHF.Flow.ThinSlabFreeEndpointMeasure
import all Critical2DKPZ.SHF.Flow.ThinSlabFreeEndpointMeasure

/-! # The collision-correction measure in the first thin-slab comparison -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The endpoint measure of the singleton-collision middle term. -/
def slabCorrectionEndpointMeasure (θ a v b : ℝ) :
    Measure (Configuration 2 × Configuration 2) :=
  (volume.prod volume).withDensity
    (Function.uncurry (slabTwoParticleCorrectionMiddleComp θ a v b))

private theorem measurable_slabCorrectionEndpointKernel (θ a v b : ℝ) :
    Measurable (Function.uncurry (slabTwoParticleCorrectionMiddleComp θ a v b)) := by
  have hC : Measurable (Function.uncurry (twoParticleCorrection θ v)) :=
    measurable_diagramKernel_comp [pairTwo] measurable_const measurable_const measurable_fst measurable_snd
  exact measurable_spatialKernelComp volume (measurable_slabMomentKernelTwo θ a)
    (measurable_spatialKernelComp volume hC (measurable_slabMomentKernelTwo θ b))

/-- The two-particle semigroup decomposition is an equality of endpoint measures. -/
theorem slabMomentKernelEndpointMeasure_eq_free_add_correction (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) :
    slabMomentKernelEndpointMeasure θ (a + v + b) =
      slabSeparatedFreeEndpointMeasure θ a v b + slabCorrectionEndpointMeasure θ a v b := by
  rw [slabSeparatedFreeEndpointMeasure_eq θ ha hb v]
  unfold slabMomentKernelEndpointMeasure slabCorrectionEndpointMeasure
  rw [← withDensity_add_left (measurable_slabFreeEndpointKernel θ a v b)]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun p => slabMomentKernelTwo_threeTime_split θ ha hv hb p.1 p.2

/-- The correction measure is dominated by the full moment measure. -/
theorem slabCorrectionEndpointMeasure_le_full (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) :
    slabCorrectionEndpointMeasure θ a v b ≤ slabMomentKernelEndpointMeasure θ (a + v + b) := by
  rw [slabMomentKernelEndpointMeasure_eq_free_add_correction θ ha hv hb]
  exact Measure.le_add_left le_rfl

/-- Compact endpoint tests are integrable against both summands of the semigroup decomposition. -/
theorem integrable_slabEndpointMeasures (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) (F : C_c(Configuration 2 × Configuration 2, ℝ)) :
    Integrable (F : Configuration 2 × Configuration 2 → ℝ)
      (slabMomentKernelEndpointMeasure θ (a + v + b)) ∧
    Integrable (F : Configuration 2 × Configuration 2 → ℝ)
      (slabSeparatedFreeEndpointMeasure θ a v b) ∧
    Integrable (F : Configuration 2 × Configuration 2 → ℝ)
      (slabCorrectionEndpointMeasure θ a v b) := by
  have hfull : Integrable (F : Configuration 2 × Configuration 2 → ℝ)
      (slabMomentKernelEndpointMeasure θ (a + v + b)) :=
    integrable_compactTest_of_locallyFinite _
      (locallyFinite_momentKernelMeasure 2 θ (add_pos (add_pos ha hv) hb)) F
  exact ⟨hfull, hfull.mono_measure (slabSeparatedFreeEndpointMeasure_le_full θ ha hv hb),
    hfull.mono_measure (slabCorrectionEndpointMeasure_le_full θ ha hv hb)⟩

/-- The continuum difference of second-moment endpoint forms is exactly the correction
integral. Integrability is supplied by `integrable_slabEndpointMeasures`. -/
theorem integral_slabEndpointCorrection_eq_sub (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) (F : C_c(Configuration 2 × Configuration 2, ℝ)) :
    (∫ q, F q ∂slabMomentKernelEndpointMeasure θ (a + v + b)) -
      (∫ q, F q ∂slabSeparatedFreeEndpointMeasure θ a v b) =
        ∫ q, F q ∂slabCorrectionEndpointMeasure θ a v b := by
  have hI := integrable_slabEndpointMeasures θ ha hv hb F
  rw [slabMomentKernelEndpointMeasure_eq_free_add_correction θ ha hv hb,
    integral_add_measure hI.2.1 hI.2.2]
  exact add_sub_cancel_left _ _

/-- Positive endpoint factors integrate against the correction measure as the zero-weight
collision-correction action used by the logarithmic estimate. -/
theorem lintegral_slabCorrectionEndpointMeasure_mul (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ)
    {f g : Configuration 2 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ q, g q.1 * f q.2 ∂slabCorrectionEndpointMeasure θ a v b) =
      slabMomentKernelTwoCorrectionEndpointForm θ a v b f g := by
  have hKa := measurable_slabMomentKernelTwo θ a
  have hKb := measurable_slabMomentKernelTwo θ b
  have hC : Measurable (Function.uncurry (twoParticleCorrection θ v)) :=
    measurable_diagramKernel_comp [pairTwo] measurable_const measurable_const measurable_fst measurable_snd
  have hComp := measurable_slabCorrectionEndpointKernel θ a v b
  rw [slabCorrectionEndpointMeasure, ← Measure.volume_eq_prod,
    lintegral_kernelMeasure_mul hComp hg hf]
  apply lintegral_congr
  intro x
  have hrow : Measurable (fun y => slabTwoParticleCorrectionMiddleComp θ a v b x y * f y) :=
    (hComp.comp (measurable_const.prodMk measurable_id)).mul hf
  have hconst := lintegral_const_mul (μ := volume) (g x) hrow
  simp only [← mul_assoc] at hconst
  rw [hconst]
  apply congrArg (fun q : ℝ≥0∞ => g x * q)
  change (∫⁻ y, spatialKernelComp volume (momentKernel 2 θ a)
      (spatialKernelComp volume (twoParticleCorrection θ v) (momentKernel 2 θ b)) x y * f y) = _
  rw [spatialKernelComp_action_eq volume volume hKa
    (measurable_spatialKernelComp volume hC hKb) hf x]
  calc
    _ = ∫⁻ z, momentKernel 2 θ a x z * (∫⁻ w, twoParticleCorrection θ v z w *
        (∫⁻ y, momentKernel 2 θ b w y * f y)) := by
      apply lintegral_congr
      intro z
      exact congrArg (fun q : ℝ≥0∞ => momentKernel 2 θ a x z * q)
        (spatialKernelComp_action_eq volume volume hC hKb hf z)
    _ = _ := slabMomentKernelTwo_correction_action_eq θ a v b ha.ne' hb.ne' f x

end Critical2DKPZ.SHF.Flow

end
