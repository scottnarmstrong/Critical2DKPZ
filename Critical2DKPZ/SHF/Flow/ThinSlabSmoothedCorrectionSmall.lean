/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabPositiveCorrectionBound
public import Critical2DKPZ.SHF.Flow.ThinSlabUniformCorrectionForm
import Mathlib.Tactic

/-! # Uniform smallness of the mollifier-inserted thin-slab correction -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.DeltaBose
open scoped ENNReal Topology
namespace Critical2DKPZ.SHF.Flow

/-- Finite quadratic endpoint norms make the correction form small as the slab shrinks, uniformly over positive mollifier scales at most one and bounded outer durations. -/
theorem slabPositiveCorrectionForm_uniformly_small (B T : ℝ)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    {f g : Configuration 2 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hf2 : (∫⁻ x, f x ^ 2) ≠ ⊤) (hg2 : (∫⁻ x, g x ^ 2) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ v₀ > 0, ∀ θ r b v e : ℝ, θ ≤ B →
      0 < r → r ≤ T → 0 < b → b ≤ T → 0 < v → v < v₀ → 0 < e → e ≤ 1 →
      ∀ F : Configuration 2 → Configuration 2 → ℝ≥0∞, (∀ x z, F x z ≤ g x * f z) →
      slabPositiveConnectorForm θ r b F
        (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v)) ≤
        ENNReal.ofReal ε := by
  obtain ⟨C, hC, hbound⟩ := exists_slabPositiveCorrectionForm_bound B T w hw hwc
  let A : ℝ≥0∞ := (∫⁻ x, f x ^ 2) ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := (∫⁻ x, g x ^ 2) ^ (1 / 2 : ℝ)
  have hA : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf2
  have hD : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hg2
  have hlog : Tendsto (fun v : ℝ => ENNReal.ofReal (1 / (1 + Real.log v⁻¹)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp tendsto_slab_inverseLog_nhdsGT_zero
  have hlimit : Tendsto (fun v : ℝ => C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) * A * D)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hlog (Or.inr hC))
          (Or.inr hA)) (Or.inr hD)
  intro ε hε
  have hsmall := hlimit.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨v₁, hv₁, hinterval⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  refine ⟨min v₁ (1 / 2), lt_min hv₁ (by norm_num), ?_⟩
  intro θ r b v e hθ hr hrT hb hbT hv hv₀ he he1 F hF
  have hv₁' : v < v₁ := hv₀.trans_le (min_le_left _ _)
  have hvhalf : v ≤ 1 / 2 := hv₀.le.trans (min_le_right _ _)
  exact (hbound θ r b v e hθ hr hrT hb hbT hv hvhalf he he1 f g hf hg F hF).trans
    (hinterval ⟨hv, hv₁'⟩).le

end Critical2DKPZ.SHF.Flow
end
