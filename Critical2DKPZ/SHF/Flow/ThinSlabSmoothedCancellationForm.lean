/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabMollifierBounds
import Mathlib.Tactic

/-! # Uniform bilinear control of the smoothed thin-slab correction -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- The smoothed correction form has one inverse-logarithmic constant uniform
in the mollifier scale and all time parameters in a fixed bounded window. -/
theorem exists_slabSmoothed_cancellation_bilinear_bound (B a T : ℝ) (ha : 0 ≤ a)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (θ r t v e : ℝ), θ ≤ B →
      0 ≤ r → r ≤ T → 0 ≤ t → t ≤ T → 0 < v → v ≤ 1 / 2 → 0 < e → e ≤ 1 →
      ∀ f g : Configuration 2 → ℝ≥0∞, Measurable f → Measurable g →
      (∫⁻ x : Configuration 2, twoParticleWeightedAction θ a r
        (slabMollifierWeightedAction a e w
          (twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f))) x * g x) ≤
        D * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_slabSmoothed_weighted_cancellation_bound B a T ha w hw hwc
  refine ⟨C ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC, ?_⟩
  intro θ r t v e hθ hr hrT ht htT hv hvhalf he he1 f g hf hg
  let A : Configuration 2 → ℝ≥0∞ := fun x =>
    twoParticleWeightedAction θ a r
      (slabMollifierWeightedAction a e w
        (twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f))) x
  have hA : Measurable A := by
    dsimp [A]
    exact measurable_twoParticleWeightedAction θ a r
      (measurable_slabMollifierWeightedAction a e hw
        (measurable_twoParticleCorrectionWeightedAction θ a v
          (measurable_twoParticleWeightedAction θ a t hf)))
  have hsq := hbound θ r t v e hθ hr hrT ht htT hv hvhalf he he1 f hf
  have hroot :
      (∫⁻ x : Configuration 2, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        C ^ (1 / 2 : ℝ) * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) ^ 2 *
          ∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        apply ENNReal.monotone_rpow_of_nonneg (by norm_num)
        simpa only [ENNReal.rpow_two] using hsq
      _ = C ^ (1 / 2 : ℝ) * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [← ENNReal.rpow_natCast_mul]
        norm_num
  have hHolder :
      (∫⁻ x : Configuration 2, A x * g x) ≤
        (∫⁻ x : Configuration 2, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      hA.aemeasurable hg.aemeasurable
  have hbound' :
      (∫⁻ x : Configuration 2, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        C ^ (1 / 2 : ℝ) * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hroot (by positivity)
  exact hHolder.trans (by simpa only [ENNReal.rpow_two] using hbound')


end Critical2DKPZ.SHF.Flow
end
