/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleWeightedBound

/-! # Weighted two-particle actions including time zero -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The weighted two-particle action, with the identity at time zero. -/
def twoParticleWeightedAction (θ a t : ℝ) (f : Configuration 2 → ℝ≥0∞)
    (x : Configuration 2) : ℝ≥0∞ :=
  if t = 0 then f x else ∫⁻ y : Configuration 2,
    expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
      (momentKernel 2 θ t) x y * f y

/-- The weighted correction is the action of the explicit one-collision kernel. -/
def twoParticleCorrectionWeightedAction (θ a v : ℝ) (f : Configuration 2 → ℝ≥0∞)
    (x : Configuration 2) : ℝ≥0∞ :=
  ∫⁻ y : Configuration 2,
    expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
      (twoParticleCorrection θ v) x y * f y

/-- The weighted two-particle moment kernel sends measurable functions to measurable functions. -/
theorem measurable_twoParticleWeightedAction (θ a t : ℝ)
    {f : Configuration 2 → ℝ≥0∞} (hf : Measurable f) :
    Measurable (twoParticleWeightedAction θ a t f) := by
  change Measurable (fun x => if t = 0 then f x else ∫⁻ y : Configuration 2,
    expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
      (momentKernel 2 θ t) x y * f y)
  by_cases ht : t = 0
  · simpa only [ite_eq_left ht] using hf
  · simp only [ite_eq_right ht]
    apply measurable_kernelAction volume _ hf
    apply measurable_expConjugate
    · exact measurable_const.mul (measurable_configurationOneNorm 2)
    · exact measurable_const.mul (measurable_configurationOneNorm 2)
    · have hp : Measurable (fun p : Configuration 2 × Configuration 2 => ((θ, t), p)) :=
        measurable_const.prodMk measurable_id
      exact Measurable.comp
        (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
          momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
        (f := fun p : Configuration 2 × Configuration 2 => ((θ, t), p))
        (measurable_momentKernel 2) hp

/-- The weighted two-particle correction kernel sends measurable functions to measurable functions. -/
theorem measurable_twoParticleCorrectionWeightedAction (θ a v : ℝ)
    {f : Configuration 2 → ℝ≥0∞} (hf : Measurable f) :
    Measurable (twoParticleCorrectionWeightedAction θ a v f) := by
  apply measurable_kernelAction volume _ hf
  apply measurable_expConjugate
  · exact measurable_const.mul (measurable_configurationOneNorm 2)
  · exact measurable_const.mul (measurable_configurationOneNorm 2)
  · exact measurable_diagramKernel_comp [pairTwo] measurable_const measurable_const measurable_fst measurable_snd

/-- Uniform boundedness includes the identity at zero, without interpreting it as a density. -/
theorem exists_twoParticleWeightedAction_l2_bound (B a T : ℝ) (ha : 0 ≤ a) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (θ t : ℝ), θ ≤ B → 0 ≤ t → t ≤ T →
      ∀ f : Configuration 2 → ℝ≥0∞, Measurable f →
      (∫⁻ x : Configuration 2, twoParticleWeightedAction θ a t f x ^ 2) ≤
        D * ∫⁻ y : Configuration 2, f y ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_momentKernel_two_weighted_l2_bound B a T ha
  refine ⟨1 + D, ENNReal.add_ne_top.mpr ⟨by norm_num, hD⟩,
    fun θ t hθ ht htT f hf => ?_⟩
  by_cases ht0 : t = 0
  · simp only [twoParticleWeightedAction, ht0, ite_eq_left]
    simpa only [one_mul] using mul_le_mul' (le_self_add : (1 : ℝ≥0∞) ≤ 1 + D)
      (le_refl (∫⁻ y : Configuration 2, f y ^ 2))
  · simp only [twoParticleWeightedAction, ht0]
    exact (hbound θ t hθ (lt_of_le_of_ne ht (Ne.symm ht0)) htT f hf).trans
      (mul_le_mul' le_add_self le_rfl)

end Critical2DKPZ.SHF.Flow

end
