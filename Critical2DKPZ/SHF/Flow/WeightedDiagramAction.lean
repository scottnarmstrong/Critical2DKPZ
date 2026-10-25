/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedCollisionTimeAction
public import Critical2DKPZ.SHF.Flow.SingleDiagramAction
public import Critical2DKPZ.SHF.Flow.KernelConjugationAction

/-! # Inverse-logarithmic decay of the explicit weighted collision diagram -/

@[expose] public noncomputable section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The weighted spatial action is the conjugate of the original three-block action. -/
theorem weightedCollisionSliceAction_eq {n : ℕ} (α : CollisionPair n) (θ a r s q : ℝ)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) (x : Configuration n) :
    weightedCollisionSliceAction α θ a r s q f x =
      ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) *
        singleCollisionAction α θ r s q
          (fun y => ENNReal.ofReal (Real.exp (-(a * configurationOneNorm y))) * f y) x := by
  have hfw : Measurable (fun y : Configuration n =>
      ENNReal.ofReal (Real.exp (-(a * configurationOneNorm y))) * f y) :=
    ((measurable_const.mul (measurable_configurationOneNorm n)).neg.exp.ennreal_ofReal).mul hf
  unfold weightedCollisionSliceAction
  rw [expConjugate_action_eq]
  congr 1
  simp_rw [oneCollisionSpatialSlice_eq_collisionSlice]
  have h := collisionSlice_action_eq α θ (r + s + q) r (r + s) hfw x
  simpa only [show r + s - r = s by ring, show r + s + q - (r + s) = q by ring] using h

/-- The same conjugation identity holds after both positive time integrations. -/
theorem weightedCollisionTimeAction_eq {n : ℕ} (α : CollisionPair n) (θ a v : ℝ)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) (x : Configuration n) :
    weightedCollisionTimeAction α θ a v f x =
      ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) *
        collisionTimeAction α θ v
          (fun y => ENNReal.ofReal (Real.exp (-(a * configurationOneNorm y))) * f y) x := by
  unfold weightedCollisionTimeAction weightedEndpointCollisionAction collisionTimeAction endpointCollisionAction
  simp_rw [weightedCollisionSliceAction_eq α θ a _ _ _ hf x]
  have he (s : ℝ) :
      (∫⁻ r in Ioo 0 (v - s), ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) *
        singleCollisionAction α θ r s (v - s - r)
          (fun y => ENNReal.ofReal (Real.exp (-(a * configurationOneNorm y))) * f y) x) =
      ENNReal.ofReal (Real.exp (a * configurationOneNorm x)) *
        ∫⁻ r in Ioo 0 (v - s), singleCollisionAction α θ r s (v - s - r)
          (fun y => ENNReal.ofReal (Real.exp (-(a * configurationOneNorm y))) * f y) x :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [he]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The conjugated diagram acts by the weighted duration-integrated action. -/
theorem diagramKernel_singleton_weighted_action_eq {n : ℕ} (α : CollisionPair n) (θ a v : ℝ)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) (x : Configuration n) :
    (∫⁻ y : Configuration n,
      expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
        (diagramKernel θ [α] v) x y * f y) = weightedCollisionTimeAction α θ a v f x := by
  have hfw : Measurable (fun y : Configuration n =>
      ENNReal.ofReal (Real.exp (-(a * configurationOneNorm y))) * f y) :=
    ((measurable_const.mul (measurable_configurationOneNorm n)).neg.exp.ennreal_ofReal).mul hf
  rw [expConjugate_action_eq, diagramKernel_singleton_action_eq α θ v hfw,
    weightedCollisionTimeAction_eq α θ a v hf x]

/-- Uniform logarithmic decay for the explicit diagram on the weighted space. -/
theorem exists_diagramKernel_singleton_weighted_l2_log_bound (n : ℕ) (B a T : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (α : CollisionPair n) (θ v : ℝ),
      θ ≤ B → 0 < v → v ≤ 1 / 2 → v ≤ T → ∀ f : Configuration n → ℝ≥0∞, Measurable f →
      (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
        expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
          (diagramKernel θ [α] v) x y * f y) ^ 2) ≤
        (C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 * ∫⁻ y : Configuration n, f y ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_weightedCollisionTimeAction_l2_log_bound n B a T ha
  refine ⟨C, hC, fun α θ v hθ hv hvhalf hvT f hf => ?_⟩
  simp_rw [diagramKernel_singleton_weighted_action_eq α θ a v hf]
  exact hbound α θ v hθ hv hvhalf hvT f hf

end Critical2DKPZ.SHF.Flow

end
