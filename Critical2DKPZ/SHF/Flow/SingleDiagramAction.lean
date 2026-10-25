/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.CollisionSliceAction
public import Critical2DKPZ.SHF.Flow.CollisionTimeOrdering

/-! # The explicit single-collision diagram and its inverse-logarithmic bound -/

@[expose] public noncomputable section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Integrating the single-collision diagram against a nonnegative test gives its time-integrated three-block action. -/
theorem diagramKernel_singleton_action_eq {n : ℕ} (α : CollisionPair n) (θ v : ℝ)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) (x : Configuration n) :
    (∫⁻ y : Configuration n, diagramKernel θ [α] v x y * f y) =
      collisionTimeAction α θ v f x := by
  rw [collisionTimeAction_eq_ordered α θ v hf x]
  have houter : Measurable (fun p : ℝ × Configuration n =>
      ∫⁻ u in Ioo p.1 v, collisionSlice α θ v x p.2 p.1 u) := by
    apply measurable_lintegral_Ioo measurable_fst measurable_const
    exact measurable_collisionSlice_comp α measurable_const measurable_const
      measurable_fst.fst measurable_snd measurable_const measurable_fst.snd
  have hinner (r : ℝ) : Measurable (fun p : ℝ × Configuration n =>
      collisionSlice α θ v x p.2 r p.1) :=
    measurable_collisionSlice_comp α measurable_const measurable_const
      measurable_const measurable_fst measurable_const measurable_snd
  change (∫⁻ y : Configuration n,
    (∫⁻ r in Ioo 0 v, ∫⁻ u in Ioo r v, collisionSlice α θ v x y r u) * f y) = _
  rw [lintegral_kernelMixture_action (volume.restrict (Ioo 0 v)) volume houter hf]
  apply lintegral_congr
  intro r
  rw [lintegral_kernelMixture_action (volume.restrict (Ioo r v)) volume (hinner r) hf]
  apply lintegral_congr
  intro u
  exact collisionSlice_action_eq α θ v r u hf x


end Critical2DKPZ.SHF.Flow

end
