/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.CollisionTimeAction
public import Critical2DKPZ.SHF.Flow.TimeTriangle

/-! # Ordered collision times and positive collision durations -/

@[expose] public noncomputable section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Reorder the collision action from duration coordinates to ordered absolute times. -/
theorem collisionTimeAction_eq_ordered {n : ℕ} (α : CollisionPair n) (θ v : ℝ)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) (x : Configuration n) :
    collisionTimeAction α θ v f x =
      ∫⁻ r in Ioo 0 v, ∫⁻ u in Ioo r v,
        singleCollisionAction α θ r (u - r) (v - u) f x := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      singleCollisionAction α θ p.1 p.2 (v - p.1 - p.2) f x) :=
    measurable_singleCollisionAction_comp α measurable_const measurable_fst measurable_snd
      ((measurable_const.sub measurable_fst).sub measurable_snd) measurable_const hf
  unfold collisionTimeAction endpointCollisionAction
  have he : (∫⁻ s in Ioo 0 v, ∫⁻ r in Ioo 0 (v - s),
      singleCollisionAction α θ r s (v - s - r) f x) =
      ∫⁻ s in Ioo 0 v, ∫⁻ r in Ioo 0 (v - s),
        singleCollisionAction α θ r s (v - r - s) f x := by
    apply lintegral_congr
    intro s
    apply lintegral_congr
    intro r
    congr 1
    ring
  rw [he]
  rw [← lintegral_timeTriangle_swap v hm]
  apply lintegral_congr
  intro r
  have h := lintegral_Ioo_sub_right r v
    (fun s => singleCollisionAction α θ r s (v - r - s) f x)
  simpa only [sub_sub_sub_cancel_right] using h

end Critical2DKPZ.SHF.Flow

end
