/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.FormBounds
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
public import Critical2DKPZ.SHF.DeltaBose.TraceL2
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Tsai.Tech
import Mathlib.Tactic

/-! # One-step kernel form bounds for the head estimate

The collision and incoming kernels have unweighted `L²` form bounds with their scalar
density and heat-time coefficients explicit.
-/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The collision operator has the exact scalar-density `L²` form constant
`4π scalarDensity θ t`. This sharper coefficient is used before integrating
the collision time in the head estimate. -/
theorem formBound_collisionKernel_scalarDensity {n : ℕ} (α : CollisionPair n)
    (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    FormBound volume volume
      (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ t z z'))
      (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t)) := by
  have hK : Measurable (Function.uncurry
      (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ t z z'))) := by
    have hp : Measurable (fun p : FusedConfiguration α × FusedConfiguration α => ((θ, t), p)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  apply (formBound_iff_l2_sq_le volume volume hK
    (ENNReal.ofReal (4 * Real.pi * scalarDensity θ t))).2
  intro f hf
  simpa only [ENNReal.rpow_two] using collisionKernel_l2_sq_le α θ ht hf

/-- At exponent two, the incoming kernel has an unweighted `L²` form bound of order `t^{-1/2}`. -/
theorem weightedFormBound_incoming_L2 {n : ℕ} (α : CollisionPair n) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun _ : Configuration n => 0) 2 2
        (fun (z : FusedConfiguration α) (x : Configuration n) =>
          ENNReal.ofReal (incomingKernel α t z x))
        (ENNReal.ofReal (c * t ^ (-(1 : ℝ) / 2))) := by
  obtain ⟨c, hc, h⟩ := weightedFormBound_incoming_unweighted α
    (p := 2) (by norm_num : (1 : ℝ) < 2)
  refine ⟨c, hc, ?_⟩
  intro t ht
  simpa only [show (2 : ℝ) / (2 - 1) = 2 by norm_num,
    show -1 / (2 : ℝ) = -(1 : ℝ) / 2 by ring] using h t ht

end Critical2DKPZ.SHF.Tsai

end
