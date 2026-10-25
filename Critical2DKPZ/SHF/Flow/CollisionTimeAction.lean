/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.EndpointCollisionAction
public import Critical2DKPZ.SHF.Flow.ScalarCollisionMass

/-! # Integrating the collision duration

The single-collision action is integrated over the collision duration and the two endpoint times. -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The single-collision action integrated over its duration and both endpoint times. -/
def collisionTimeAction {n : ℕ} (α : CollisionPair n) (θ v : ℝ)
    (f : Configuration n → ℝ≥0∞) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ s in Ioo 0 v, endpointCollisionAction α θ s (v - s) f x




end Critical2DKPZ.SHF.Flow

end
