/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
public import Critical2DKPZ.SHF.DeltaBose.TraceL2

/-! # The three-block action of a single collision

The incoming, repeated-collision, and outgoing operators compose into an action on nonnegative functions. Nonnegative integration defines this action before its finiteness is established. -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- One incoming/collision/outgoing slice acting on a nonnegative function. -/
def singleCollisionAction {n : ℕ} (α : CollisionPair n) (θ r s q : ℝ)
    (f : Configuration n → ℝ≥0∞) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ z : FusedConfiguration α, ENNReal.ofReal (incomingKernel α r z x) *
    ∫⁻ z' : FusedConfiguration α, ENNReal.ofReal (collisionKernel α θ s z z') *
      ∫⁻ y : Configuration n, ENNReal.ofReal (incomingKernel α q z' y) * f y


end Critical2DKPZ.SHF.Flow

end
