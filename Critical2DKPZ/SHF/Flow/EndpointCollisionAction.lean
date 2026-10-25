/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SingleCollisionCoefficient
public import Critical2DKPZ.SHF.Flow.SingleCollisionMeasurability
public import Critical2DKPZ.SHF.Flow.KernelMixture
public import Critical2DKPZ.SHF.Flow.EndpointBeta

/-! # Integrating the two endpoint times of a collision -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Integrate the two positive endpoint times while holding collision duration fixed. -/
def endpointCollisionAction {n : ℕ} (α : CollisionPair n) (θ s T : ℝ)
    (f : Configuration n → ℝ≥0∞) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 T, singleCollisionAction α θ r s (T - r) f x



end Critical2DKPZ.SHF.Flow

end
