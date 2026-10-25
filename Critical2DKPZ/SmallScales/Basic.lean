/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.HeatKernel

/-! # Heat-start logarithms and test-function barycentres -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SmallScales

/-- The logarithm of the heat-start stochastic heat flow mass with smoothing time `δ`, initial time `s` and terminal time `T`. -/
def heatStartLog {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (s T δ : ℝ) (x : Plane)
    (ω : Ω) : ℝ :=
  Real.log (shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω)

/-- The first spatial moment of a test function, equal to its barycentre when its integral is one. -/
def barycentre (φ : TestFn) : Plane := ∫ y, φ y • y

end Critical2DKPZ.SmallScales
