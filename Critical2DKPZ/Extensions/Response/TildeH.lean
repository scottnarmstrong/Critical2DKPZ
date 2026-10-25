/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.TestFn

/-! # Spatially smoothed centred KPZ pairings

The note's `H̃^{(r)}_t` smooths the terminal position of the time-`t` flow.
Its centring is independent of the initial profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.Response

/-- The spatially smoothed centred pairing of the note, §4.3. -/
def spatialCenteredPairing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω) : ℝ :=
  ∫ x, ψ x * (Real.log (shfPairing Z 0 t (fun y => Real.exp (h y))
    (fun y => heatKernel r (y - x)) ω) -
    ∫ ω', Real.log (shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω') ∂P)

end Critical2DKPZ.Extensions.Response
