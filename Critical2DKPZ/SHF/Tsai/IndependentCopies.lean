/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Integration

/-! # Independent coordinate copies of a finite family

The joint law of independent variables is the product of their marginal
laws. Applying each variable to its own coordinate in the finite product
of the original probability space produces exactly that same law.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- A finite independent family has the same joint law as its separate coordinate copies. -/
theorem iIndepFun.map_eq_map_coordinateCopies {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (B : Fin m → Ω → X) (hB : ∀ i, Measurable (B i)) (hind : iIndepFun B P) :
    P.map (fun ω i => B i ω) =
      (Measure.pi (fun _ : Fin m => P)).map (fun ω i => B i (ω i)) := by
  rw [hind.map_fun_eq_pi_map (fun i => (hB i).aemeasurable),
    Measure.pi_map_pi (fun i => (hB i).aemeasurable)]


end Critical2DKPZ.SHF.Tsai

end
