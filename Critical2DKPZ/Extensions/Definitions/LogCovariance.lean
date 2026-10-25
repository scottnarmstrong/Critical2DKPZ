/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Critical2DKPZ.Definitions.TestFn

/-!
# `logCovariance`

A definition used in the statement of Theorem D of the note *Four results on the critical 2D KPZ
process* (`docs/four-results.pdf`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions

/-- `Q(f, g) = −∬ f(u) g(v) log|u − v| du dv` (note, Theorem D). -/
def logCovariance (f g : TestFn) : ℝ :=
  -(∫ u : Plane, ∫ v : Plane, f u * g v * Real.log ‖u - v‖)

end Critical2DKPZ.Extensions

end

end
