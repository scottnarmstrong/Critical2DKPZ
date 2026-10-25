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
public import Critical2DKPZ.Extensions.Definitions.ScalePath

/-!
# `IsWienerLaw`

A definition used in the statement of Theorem C of the note *Four results on the critical 2D KPZ
process* (`docs/four-results.pdf`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions

/-- `μ` has the finite-dimensional distributions of standard Brownian motion on `[0, S]`. -/
def IsWienerLaw (S : ℝ≥0) (μ : ProbabilityMeasure (ScalePath S)) : Prop :=
  ∀ (I : Finset ℝ≥0) (hI : ∀ s ∈ I, (s : ℝ) ≤ S),
    HasLaw (fun f : ScalePath S => fun i : I =>
      f ⟨(i.1 : ℝ), i.1.property, hI i.1 i.2⟩)
      (BrownianReal.projectiveFamily I) (μ : Measure (ScalePath S))

end Critical2DKPZ.Extensions

end

end
