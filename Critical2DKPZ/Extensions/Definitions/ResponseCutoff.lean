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
public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.TestFn

/-!
# `responseCutoff`

A definition used in the statement of Theorem B of the note *Four results on the critical 2D KPZ
process* (`docs/four-results.pdf`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions

/-- Cutoff response (note (1.2)): `∫ ψ(x) {log Z_{0,t}(e^{h+qv}, g_r^{(x)}) − log Z_{0,t}(e^h, g_r^{(x)})} dx`. -/
def responseCutoff {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω) (q : ℝ) : ℝ :=
  ∫ x, ψ x * (Real.log (shfPairing Z 0 t
    (fun y => Real.exp (h y + q * v y)) (fun y => heatKernel r (y - x)) ω) -
    Real.log (shfPairing Z 0 t (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω))

end Critical2DKPZ.Extensions

end

end
