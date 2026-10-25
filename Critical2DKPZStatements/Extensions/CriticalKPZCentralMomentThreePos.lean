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
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Extensions.Provider.CriticalKPZCentralMomentThreePos

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u

namespace Critical2DKPZ.Extensions

/-- **Theorem A** (strict skewness). -/
theorem criticalKPZ_centralMoment_three_pos (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ0 : ψ ≠ 0) :
    MemLp (fun ω => H t 0 ω ψ) (3 : ℝ≥0∞) P ∧
      0 < centralMoment (fun ω => H t 0 ω ψ) 3 P :=
  by exact Critical2DKPZ.Extensions.Provider.criticalKPZ_centralMoment_three_pos ϑ P Z hZ H hH t ht ψ hψ hψ0
end Critical2DKPZ.Extensions

end

end
