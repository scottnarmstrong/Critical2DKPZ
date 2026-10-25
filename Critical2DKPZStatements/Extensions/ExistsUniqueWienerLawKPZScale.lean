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
public import Critical2DKPZ.Extensions.Definitions.ScaleInterval
public import Critical2DKPZ.Extensions.Definitions.ScalePath
public import Critical2DKPZ.Extensions.Definitions.ScaleRadius
public import Critical2DKPZ.Extensions.Definitions.ScaledPairing
public import Critical2DKPZ.Extensions.Definitions.IsWienerLaw
public import Critical2DKPZ.Extensions.Provider.ExistsUniqueWienerLawKPZScale

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u

namespace Critical2DKPZ.Extensions

/-- **Theorem C** (Brownian motion across scales). -/
theorem existsUnique_wienerLaw_and_kpz_scale_tendstoInDistribution (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (S : ℝ≥0) (hS : 0 < S) :
    ∃! μ : ProbabilityMeasure (ScalePath S),
      IsWienerLaw S μ ∧
      ∃ X : Set.Ioi (0 : ℝ) → Ω → ScalePath S,
        (∀ L ω s, X L ω s = scaledPairing (H t 0 ω) φ x L s) ∧
        TendstoInDistribution X atTop id (fun _ => P) (μ : Measure (ScalePath S)) :=
  by exact Critical2DKPZ.Extensions.Provider.existsUnique_wienerLaw_and_kpz_scale_tendstoInDistribution ϑ P Z hZ H hH t ht x φ hφ hφ1 S hS
end Critical2DKPZ.Extensions

end

end
