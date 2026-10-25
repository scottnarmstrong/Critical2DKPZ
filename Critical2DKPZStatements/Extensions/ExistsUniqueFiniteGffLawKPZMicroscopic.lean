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
public import Critical2DKPZ.Extensions.Definitions.LogCovariance
public import Critical2DKPZ.Extensions.Definitions.IsFiniteGffLaw
public import Critical2DKPZ.Extensions.Provider.ExistsUniqueFiniteGffLawKPZMicroscopic

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u

namespace Critical2DKPZ.Extensions

/-- **Theorem D** (Gaussian free field tangent). -/
theorem existsUnique_finiteGffLaw_and_kpz_microscopic_tendstoInDistribution (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (x : Plane) (n : ℕ) (f : Fin n → TestFn)
    (hf : ∀ i, (∫ y : Plane, f i y) = 0) :
    ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      IsFiniteGffLaw f μ ∧
      TendstoInDistribution
        (fun (ε : ℝ) (ω : Ω) => WithLp.toLp 2
          (fun i : Fin n => Real.sqrt (Real.log ε⁻¹) * H t 0 ω ((f i).dilate ε x)))
        (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (μ : Measure _) :=
  by exact Critical2DKPZ.Extensions.Provider.existsUnique_finiteGffLaw_and_kpz_microscopic_tendstoInDistribution ϑ P Z hZ H hH t ht x n f hf
end Critical2DKPZ.Extensions

end

end
