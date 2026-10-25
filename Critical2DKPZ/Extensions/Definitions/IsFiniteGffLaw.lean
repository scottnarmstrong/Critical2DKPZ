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
public import Critical2DKPZ.Extensions.Definitions.LogCovariance

/-!
# `IsFiniteGffLaw`

A definition used in the statement of Theorem D of the note *Four results on the critical 2D KPZ
process* (`docs/four-results.pdf`).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions

/-- `μ` is the centred Gaussian law on `ℝⁿ` with covariance `(Q(f_i, f_j))_{i,j}`. -/
def IsFiniteGffLaw {n : ℕ} (f : Fin n → TestFn)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) : Prop :=
  AEMeasurable (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
  IsGaussian (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
  (∀ i, MemLp (fun z : EuclideanSpace ℝ (Fin n) => z i) 2
    (μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
  (∀ i, (∫ z : EuclideanSpace ℝ (Fin n), z i ∂μ) = 0) ∧
  (∀ i j, covariance (fun z : EuclideanSpace ℝ (Fin n) => z i)
    (fun z : EuclideanSpace ℝ (Fin n) => z j) (μ : Measure _) =
      logCovariance (f i) (f j)) ∧
  ∀ z : EuclideanSpace ℝ (Fin n),
    charFun (μ : Measure _) z =
      Complex.exp (Complex.ofReal (-(∑ i, ∑ j,
        z i * logCovariance (f i) (f j) * z j) / 2))

end Critical2DKPZ.Extensions

end

end
