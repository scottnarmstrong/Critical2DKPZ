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
public import Critical2DKPZ.Extensions.Definitions.ResponseCutoff
public import Critical2DKPZ.Extensions.Definitions.RestrictJet
public import Critical2DKPZ.Extensions.Provider.InitialResponseExistsUnique

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u

namespace Critical2DKPZ.Extensions

/-- **Theorem B** (response to the initial condition). -/
theorem initialResponse_existsUnique (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∃! R : Ω →ₘ[P] C(ℝ, Fin 3 → ℝ),
      (∀ q : ℝ, (fun ω => R ω q 0) =ᵐ[P]
        (fun ω => H t (h + q • v) ω ψ - H t h ω ψ)) ∧
      (∀ᵐ ω ∂P, ∀ q : ℝ,
        HasDerivAt (fun u => R ω u 0) (R ω q 1) q ∧
        HasDerivAt (fun u => R ω u 1) (R ω q 2) q ∧
        |R ω q 0| ≤ (∫ x, |ψ x|) * ‖v‖ * |q| ∧
        |R ω q 1| ≤ (∫ x, |ψ x|) * ‖v‖ ∧
        |R ω q 2| ≤ (∫ x, |ψ x|) * ‖v‖ ^ 2 ∧
        ((∀ x, 0 ≤ ψ x) → 0 ≤ R ω q 2)) ∧
      (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P,
        ContDiff ℝ 3 (responseCutoff Z t r h v ψ ω)) ∧
      (∀ (a b : ℝ), a ≤ b → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
        MemLp (fun ω => restrictJet a b (R ω)) p P ∧
        ∃ Q : Set.Ioi (0 : ℝ) → Ω → C(Set.Icc a b, Fin 3 → ℝ),
          (∀ r, MemLp (Q r) p P) ∧
          (∀ r, ∀ᵐ ω ∂P, ∀ q : Set.Icc a b, ∀ j : Fin 3,
            Q r ω q j = iteratedDeriv (j : ℕ) (responseCutoff Z t r h v ψ ω) q) ∧
          Tendsto (fun r => eLpNorm
            (fun ω => Q r ω - restrictJet a b (R ω)) p P)
            (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi (0 : ℝ)))) (𝓝 0)) :=
  by exact Critical2DKPZ.Extensions.Provider.initialResponse_existsUnique ϑ P Z hZ H hH t ht h v ψ
end Critical2DKPZ.Extensions

end

end
