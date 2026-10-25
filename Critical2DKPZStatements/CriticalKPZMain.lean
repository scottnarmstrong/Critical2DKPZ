/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.KpzLattice
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.LocalNegSobolevSq
public import Critical2DKPZ.Definitions.MemLocalNegSobolev
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ShfSigma
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.ToLocNegSobolevTuple
public import Critical2DKPZ.Provider.CriticalKPZMain

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **Theorem 1.2** (Critical 2D KPZ Process, `thm:main`, §1.2, with joint convergence in `h₀`,
§6.2). -/
theorem criticalKPZ_main (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr,
      IsCriticalKPZ P Z H ∧
      -- `H` is a measurable function of the SHF
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn), Measurable[shfSigma Z] (fun ω => H t h₀ ω φ)) ∧
      -- `H` takes values in `⋂_{a>0} H^{-a}_loc`
      (∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P, ∀ a, 0 < a → MemLocalNegSobolev a (H t h₀ ω)) ∧
      -- the regularised fields are locally integrable functions
      (∀ t δ, 0 < δ → δ < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P,
        LocallyIntegrable (fun x => kpzRegularized P Z t δ h₀ x ω)) ∧
      -- `ℋ^{(δ)} → ℋ` in probability in `H^{-a}_loc`
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (a : ℝ), 0 < a → ∀ (χ : TestFn) (ε : ℝ≥0∞), 0 < ε →
        Tendsto (fun δ => P {ω | ε < localNegSobolevSq a
            (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤ - H t h₀ ω) χ})
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      -- `L^p` convergence against test functions
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      -- `ℋ^{(N)} → ℋ` in law in `(H^{-a}_loc)^k`, jointly at finitely many `(tᵢ, h₀ᵢ)`
      (∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)), (∀ i, 0 < t i) → ∀ a, 0 < a →
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) => toLocNegSobolevTuple a fun i =>
            Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤)
          atTop (fun ω => toLocNegSobolevTuple a fun i => H (t i) (h₀ i) ω)
          (fun _ => disorderLaw) P) :=
  by exact Critical2DKPZ.Provider.criticalKPZ_main ϑ P Z hZ
end Critical2DKPZ

end

end
