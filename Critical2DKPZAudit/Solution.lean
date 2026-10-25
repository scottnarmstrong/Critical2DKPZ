/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZAudit.SolutionBridge

/-! Theorem 1.2 gives a stochastic-heat-flow-measurable KPZ field and its regularized and lattice limits. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZAudit

/-- The KPZ field exists, is SHF-measurable, and is the regularized and lattice limit. -/
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
          (fun _ => disorderLaw) P) := by
  exact Critical2DKPZ.criticalKPZ_main ϑ P Z hZ

end Critical2DKPZAudit
