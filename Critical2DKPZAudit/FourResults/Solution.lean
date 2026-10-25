/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZAudit.FourResults.SolutionBridge
public import Critical2DKPZStatements.Extensions.CriticalKPZCentralMomentThreePos
public import Critical2DKPZStatements.Extensions.InitialResponseExistsUnique
public import Critical2DKPZStatements.Extensions.ExistsUniqueWienerLawKPZScale
public import Critical2DKPZStatements.Extensions.ExistsUniqueFiniteGffLawKPZMicroscopic

/-! The four results follow from the library theorems through the definition equalities. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal NNReal Pointwise Topology

universe u

namespace Critical2DKPZAudit.FourResults

namespace Extensions

/-- **Theorem A** (strict skewness). -/
theorem criticalKPZ_centralMoment_three_pos (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ0 : ψ ≠ 0) :
    MemLp (fun ω => H t 0 ω ψ) (3 : ℝ≥0∞) P ∧
      0 < centralMoment (fun ω => H t 0 ω ψ) 3 P := by
  exact Critical2DKPZ.Extensions.criticalKPZ_centralMoment_three_pos ϑ P Z hZ H hH t ht ψ hψ hψ0

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
            (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi (0 : ℝ)))) (𝓝 0)) := by
  exact Critical2DKPZ.Extensions.initialResponse_existsUnique ϑ P Z hZ H hH t ht h v ψ

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
        TendstoInDistribution X atTop id (fun _ => P) (μ : Measure (ScalePath S)) := by
  exact Critical2DKPZ.Extensions.existsUnique_wienerLaw_and_kpz_scale_tendstoInDistribution ϑ P Z hZ H hH t ht x φ hφ hφ1 S hS

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
        (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (μ : Measure _) := by
  exact Critical2DKPZ.Extensions.existsUnique_finiteGffLaw_and_kpz_microscopic_tendstoInDistribution ϑ P Z hZ H hH t ht x n f hf

end Extensions

end Critical2DKPZAudit.FourResults

end

end
