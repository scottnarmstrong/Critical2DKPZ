/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.Basic
public import Critical2DKPZ.Definitions.CellAverage
public import Critical2DKPZ.Definitions.Disorder
public import Critical2DKPZ.Definitions.DisorderLaw
public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsEhrhardType
public import Critical2DKPZ.Definitions.KpzLattice
public import Critical2DKPZ.Definitions.KpzLatticeReversed
public import Critical2DKPZ.Definitions.KpzRegularizedReversed
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ProfileP2Fun
public import Critical2DKPZ.Definitions.ShfSigma
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.SHF.Limit.Basic

/-! # Symmetry and convergence properties of the critical stochastic heat flow -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction CompactlySupported ENNReal Topology

universe u v

namespace Critical2DKPZ.LocalSobolev

open Critical2DKPZ.SHF.Limit

/-- The critical stochastic heat flow has spatial and temporal symmetries, continuity in probability, and Ehrhard-type heat-start logarithms. -/
def ShfSymmetriesAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  (∀ z : Plane, IsCriticalSHF ϑ P fun s t ω => (Z s t ω).map fun p => (p.1 + z, p.2 + z)) ∧
    (∀ R : Plane ≃ₗᵢ[ℝ] Plane, LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
      IsCriticalSHF ϑ P fun s t ω => (Z s t ω).map fun p => (R p.1, R p.2)) ∧
    (∀ u : ℝ, 0 ≤ u → IsCriticalSHF ϑ P fun s t ω => Z (s + u) (t + u) ω) ∧
    (∀ a : ℝ, 0 < a → IsCriticalSHF (ϑ + Real.log a) P fun s t ω =>
      ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)) ∧
    (∀ (T : ℝ) (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i ∧ t i ≤ T) →
      ∀ φ : Fin k → C_c(Plane × Plane, ℝ),
        P.map (fun ω i => ∫ p, φ i (p.2, p.1) ∂(Z (T - t i) (T - s i) ω)) =
          P.map (fun ω i => ∫ p, φ i p ∂(Z (s i) (t i) ω))) ∧
    (∀ (φ : C_c(Plane × Plane, ℝ)) (s t : ℝ), 0 ≤ s → s < t →
      TendstoInMeasure P (fun (q : ℝ × ℝ) ω => ∫ p, φ p ∂(Z q.1 q.2 ω))
        (nhdsWithin (s, t) {q | 0 ≤ q.1 ∧ q.1 < q.2}) (fun ω => ∫ p, φ p ∂(Z s t ω))) ∧
    (∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P ∧
      IsEhrhardType (P.map fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)))

/-- Heat-start logarithmic fields converge jointly at finitely many times and initial profiles on each positive time horizon. -/
def ToyJointAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ T : ℝ, 0 < T →
  ∃ X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ,
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn), 0 ≤ t → t < T → Measurable[shfSigma Z] (X t h₀ φ)) ∧
      (∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a : ℝ), 0 < a → a ≤ T → ∃ C δ₁ : ℝ, 0 < δ₁ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ t : ℝ, 0 ≤ t → t ≤ T - a →
          eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) 2 P ≤
            ENNReal.ofReal (C * |Real.log (δ / (T - t))| ^ (-(1 : ℝ) / 40))) ∧
      (∀ (t : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞), 0 ≤ t → t < T → 1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm (fun ω =>
            (∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) - X t h₀ φ ω) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
        (∀ i, 0 ≤ t i ∧ t i < T) →
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
            ∫ x, φ i x * kpzLatticeReversed ϑ N (t i) T (h₀ i) x ω)
          atTop (fun ω i => X (t i) (h₀ i) (φ i) ω) (fun _ => disorderLaw) P) ∧
      (∀ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr, IsCriticalKPZ P Z H →
        ∀ (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
          (∀ i, 0 ≤ t i ∧ t i < T) →
          P.map (fun ω i => X (t i) (h₀ i) (φ i) ω) = P.map (fun ω i => H (T - t i) (h₀ i) ω (φ i)))

/-- Fixed-width joint convergence of heat-start logarithms and their moments.
The limit moment is a Bochner integral; integrability of that limiting logarithm
is not part of this proposition. -/
def HeatStartLogAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ (T : ℝ) (h₀ : Plane →ᵇ ℝ) (k : ℕ) (s δ : Fin k → ℝ) (x : Fin k → Plane),
    (∀ i, 0 ≤ s i ∧ s i < T ∧ 0 < δ i) →
  (∀ i, ∀ᵐ ω ∂P, 0 < shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
      (fun y => Real.exp (h₀ y)) ω) ∧
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) => Real.log (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s i)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
        (cellAverage N fun y => Real.exp (h₀ y)) ω))
      atTop
      (fun ω i => Real.log (shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
        (fun y => Real.exp (h₀ y)) ω))
      (fun _ => disorderLaw) P ∧
    ∀ (i : Fin k) (p : ℝ), 0 < p →
      Tendsto (fun N : ℕ => ∫ ω, |Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s i)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N (x i)))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)| ^ p ∂disorderLaw) atTop
        (𝓝 (∫ ω, |Real.log (shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x i))
          (fun y => Real.exp (h₀ y)) ω)| ^ p ∂P))

/-- Joint convergence of the spatially tested heat-start logarithm fields. -/
def HeatStartLogFieldAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ (T : ℝ) (k : ℕ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (s δ : Fin k → ℝ) (φ : Fin k → TestFn),
    (∀ i, 0 ≤ s i ∧ s i < T ∧ 0 < δ i) →
  TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) => ∫ x, φ i x * Real.log (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s i)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp (h₀ i y)) ω))
      atTop
      (fun ω i => ∫ x, φ i x * Real.log (shfPairing Z (s i) T (fun y => heatKernel (δ i) (y - x))
        (fun y => Real.exp (h₀ i y)) ω))
      (fun _ => disorderLaw) P

/-- Integrability and convergence of heat-start SHF pairings with bounded terminal data. -/
def HeatBoundedPairingAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
  (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
    Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
    (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) => ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
      atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) (fun _ => disorderLaw) P

/-- Critical stochastic heat flows with the same parameter have identical finite-dimensional laws. -/
def CriticalSHFFddUnique : Prop :=
  ∀ (ϑ : ℝ) {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)),
    IsCriticalSHF ϑ P Z → IsCriticalSHF ϑ P' Z' → ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)

/-- Finite vectors of tested forward and reversed lattice fields have asymptotically equal expectations against bounded continuous functions. -/
def LatticeReverseLawClose (ϑ : ℝ) : Prop :=
  ∀ (T : ℝ) (k : ℕ) (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn),
    (∀ i, 0 < t i ∧ t i ≤ T) → ∀ g : (Fin k → ℝ) →ᵇ ℝ,
      Tendsto (fun N : ℕ =>
          (∫ ω, g (fun i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω) ∂disorderLaw) -
            ∫ ω, g (fun i => ∫ x, φ i x * kpzLatticeReversed ϑ N (T - t i) T (h₀ i) x ω) ∂disorderLaw)
        atTop (𝓝 0)

end Critical2DKPZ.LocalSobolev

end
