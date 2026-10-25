/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Inputs
public import Critical2DKPZ.SmallScales.NoLocalSignedMeasureBridge
public import Critical2DKPZ.SmallScales.DistributionMeasureObstruction
public import Critical2DKPZ.SmallScales.DilatedFieldGrowth
public import Critical2DKPZ.SmallScales.SmallScaleCLT

/-! # Local and global obstructions to signed-measure representations -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- The small-scale Gaussian limit and spatial invariance imply that almost surely the KPZ distribution has no difference-of-locally-finite-measures representation on any nonempty open set. -/
theorem kpz_no_local_signedMeasure_of_CLT_and_invariance
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
    (_hsym : ShfSymmetriesAt ϑ P Z) (_hC8 : SmallScaleSHFLogNormality.{u})
    (_hC12 : ToyJointAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (_hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z) (_hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (_hH : IsCriticalKPZ P Z H)
    (hR7 : KpzTransportAt P H) {t : ℝ} (ht : 0 < t)
    (hCLT : ∀ (t : ℝ), 0 < t → ∀ (x : Plane) (φ : TestFn) (_hφ : ∀ y, 0 ≤ φ y),
      TendstoInDistribution
        (fun ε ω => H t 0 ω (φ.dilate ε x) /
          Real.sqrt (Real.log (Real.log ε⁻¹)))
        (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P)
        (gaussianReal 0 ((∫ y, φ y) ^ 2).toNNReal)) :
    ∀ᵐ ω ∂P, ∀ U : Set Plane, IsOpen U → U.Nonempty → ¬ ∃ μ ν : Measure Plane,
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤ ∧ ν K < ⊤) ∧
      ∀ φ : TestFn, tsupport φ ⊆ U →
        H t 0 ω φ = (∫ y, φ y ∂μ) - ∫ y, φ y ∂ν := by
  have hCLTunit : TendstoInDistribution
      (fun ε ω => H t 0 ω (Analysis.Sobolev.unitMassTestFn.dilate ε 0) /
        Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (gaussianReal 0 1) := by
    simpa [Analysis.Sobolev.integral_unitMassTestFn] using
      hCLT t ht 0 Analysis.Sobolev.unitMassTestFn Analysis.Sobolev.unitMassTestFn_nonneg
  obtain ⟨ε, hεlim, hε, hGrowth⟩ :=
    ae_eventually_large_unitMass_dilate_of_CLT_and_invariance
      P H hR7 ht hCLTunit
  filter_upwards [hGrowth] with ω hω
  exact no_local_measure_representation_of_eventually_large_dilates
    (H t 0 ω) ε hεlim (fun k => (hε k).1) hω


/-- Almost surely, the critical KPZ distribution has no difference-of-locally-finite-measures representation on any nonempty open set. -/
theorem kpz_no_local_signedMeasure_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC8 : SmallScaleSHFLogNormality.{u})
    (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hR7 : KpzTransportAt P H) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ U : Set Plane, IsOpen U → U.Nonempty → ¬ ∃ μ ν : Measure Plane,
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤ ∧ ν K < ⊤) ∧
      ∀ φ : TestFn, tsupport φ ⊆ U →
        H t 0 ω φ = (∫ y, φ y ∂μ) - ∫ y, φ y ∂ν := by
  apply kpz_no_local_signedMeasure_of_CLT_and_invariance
    ϑ P Z hZ hsym hC8 hC12 hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH hR7 ht
  intro T hT x φ hφ
  exact criticalKPZ_smallScaleCLT_of
    ϑ P Z hZ hsym hC8 hC12 hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH T hT x φ hφ

/-- Almost surely, the critical KPZ distribution is not a difference of two locally finite measures on the plane. -/
theorem criticalKPZ_not_signedMeasure_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC8 : SmallScaleSHFLogNormality.{u})
    (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) (hR7 : KpzTransportAt P H)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ¬ ∃ μ ν : Measure Plane, IsLocallyFiniteMeasure μ ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : TestFn, H t 0 ω φ = (∫ x, φ x ∂μ) - ∫ x, φ x ∂ν := by
  apply no_local_signedMeasure_implies_no_global P H t
  exact kpz_no_local_signedMeasure_of
    ϑ P Z hZ hsym hC8 hC12 hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH hR7 ht

end Critical2DKPZ.SmallScales

end
