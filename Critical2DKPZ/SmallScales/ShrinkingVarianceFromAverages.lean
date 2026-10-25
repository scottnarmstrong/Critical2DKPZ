/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Inputs
public import Critical2DKPZ.SmallScales.ShrinkingVarianceFromHeatStartComparison
public import Critical2DKPZ.SmallScales.PointMatchedComparison
public import Critical2DKPZ.SmallScales.ShrinkingRegularizedReversed
public import Critical2DKPZ.SmallScales.SmallScaleCLT

/-! # Shrinking variance from averaged-field and point-matched estimates -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- For a nonnegative unit-mass test, the KPZ pairing variance is asymptotic to the double logarithm of inverse scale under the stated spatial-average, comparison and Gaussian-limit hypotheses. -/
theorem kpz_shrinking_variance_of_spatial_average_bounds
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (_hC8 : SmallScaleSHFLogNormality.{u})
    (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (_hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z) (_hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y)
    (hφ₁ : ∫ y, φ y = 1) (x : Plane)
    (hReg : ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ x : Plane, ∀ δ : ℝ, 0 < δ → δ ≤ ε ^ 2 →
        eLpNorm (fun ω => ∫ y, φ.dilate ε x y *
          (kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 t δ 0 y ω)) 2 P ≤ ENNReal.ofReal C)
    (hPoint : ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ X : Ω → ℝ, P.map X = P.map (fun ω => H t 0 ω (φ.dilate ε x)) ∧
        Integrable (fun ω => X ω -
          (heatStartLog Z (ε ^ 2) t (ε ^ 2) (x + ε • barycentre φ) ω -
            ∫ ω', heatStartLog Z (ε ^ 2) t (ε ^ 2)
              (x + ε • barycentre φ) ω' ∂P)) P ∧
        ∫ ω, |X ω -
          (heatStartLog Z (ε ^ 2) t (ε ^ 2) (x + ε • barycentre φ) ω -
            ∫ ω', heatStartLog Z (ε ^ 2) t (ε ^ 2)
              (x + ε • barycentre φ) ω' ∂P)| ∂P ≤ C)
    (hCLT : TendstoInDistribution
      (fun ε ω => H t 0 ω (φ.dilate ε x) /
        Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P)
      (gaussianReal 0 ((∫ y, φ y) ^ 2).toNNReal)) :
    (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      MemLp (fun ω => H t 0 ω (φ.dilate ε x)) 2 P) ∧
      Tendsto (fun ε => Var[fun ω => H t 0 ω (φ.dilate ε x); P] /
        Real.log (Real.log ε⁻¹))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
  exact kpz_shrinking_variance_of_stages ϑ P Z hZ hsym hC12 hHeatStartLogInput H hH ht φ hφ hφ₁ x
    hReg hPoint hCLT

/-- For a nonnegative unit-mass test, the KPZ pairing has finite second moment at small scales and variance asymptotic to the double logarithm of inverse scale. -/
theorem kpz_shrinking_variance_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC8 : SmallScaleSHFLogNormality.{u})
    (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (hLatticeSmoothingEnergyInput : LatticeSmoothingErrorEnergy)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) (hφ₁ : ∫ y, φ y = 1) (x : Plane) :
    (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), MemLp (fun ω => H t 0 ω (φ.dilate ε x)) 2 P) ∧
      Tendsto (fun ε => Var[fun ω => H t 0 ω (φ.dilate ε x); P] / Real.log (Real.log ε⁻¹))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
  apply kpz_shrinking_variance_of_spatial_average_bounds ϑ P Z hZ hsym hC8 hC12 hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH ht
    φ hφ hφ₁ x
    (kpzRegularizedReversed_shrinking_le_of ϑ P Z hZ hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput ht φ)
    (kpz_point_matched_comparison_of ϑ P Z hZ hsym hC12 hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH ht
      φ hφ hφ₁ x)
    (criticalKPZ_smallScaleCLT_of ϑ P Z hZ hsym hC8 hC12 hHeatStartLogInput hHeatStartLogFieldInput hLatticeSmoothingEnergyInput H hH t ht x φ hφ)

end Critical2DKPZ.SmallScales

end
