/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ApproximateFlowFromSlabComparisons
public import Critical2DKPZ.SHF.Flow.DenseSubsequenceProductLimit

/-! # SHF conditions on countable time sets from slab comparisons -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Under the moment and semigroup hypotheses, the slab comparisons give the SHF conditions for a polymer limit on its countable time set. -/
theorem isDenseSHF_of_isPolymerSubseqLimit_of_comparisons
    (hComparisonOne : ∀ (ϑ : ℝ) (_hPolymerMomentInput : PolymerMomentLimit ϑ)
      (_hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
      (_hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant)) {s t u : ℝ} (_hs : 0 ≤ s)
      (_hst : s < t) (_htu : t < u) (Φ : C_c(Plane × Plane, ℝ)),
      ∀ ε > 0, ∃ v₀ > 0, ∀ v : ℝ, 0 < v → v < v₀ → ∀ᶠ N : ℕ in atTop,
        ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω) - kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabMeanKernel ϑ N t (t + v)) (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε)
    (hComparisonTwo : ∀ (ϑ : ℝ) (_hPolymerMomentInput : PolymerMomentLimit ϑ)
      (_hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
      (_hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant)) {s t u : ℝ} (_hs : 0 ≤ s)
      (_hst : s < t) (_htu : t < u) (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
      (_hw : ContDiff ℝ (⊤ : ℕ∞) w) (_hwc : HasCompactSupport w) (_hw0 : ∀ x, 0 ≤ w x) (_hw1 : ∫ x, w x = 1),
      ∀ ε > 0, ∃ v₀ > 0, ∀ v : ℝ, 0 < v → v < v₀ → ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ᶠ N : ℕ in atTop,
        ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x))
            (polymerMeasure ϑ N t u ω) Φ -
          kernelProductPairing (polymerMeasure ϑ N s t ω)
            (fun a b => ∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) * slabMeanKernel ϑ N t (t + v) y b)
            (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε)
    (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant))
    (D : Set ℝ) (hD : D.Countable)
    (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ) (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  apply _root_.Critical2DKPZ.SHF.Flow.isDenseSHF_of_isPolymerSubseqLimit_of_approximate_flow
    ϑ hPolymerMomentInput hFlatSixthMomentInput ?_ D hD hD0 ψ hψ P Z hZ
  intro s t u hs hst htu Φ w hw hwc hw0 hw1
  exact smoothedProduct_approx_flow_of_comparisons hComparisonOne hComparisonTwo
    ϑ hPolymerMomentInput hFlatSixthMomentInput hSG hs hst htu Φ w hw hwc hw0 hw1

end Critical2DKPZ.SHF.Flow
