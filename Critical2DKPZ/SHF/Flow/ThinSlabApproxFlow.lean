/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ApproximateFlowFromSlabComparisons
import Critical2DKPZ.SHF.Flow.PairingSlabComparison
import Critical2DKPZ.SHF.Flow.MollifiedProductSlabComparison

/-! # Approximate Chapman–Kolmogorov from the three slab comparisons -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The polymer smoothed product approximates the full pairing in annealed second moment. -/
theorem smoothedProduct_approx_flow_of (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant))
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η → ∀ᶠ N : ℕ in atTop,
      ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x))
          (polymerMeasure ϑ N t u ω) Φ - ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw ≤ ε := by
  exact smoothedProduct_approx_flow_of_comparisons
    polymerMeasure_sub_slabProduct_sq_small_of smoothedProduct_sub_slabProduct_sq_small_of
    ϑ hPolymerMomentInput hFlatSixthMomentInput hSG hs hst htu Φ w hw hwc hw0 hw1

end Critical2DKPZ.SHF.Flow
