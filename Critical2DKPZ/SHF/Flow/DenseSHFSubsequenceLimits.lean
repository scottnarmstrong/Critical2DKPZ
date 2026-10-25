/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabApproxFlow
public import Critical2DKPZ.SHF.Flow.DenseSubsequenceProductLimit

/-! # SHF conditions for polymer limits on countable time sets -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Under the moment and semigroup hypotheses, a polymer subsequential limit satisfies the SHF conditions on its countable time set. -/
theorem isDenseSHF_of_isPolymerSubseqLimit_of (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ) (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant))
    (D : Set ℝ) (hD : D.Countable)
    (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ) (hψ : StrictMono ψ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  apply isDenseSHF_of_isPolymerSubseqLimit_of_approximate_flow
    ϑ hPolymerMomentInput hFlatSixthMomentInput ?_ D hD hD0 ψ hψ P Z hZ
  intro s t u hs hst htu Φ w hw hwc hw0 hw1
  exact smoothedProduct_approx_flow_of ϑ hPolymerMomentInput hFlatSixthMomentInput hSG hs hst htu Φ w hw hwc hw0 hw1

end Critical2DKPZ.SHF.Flow
