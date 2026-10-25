/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleKernelActions
public import Critical2DKPZ.SHF.Flow.PairingSlabComparisonPairingMoment

/-! Positive endpoint forms describe the two-particle semigroup comparison. -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The positive two-particle endpoint form at one time. -/
def momentKernelTwoEndpointForm (θ h : ℝ)
    (f g : Configuration 2 → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x : Configuration 2, g x *
    (∫⁻ y : Configuration 2, momentKernel 2 θ h x y * f y)


/-- The one-collision middle correction in the endpoint bilinear form. -/
def slabMomentKernelTwoCorrectionEndpointForm (θ a v b : ℝ)
    (f g : Configuration 2 → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x : Configuration 2, g x *
    twoParticleWeightedAction θ 0 a
      (twoParticleCorrectionWeightedAction θ 0 v
        (twoParticleWeightedAction θ 0 b f)) x



end Critical2DKPZ.SHF.Flow

end
