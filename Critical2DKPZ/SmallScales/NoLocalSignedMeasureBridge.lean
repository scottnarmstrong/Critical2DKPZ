/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Distr
public import Critical2DKPZ.Definitions.TestFn
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # From the local obstruction to the global signed-measure obstruction -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported Distributions

namespace Critical2DKPZ.SmallScales

/-- A globally defined difference of locally finite measures would be a local representative on every
open nonempty set. This reduces the global obstruction to the local one at `U = univ`. -/
theorem no_local_signedMeasure_implies_no_global {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (t : ℝ)
    (hNoLocal : ∀ᵐ ω ∂P, ∀ U : Set Plane, IsOpen U → U.Nonempty →
      ¬ ∃ μ ν : Measure Plane,
        (∀ K, IsCompact K → K ⊆ U → μ K < ⊤ ∧ ν K < ⊤) ∧
        ∀ φ : TestFn, tsupport φ ⊆ U →
          H t 0 ω φ = (∫ y, φ y ∂μ) - ∫ y, φ y ∂ν) :
    ∀ᵐ ω ∂P, ¬ ∃ μ ν : Measure Plane, IsLocallyFiniteMeasure μ ∧ IsLocallyFiniteMeasure ν ∧
      ∀ φ : TestFn, H t 0 ω φ = (∫ x, φ x ∂μ) - ∫ x, φ x ∂ν := by
  filter_upwards [hNoLocal] with ω hω
  rintro ⟨μ, ν, hμ, hν, hrepr⟩
  apply hω Set.univ isOpen_univ ⟨0, Set.mem_univ _⟩
  refine ⟨μ, ν, ?_, ?_⟩
  · intro K hK _
    have hμc : IsFiniteMeasureOnCompacts μ :=
      @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure Plane inferInstance inferInstance μ hμ
    have hνc : IsFiniteMeasureOnCompacts ν :=
      @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure Plane inferInstance inferInstance ν hν
    exact ⟨@IsFiniteMeasureOnCompacts.lt_top_of_isCompact Plane inferInstance inferInstance μ hμc K hK,
      @IsFiniteMeasureOnCompacts.lt_top_of_isCompact Plane inferInstance inferInstance ν hνc K hK⟩
  · intro φ _
    exact hrepr φ

end Critical2DKPZ.SmallScales

end
