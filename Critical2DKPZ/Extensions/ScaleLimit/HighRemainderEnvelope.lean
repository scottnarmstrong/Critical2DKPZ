/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HighRemainderBounds
public import Critical2DKPZ.Extensions.ScaleLimit.WeightedL2CurveEnvelope
import Mathlib.Tactic

/-! # A uniform weighted square envelope for the high remainder -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- Continuous high-remainder versions with a square envelope whose budget
is uniform in the upper endpoint. The inverse-square derivative weight
removes any dependence on the radius ratio `β/α`. -/
theorem exists_bandHighRemainder_square_envelope (hD : StationarySpectralData P D ν)
    (φ : TestFn) (x : Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ α β : ℝ, 0 < α → α < β →
      ∃ w : ℝ → Ω → ℝ, ∃ Z : Ω → ℝ,
        (∀ r ∈ Set.Icc α β, w r =ᵐ[P] (bandHighRemainder hD a φ x r : Ω → ℝ)) ∧
        (∀ᵐ ω ∂P, ContinuousOn (fun r => w r ω) (Set.Icc α β)) ∧
        Integrable Z P ∧ (∀ ω, 0 ≤ Z ω) ∧
        (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc α β, w r ω ^ 2 ≤ Z ω) ∧
        (∫ ω, Z ω ∂P) ≤ C * (a / α) ^ 2 * specMass ν a⁻¹ := by
  obtain ⟨C, hC, hraw⟩ := high_remainder_raw_bounds hD φ x
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hraw] with a ha hrawa
  have ha' : 0 < a := ha
  intro α β hα hαβ
  let V : ℝ → Lp ℝ 2 P := fun r => bandHighRemainderDerivative hD a φ x (max α r)
  have hV : Continuous V := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (continuousAt_bandHighRemainderDerivative hD a φ x
      (hα.trans_le (le_max_left _ _))).comp
      (continuous_const.max continuous_id).continuousAt
  have hd (r : ℝ) (hr : r ∈ Set.Icc α β) :
      HasDerivAt (bandHighRemainder hD a φ x) (V r) r := by
    change HasDerivAt _ (bandHighRemainderDerivative hD a φ x (max α r)) r
    rw [max_eq_right hr.1]
    exact hasDerivAt_bandHighRemainder hD φ x ha' (hα.trans_le hr.1)
  have hb (r : ℝ) (hr : r ∈ Set.Icc α β) :
      ‖V r‖ ^ 2 ≤ C * r⁻¹ ^ 2 * (a / r) ^ 2 * specMass ν a⁻¹ := by
    change ‖bandHighRemainderDerivative hD a φ x (max α r)‖ ^ 2 ≤ _
    rw [max_eq_right hr.1]
    exact (hrawa r (hα.trans_le hr.1)).2
  obtain ⟨w, Z, hw, hc, hZi, hZ0, hZw, hZ⟩ := exists_weighted_L2_curve_square_envelope P
    (bandHighRemainder hD a φ x) V hV ha' hα hαβ hC.le ENNReal.toReal_nonneg hd
    (hrawa α hα).1 hb
  refine ⟨w, Z, hw, hc, hZi, hZ0, hZw, ?_⟩
  exact hZ

end Critical2DKPZ.Extensions.ScaleLimit
