/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandAverageDerivative
public import Critical2DKPZ.Extensions.ScaleLimit.L2CurveEnvelope
import Mathlib.Tactic

/-! # A uniform square envelope for the low-frequency remainder -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The low remainder vanishes at radius zero for a unit-integral test. -/
theorem bandLowRemainder_zero (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane) {b : ℝ} (hb : 0 < b) :
    bandLowRemainder hD b φ x 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (norm_bandLowRemainder_le hD φ hφ x hb 0).trans_eq (by simp)

/-- A continuous version of the low remainder has an integrable square
majorant, uniformly over the entire radius interval. Its bound is valid even
when the coarse band scale is large, as required at time zero. -/
theorem exists_bandLowRemainder_square_envelope (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane)
    {b β : ℝ} (hb : 0 < b) (hβ : 0 < β) :
    ∃ u : ℝ → Ω → ℝ, ∃ Z : Ω → ℝ,
      (∀ r ∈ Set.Icc 0 β, u r =ᵐ[P] (bandLowRemainder hD b φ x r : Ω → ℝ)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun r => u r ω) (Set.Icc 0 β)) ∧
      Integrable Z P ∧ (∀ ω, 0 ≤ Z ω) ∧
      (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc 0 β, u r ω ^ 2 ≤ Z ω) ∧
      (∫ ω, Z ω ∂P) ≤
        8 * testFirstMoment φ ^ 2 * (β / b) ^ 2 * specMass ν (2 / b) := by
  let K := (Real.sqrt (specMass ν (2 / b)) * (2 / b)) * testFirstMoment φ
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (testFirstMoment_nonneg φ)
  have hd (r : ℝ) (_hr : r ∈ Set.Icc 0 β) : HasDerivAt
      (bandLowRemainder hD b φ x) (bandAverageDerivative hD b φ x r) r := by
    change HasDerivAt (fun q => bandAverage hD b φ x q - schwartzExt hD (zetaScaled b x)) _ r
    exact (hasDerivAt_bandAverage hD hb φ x r).sub_const _
  obtain ⟨u, Z, hu, hc, hZi, hZ0, hZu, hZ⟩ := exists_L2_curve_square_envelope P
    (bandLowRemainder hD b φ x) (bandAverageDerivative hD b φ x)
    (continuous_bandAverageDerivative hD hb φ x) (bandLowRemainder_zero hD φ hφ x hb)
    hβ hK hd (fun r _ => norm_bandAverageDerivative_le hD hb φ x r)
  refine ⟨u, Z, hu, hc, hZi, hZ0, hZu, hZ.trans_eq ?_⟩
  dsimp [K]
  rw [mul_pow, mul_pow, Real.sq_sqrt (show 0 ≤ specMass ν (2 / b) from ENNReal.toReal_nonneg)]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
