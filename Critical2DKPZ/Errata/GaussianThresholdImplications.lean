/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Counterexamples.NP16GaussianThreshold

/-! # Exponential and Gaussian distribution-function thresholds

The implications used in the NP16 comparison argument correspond to thresholds one for the exponential and one half for the Gaussian distribution function. -/

public section

open MeasureTheory

namespace Critical2DKPZ.Errata

/-- The exponential implication is exactly the nonpositive-expression implication. -/
theorem exp_implication_iff_nonpos_implication {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → ℝ) (b : ℝ) {R : ℝ} (hR : 0 < R) :
    ((∀ᵐ ω ∂P, Real.exp (R * A ω) ≤ 1) → Real.exp (R * b) ≤ 1) ↔
      ((∀ᵐ ω ∂P, A ω ≤ 0) → b ≤ 0) := by
  have hsign (x : ℝ) : R * x ≤ 0 ↔ x ≤ 0 := by
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ hR : R * x ≤ R * 0 ↔ x ≤ 0)
  simp only [Real.exp_le_one_iff, hsign]

/-- The Gaussian-CDF implication is exactly the nonpositive-expression implication. -/
theorem cdf_implication_iff_nonpos_implication {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → ℝ) (b : ℝ) {R : ℝ} (hR : 0 < R) :
    ((∀ᵐ ω ∂P, Ehrhard.gaussianCDF (R * A ω) ≤ (1 / 2 : ℝ)) →
        Ehrhard.gaussianCDF (R * b) ≤ (1 / 2 : ℝ)) ↔
      ((∀ᵐ ω ∂P, A ω ≤ 0) → b ≤ 0) := by
  have hsign (x : ℝ) : R * x ≤ 0 ↔ x ≤ 0 := by
    simpa only [mul_zero] using (mul_le_mul_iff_right₀ hR : R * x ≤ R * 0 ↔ x ≤ 0)
  simp only [(gaussianCDF_le_half_iff_and_not_le_zero _).1, hsign]

end Critical2DKPZ.Errata
