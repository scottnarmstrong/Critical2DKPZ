/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Identifying positive integral ratios with real ratios -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- For nonnegative integrable functions, the ratio of nonnegative integrals agrees
with the real ratio after conversion to real numbers, including at a zero denominator. -/
theorem lintegralRatio_toReal_eq_integralRatio {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) (F G : E → ℝ) (hF : Integrable F μ) (hG : Integrable G ν)
    (hF0 : 0 ≤ᵐ[μ] F) (hG0 : 0 ≤ᵐ[ν] G) :
    ((∫⁻ p, ENNReal.ofReal (F p) ∂μ) / (∫⁻ p, ENNReal.ofReal (G p) ∂ν)).toReal =
      (∫ p, F p ∂μ) / (∫ p, G p ∂ν) := by
  rw [ENNReal.toReal_div, ← ofReal_integral_eq_lintegral_ofReal hF hF0,
    ← ofReal_integral_eq_lintegral_ofReal hG hG0,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hF0),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hG0)]

/-- The positive tensor ratio of two endpoint measures is its real counterpart. -/
theorem positiveTensorRatio_toReal_eq (μ ν : Measure (Plane × Plane))
    (f g : Plane → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hnum : Integrable (fun p : Plane × Plane => f p.1 * g p.2) μ)
    (hden : Integrable (fun p : Plane × Plane => f p.1) ν) :
    ((∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (g p.2) ∂μ) /
      (∫⁻ p, ENNReal.ofReal (f p.1) ∂ν)).toReal =
      (∫ p, f p.1 * g p.2 ∂μ) / (∫ p, f p.1 ∂ν) := by
  have hprod (p : Plane × Plane) :
      ENNReal.ofReal (f p.1) * ENNReal.ofReal (g p.2) = ENNReal.ofReal (f p.1 * g p.2) :=
    (ENNReal.ofReal_mul (hf0 p.1)).symm
  simp_rw [hprod]
  exact lintegralRatio_toReal_eq_integralRatio μ ν _ _ hnum hden
    (Filter.Eventually.of_forall fun p => mul_nonneg (hf0 p.1) (hg0 p.2))
    (Filter.Eventually.of_forall fun p => hf0 p.1)

end Critical2DKPZ.NonGaussian

end
