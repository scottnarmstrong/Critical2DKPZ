/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.AngularFourier
import Mathlib.Tactic.Ring

/-!
# Continuity, uniform bounds and conjugation of the angular Fourier integral
-/

public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexConjugate RealInnerProductSpace

namespace Critical2DKPZ

open Analysis.Sobolev

theorem continuous_angularFourierIntegral {f : Plane → ℝ} (hf : Integrable f) :
    Continuous (angularFourierIntegral f) := by
  have hF := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (hf.ofReal (𝕜 := ℂ))
  have he : angularFourierIntegral f =
      (𝓕 (fun x => (f x : ℂ))) ∘ (fun ξ => (2 * Real.pi)⁻¹ • ξ) := by
    funext ξ
    exact angularFourierIntegral_eq_fourier f ξ
  rw [he]
  exact hF.comp ((continuous_id : Continuous (fun ξ : Plane => ξ)).const_smul ((2 * Real.pi)⁻¹ : ℝ))

/-- The angular Fourier integral is uniformly bounded by the L¹ norm of its input. -/
theorem norm_angularFourierIntegral_le (f : Plane → ℝ) (ξ : Plane) :
    ‖angularFourierIntegral f ξ‖ ≤ ∫ x : Plane, ‖f x‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Conjugation reverses the Fourier phase for real input. -/
theorem conj_angularFourierIntegral (f : Plane → ℝ) (ξ : Plane) :
    conj (angularFourierIntegral f ξ) =
      ∫ x : Plane, Complex.exp ((inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ) := by
  rw [angularFourierIntegral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_ofReal]
  congr 2
  push_cast
  ring

end Critical2DKPZ

end
