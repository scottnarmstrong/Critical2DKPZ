/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.AngularFourierBasic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The KPZ Fourier convention -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

namespace Critical2DKPZ.Spectral

/-- The paper's Fourier transform, with angular frequency and no `2π` in the phase. -/
def fourierKPZ (f : Plane → ℝ) (ξ : Plane) : ℂ :=
  ∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * (f x : ℂ)

/-- The paper’s Fourier transform agrees with the angular Fourier integral on test functions. -/
theorem fourierKPZ_eq_angularFourierIntegral (f : TestFn) (ξ : Plane) :
    fourierKPZ (f : Plane → ℝ) ξ = Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral f ξ := by
  unfold fourierKPZ Critical2DKPZ.Analysis.Sobolev.angularFourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  rw [real_inner_comm x ξ]
  push_cast
  ring

/-- Composing a test function with a plane isometry composes its paper-normalized Fourier
transform with the same isometry. -/
theorem fourierKPZ_comp_linearIsometryEquiv (f : TestFn)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (ξ : Plane) :
    fourierKPZ (fun x : Plane => f (R x)) ξ = fourierKPZ f (R ξ) := by
  unfold fourierKPZ
  let g : Plane → ℂ := fun x =>
    Complex.exp (-(Complex.I * (inner ℝ x (R ξ) : ℝ))) * (f x : ℂ)
  have hphase (x : Plane) :
      inner ℝ (R x) (R ξ) = inner ℝ x ξ := by
    rw [LinearIsometryEquiv.inner_map_eq_flip]
    simp
  calc
    (∫ x : Plane,
      Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * (f (R x) : ℂ)) =
      ∫ x : Plane, g (R x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g]
        rw [← hphase x]
    _ = ∫ x : Plane, g x :=
      (LinearIsometryEquiv.measurePreserving R).integral_comp' (f := R.toMeasurableEquiv) g
    _ = ∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x (R ξ) : ℝ))) * (f x : ℂ) := rfl

/-- The norm of a smooth compactly supported test function is integrable. This supplies the
integrability required for the Fourier-transform norm bound below. -/
theorem integrable_norm_testFn (f : TestFn) : Integrable (fun x : Plane => ‖f x‖) := by
  exact f.continuous.norm.integrable_of_hasCompactSupport f.hasCompactSupport.norm

/-- The KPZ Fourier transform is bounded by the test function's `L¹` norm; that integral is finite
by `integrable_norm_testFn`. -/
theorem norm_fourierKPZ_le (f : TestFn) (ξ : Plane) :
    ‖fourierKPZ (f : Plane → ℝ) ξ‖ ≤ ∫ x : Plane, ‖f x‖ := by
  rw [fourierKPZ_eq_angularFourierIntegral]
  exact Critical2DKPZ.norm_angularFourierIntegral_le f ξ

/-- Conjugating the KPZ Fourier transform reverses the Fourier phase. -/
theorem conj_fourierKPZ (f : TestFn) (ξ : Plane) :
    conj (fourierKPZ (f : Plane → ℝ) ξ) =
      ∫ x : Plane, Complex.exp ((inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ) := by
  rw [fourierKPZ_eq_angularFourierIntegral]
  exact Critical2DKPZ.conj_angularFourierIntegral f ξ

end Critical2DKPZ.Spectral

end
