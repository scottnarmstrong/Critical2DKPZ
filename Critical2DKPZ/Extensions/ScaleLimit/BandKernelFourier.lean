/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzTranslate
import Critical2DKPZ.Spectral.BochnerSchwartzSquareCone
import Mathlib.Tactic

/-! # Fourier identities for the radial band kernel -/

public section
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The cutoff is even. -/
@[simp] theorem chi_neg (x : Plane) : chi (-x) = chi x :=
  chi_radial (norm_neg x)

/-- The cutoff lies between zero and one. -/
theorem chi_bounds (x : Plane) : 0 ≤ chi x ∧ chi x ≤ 1 :=
  (ContDiffBumpBase.ofInnerProductSpace Plane).mem_Icc 2 x

/-- The cutoff equals one on the closed unit ball. -/
theorem chi_eq_one {x : Plane} (hx : ‖x‖ ≤ 1) : chi x = 1 := by
  exact (ContDiffBumpBase.ofInnerProductSpace Plane).eq_one 2 (by norm_num) x hx

/-- The cutoff vanishes outside the open ball of radius two. -/
theorem chi_eq_zero {x : Plane} (hx : 2 ≤ ‖x‖) : chi x = 0 := by
  rw [chi_apply]
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The angular transform is Mathlib's transform evaluated at rescaled frequency. -/
theorem fourierKPZ_eq_fourier (f : Plane → ℝ) (ξ : Plane) :
    Spectral.fourierKPZ f ξ =
      𝓕 (fun x => (f x : ℂ)) (Spectral.angularFrequencyEquiv ξ) := by
  rw [Spectral.fourierKPZ, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  change Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ))) * (f x : ℂ) =
    Complex.exp ((-2 * Real.pi * inner ℝ x ((2 * Real.pi)⁻¹ • ξ) : ℝ) * Complex.I) • (f x : ℂ)
  rw [real_inner_smul_right, smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- The real kernel has precisely the author-specified angular Fourier transform. -/
theorem fourierKPZ_zeta (ξ : Plane) : Spectral.fourierKPZ zeta ξ = (chi ξ : ℂ) := by
  let H : SchwartzMap Plane ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    Spectral.angularFrequencyEquiv.symm (Spectral.testFnToSchwartzMap chi)
  let G : SchwartzMap Plane ℂ := 𝓕⁻ H
  have hreal : Spectral.conjugateSchwartz G = G := by
    have hF : 𝓕 (Spectral.conjugateSchwartz G) = 𝓕 G := by
      ext x
      rw [Spectral.fourier_conjugateSchwartz_apply]
      have hFG : 𝓕 G = H := by dsimp [G]; simp
      rw [hFG]
      simp [H, map_neg, chi_neg]
    have hi := congrArg (fun f : SchwartzMap Plane ℂ => 𝓕⁻ f) hF
    simpa using hi
  have hz : SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM zeta = G := by
    ext x
    have hr : conj (G x) = G x := congrArg (fun f : SchwartzMap Plane ℂ => f x) hreal
    change ((G x).re : ℂ) = G x
    exact Complex.conj_eq_iff_re.mp hr
  rw [fourierKPZ_eq_fourier]
  change 𝓕 (fun x => (zeta x : ℂ)) (Spectral.angularFrequencyEquiv ξ) = _
  change 𝓕 (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM zeta)
    (Spectral.angularFrequencyEquiv ξ) = _
  rw [hz]
  have hFG : 𝓕 G = H := by dsimp [G]; simp
  rw [hFG]
  simp [H]

/-- Translating a real function multiplies its transform by the angular phase. -/
theorem fourierKPZ_translate (f : SchwartzMap Plane ℝ) (y ξ : Plane) :
    Spectral.fourierKPZ (translateSchwartz y f) ξ =
      Complex.exp (-(Complex.I * (inner ℝ y ξ : ℂ))) * Spectral.fourierKPZ f ξ := by
  unfold Spectral.fourierKPZ
  rw [← integral_add_right_eq_self _ y, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [translateSchwartz_apply, add_sub_cancel_right, inner_add_left, Complex.ofReal_add]
  rw [mul_add, neg_add, Complex.exp_add]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
