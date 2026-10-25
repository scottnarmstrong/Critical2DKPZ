/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

/-! # Translations and normalized band kernels in Schwartz space

The frequency cutoff is the radial bump with inner radius one and outer radius two.
The inverse Fourier transform uses the angular-frequency change of variables, so
its normalization agrees with `Spectral.fourierKPZ`.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Translation by `z`, with the convention `f(x-z)`. -/
def translateSchwartz (z : Plane) (f : SchwartzMap Plane ℝ) : SchwartzMap Plane ℝ :=
  SchwartzMap.compSubConstCLM ℝ z f

@[simp] theorem translateSchwartz_apply (z : Plane) (f : SchwartzMap Plane ℝ) (x : Plane) :
    translateSchwartz z f x = f (x - z) := rfl


/-- Successive translations add their displacement. -/
theorem translateSchwartz_add (z w : Plane) (f : SchwartzMap Plane ℝ) :
    translateSchwartz z (translateSchwartz w f) = translateSchwartz (z + w) f := by
  ext x
  simp only [translateSchwartz_apply]
  congr 1
  abel

/-- The fixed radial frequency cutoff, equal to one on the unit ball. -/
def chi : TestFn where
  toFun := (ContDiffBumpBase.ofInnerProductSpace Plane).toFun 2
  contDiff' := by
    have hc := (ContDiffBumpBase.ofInnerProductSpace Plane).smooth
    have hh : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Plane =>
        (ContDiffBumpBase.ofInnerProductSpace Plane).toFun 2 x) Set.univ :=
      hc.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨by norm_num, Set.mem_univ _⟩)
    exact contDiffOn_univ.mp hh
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) 2)
    intro x hx
    apply Metric.ball_subset_closedBall
    rwa [← (ContDiffBumpBase.ofInnerProductSpace Plane).support 2 (by norm_num)]
  tsupport_subset' := Set.subset_univ _

/-- The cutoff is specified by the explicit radial bump, rather than by an arbitrary bump choice. -/
theorem chi_apply (x : Plane) : chi x = Real.smoothTransition (2 - ‖x‖) := by
  norm_num [chi, ContDiffBumpBase.ofInnerProductSpace]

/-- Equal radii give equal cutoff values. -/
theorem chi_radial {x y : Plane} (hxy : ‖x‖ = ‖y‖) : chi x = chi y := by
  rw [chi_apply, chi_apply, hxy]

/-- The real band kernel: inverse angular Fourier transform of `chi`. -/
def zeta : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM
    (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      Spectral.angularFrequencyEquiv.symm (Spectral.testFnToSchwartzMap chi)))

/-- Spatial scaling by the inverse scale, as a continuous linear equivalence. -/
def inverseScaleEquiv (a : ℝ) (ha : a ≠ 0) : Plane ≃L[ℝ] Plane :=
  ContinuousLinearEquiv.ofHomothety
    (LinearEquiv.smulOfNeZero ℝ Plane a⁻¹ (inv_ne_zero ha)) |a⁻¹|
    (abs_pos.mpr (inv_ne_zero ha))
    (fun x => by simp [LinearEquiv.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs])

@[simp] theorem inverseScaleEquiv_apply (a : ℝ) (ha : a ≠ 0) (x : Plane) :
    inverseScaleEquiv a ha x = a⁻¹ • x := rfl

/-- The normalized scaled kernel `a⁻² ζ((x-y)/a)`. At zero scale the formula is zero. -/
def zetaScaled (a : ℝ) (y : Plane) : SchwartzMap Plane ℝ :=
  translateSchwartz y (if ha : a = 0 then 0 else
    a⁻¹ ^ 2 • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (inverseScaleEquiv a ha) zeta)

@[simp] theorem zetaScaled_apply (a : ℝ) (y x : Plane) :
    zetaScaled a y x = a⁻¹ ^ 2 * zeta (a⁻¹ • (x - y)) := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [zetaScaled]
  · simp only [zetaScaled, ha, dite_false, translateSchwartz_apply,
      smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, inverseScaleEquiv_apply, smul_eq_mul]

/-- Translating the kernel at the origin gives the kernel at any center. -/
theorem zetaScaled_eq_translate (a : ℝ) (y : Plane) :
    zetaScaled a y = translateSchwartz y (zetaScaled a 0) := by
  ext x
  simp

end Critical2DKPZ.Extensions.ScaleLimit
