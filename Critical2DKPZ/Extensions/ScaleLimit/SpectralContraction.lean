/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzPairingContinuity
public import Critical2DKPZ.Extensions.ScaleLimit.HilbertContraction
import Mathlib.Tactic

/-! # A contraction from spectral `L²` to random pairings -/

public section
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The angular Schwartz transform as a real continuous linear map. -/
def angularSchwartzCLM : SchwartzMap Plane ℝ →L[ℝ] SchwartzMap Plane ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Spectral.angularFrequencyEquiv).comp
    ((SchwartzMap.fourierTransformCLM ℝ).comp (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM))

@[simp] theorem angularSchwartzCLM_apply (f : SchwartzMap Plane ℝ) :
    angularSchwartzCLM f = angularSchwartz f := by
  ext ξ
  simp only [angularSchwartzCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.fourierTransformCLM_apply]
  rw [angularSchwartz_apply, fourierKPZ_eq_fourier]
  rfl

/-- The spectral realization of a real Schwartz test in complex `L²`. -/
def spectralLp {ν : Measure Plane} [ν.HasTemperateGrowth] :
    SchwartzMap Plane ℝ →L[ℝ] Lp ℂ 2 ν :=
  (SchwartzMap.toLpCLM ℝ ℂ 2 ν).comp angularSchwartzCLM

/-- Identification of the spectral realization as a random function of frequency. -/
theorem spectralLp_ae_eq {ν : Measure Plane} [ν.HasTemperateGrowth] (f : SchwartzMap Plane ℝ) :
    (spectralLp (ν := ν) f : Plane → ℂ) =ᵐ[ν] Spectral.fourierKPZ f := by
  have hh : spectralLp (ν := ν) f = (angularSchwartz f).toLp 2 ν := by
    simp only [spectralLp, ContinuousLinearMap.comp_apply, angularSchwartzCLM_apply,
      SchwartzMap.toLpCLM_apply]
  rw [hh]
  exact (SchwartzMap.coeFn_toLp (angularSchwartz f) 2 ν).trans
    (Filter.Eventually.of_forall (angularSchwartz_apply f))

/-- The square norm in `L²` is the integral of the squared pointwise norm. -/
theorem norm_Lp_two_sq {α F : Type*} [MeasurableSpace α] (μ : Measure α)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : Lp F 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => real_inner_self_eq_norm_sq (f x)))

/-- An isometric Schwartz pairing factors through a contraction on spectral `L²`.
This lets ordinary Banach-space calculus supply all band derivatives. -/
theorem exists_spectral_contraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure Plane) [ν.HasTemperateGrowth]
    (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : ∀ f g, (∫ ω, E f ω * E g ω ∂P) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν) :
    ∃ T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 P, ‖T‖ ≤ 1 ∧ ∀ f, T (spectralLp (ν := ν) f) = E f := by
  apply exists_hilbert_contraction E (spectralLp (ν := ν)).toLinearMap
  intro f
  have hsq : ‖E f‖ ^ 2 = ‖spectralLp (ν := ν) f‖ ^ 2 := by
    rw [norm_schwartzPairing_sq P ν E hE, norm_Lp_two_sq]
    exact integral_congr_ae ((spectralLp_ae_eq (ν := ν) f).mono (fun ξ hξ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hξ.symm))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq.le

end Critical2DKPZ.Extensions.ScaleLimit
