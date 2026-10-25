/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandKernelFourier
public import Critical2DKPZ.Extensions.ScaleLimit.SpectralGrowth
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Continuity of Schwartz random pairings under spatial translation -/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The spectral hypothesis gives polynomial growth, hence a tempered measure. -/
theorem temperateGrowth_of_spectralData {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) : ν.HasTemperateGrowth := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  obtain ⟨C, hC, hbound⟩ := specMass_loglog_bound ν hD.locFin hD.ballAsymp
  apply Spectral.measure_hasTemperateGrowth_of_polynomial_ball_growth ν
  refine ⟨C + specMass ν 2, 1, fun R hR => ?_⟩
  rw [pow_one]
  have hN : 0 ≤ specMass ν 2 := ENNReal.toReal_nonneg
  by_cases hR2 : 2 ≤ R
  · have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
    have hll := Real.log_le_sub_one_of_pos hlogR
    have hl := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hR)
    have hlin : 1 + Real.log (Real.log R) ≤ R := by linarith
    calc
      specMass ν R ≤ C * (1 + Real.log (Real.log R)) := hbound R hR2
      _ ≤ C * R := mul_le_mul_of_nonneg_left hlin hC
      _ ≤ (C + specMass ν 2) * R := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN) (by linarith)
  · have hmono := specMass_mono ν (le_of_not_ge hR2)
    calc
      specMass ν R ≤ specMass ν 2 := hmono
      _ ≤ specMass ν 2 * R := le_mul_of_one_le_right hN hR
      _ ≤ (C + specMass ν 2) * R := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by linarith)

/-- The angular Fourier transform of a real Schwartz function, as a Schwartz function. -/
def angularSchwartz (f : SchwartzMap Plane ℝ) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Spectral.angularFrequencyEquiv
    (𝓕 (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM f))

@[simp] theorem angularSchwartz_apply (f : SchwartzMap Plane ℝ) (ξ : Plane) :
    angularSchwartz f ξ = Spectral.fourierKPZ f ξ := (fourierKPZ_eq_fourier f ξ).symm

/-- The isometry identifies the square of the random pairing norm with spectral energy. -/
theorem norm_schwartzPairing_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Measure Plane) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : ∀ f g, (∫ ω, E f ω * E g ω ∂P) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν)
    (f : SchwartzMap Plane ℝ) : ‖E f‖ ^ 2 = ∫ ξ, ‖Spectral.fourierKPZ f ξ‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  change (∫ ω, E f ω * E f ω ∂P) = _
  rw [hE]
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ f ξ)).re = _
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- The square spectral norm of every Schwartz transform is integrable. -/
theorem integrable_sq_fourierKPZ_schwartz (ν : Measure Plane) [ν.HasTemperateGrowth]
    (f : SchwartzMap Plane ℝ) : Integrable (fun ξ => ‖Spectral.fourierKPZ f ξ‖ ^ 2) ν := by
  have hi := ((angularSchwartz f).memLp 2 ν).integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, angularSchwartz_apply] using hi

/-- The angular transform is linear over real scalars, in particular under subtraction. -/
theorem fourierKPZ_sub_schwartz (f g : SchwartzMap Plane ℝ) (ξ : Plane) :
    Spectral.fourierKPZ (f - g : SchwartzMap Plane ℝ) ξ = Spectral.fourierKPZ f ξ - Spectral.fourierKPZ g ξ := by
  rw [← angularSchwartz_apply (f - g), ← angularSchwartz_apply f, ← angularSchwartz_apply g]
  have heq : angularSchwartz (f - g) = angularSchwartz f - angularSchwartz g := by
    simp only [angularSchwartz, map_sub]
    change SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Spectral.angularFrequencyEquiv
      (SchwartzMap.fourierTransformCLM ℂ (_ - _)) = _
    rw [map_sub, map_sub]
    simp only [SchwartzMap.fourierTransformCLM_apply]
  rw [heq]
  rfl

/-- Every isometric Schwartz extension is continuous in `L²` under translations. -/
theorem continuous_schwartzPairing_translate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure Plane) [ν.HasTemperateGrowth]
    (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : ∀ f g, (∫ ω, E f ω * E g ω ∂P) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν)
    (ψ : SchwartzMap Plane ℝ) : Continuous (fun y => E (translateSchwartz y ψ)) := by
  apply continuous_iff_continuousAt.mpr
  intro y₀
  let W : Plane → ℝ := fun ξ => 4 * ‖Spectral.fourierKPZ ψ ξ‖ ^ 2
  let V : Plane → Plane → ℝ := fun y ξ =>
    ‖Spectral.fourierKPZ (translateSchwartz y ψ) ξ -
      Spectral.fourierKPZ (translateSchwartz y₀ ψ) ξ‖ ^ 2
  have hVm (y : Plane) : AEStronglyMeasurable (V y) ν := by
    have hc := ((angularSchwartz (translateSchwartz y ψ)).continuous.sub
      (angularSchwartz (translateSchwartz y₀ ψ)).continuous).norm.pow 2
    have hm := hc.aestronglyMeasurable (μ := ν)
    convert hm using 1
    funext ξ
    simp only [V, Pi.pow_apply, Pi.sub_apply, angularSchwartz_apply]
  have hW : Integrable W ν := (integrable_sq_fourierKPZ_schwartz ν ψ).const_mul 4
  have hphase (y ξ : Plane) :
      ‖Complex.exp (-(Complex.I * (inner ℝ y ξ : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hbound (y ξ : Plane) : ‖V y ξ‖ ≤ W ξ := by
    dsimp [V, W]
    rw [abs_of_nonneg (sq_nonneg _)]
    rw [fourierKPZ_translate, fourierKPZ_translate]
    have hh := norm_sub_le (Complex.exp (-(Complex.I * (inner ℝ y ξ : ℂ))) * Spectral.fourierKPZ ψ ξ)
      (Complex.exp (-(Complex.I * (inner ℝ y₀ ξ : ℂ))) * Spectral.fourierKPZ ψ ξ)
    simp only [norm_mul, hphase, one_mul] at hh
    nlinarith only [hh, norm_nonneg (Spectral.fourierKPZ ψ ξ),
      norm_nonneg (Complex.exp (-(Complex.I * (inner ℝ y ξ : ℂ))) * Spectral.fourierKPZ ψ ξ -
        Complex.exp (-(Complex.I * (inner ℝ y₀ ξ : ℂ))) * Spectral.fourierKPZ ψ ξ)]
  have hlim (ξ : Plane) : Tendsto (fun y => V y ξ) (𝓝 y₀) (𝓝 0) := by
    have hc : Continuous (fun y : Plane => Complex.exp (-(Complex.I * (inner ℝ y ξ : ℂ))) *
        Spectral.fourierKPZ ψ ξ) := by fun_prop
    simpa only [V, fourierKPZ_translate, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((hc.continuousAt (x := y₀)).tendsto.sub_const
        (Complex.exp (-(Complex.I * (inner ℝ y₀ ξ : ℂ))) * Spectral.fourierKPZ ψ ξ)).norm.pow 2
  have hi := tendsto_integral_filter_of_dominated_convergence W
    (Eventually.of_forall hVm) (Eventually.of_forall (fun y => Eventually.of_forall (hbound y)))
    hW (Eventually.of_forall hlim)
  have hsq : Tendsto (fun y => ‖E (translateSchwartz y ψ) - E (translateSchwartz y₀ ψ)‖ ^ 2)
      (𝓝 y₀) (𝓝 0) := by
    have heq (y : Plane) : ‖E (translateSchwartz y ψ) - E (translateSchwartz y₀ ψ)‖ ^ 2 =
        ∫ ξ, V y ξ ∂ν := by
      rw [← map_sub, norm_schwartzPairing_sq P ν E hE]
      congr 1
      funext ξ
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (fourierKPZ_sub_schwartz _ _ ξ)
    simpa only [heq, integral_zero] using hi
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hz : Tendsto (fun y => ‖E (translateSchwartz y ψ) - E (translateSchwartz y₀ ψ)‖)
      (𝓝 y₀) (𝓝 0) := by
    change Tendsto (fun y => Real.sqrt (‖E (translateSchwartz y ψ) - E (translateSchwartz y₀ ψ)‖ ^ 2))
      (𝓝 y₀) (𝓝 (Real.sqrt 0)) at hn
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hz

end Critical2DKPZ.Extensions.ScaleLimit
