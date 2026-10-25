/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralShape
public import Critical2DKPZ.Extensions.ScaleLimit.ShapeDilation
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzRandomPairing
public import Critical2DKPZ.Extensions.ScaleLimit.WidthClock
import Critical2DKPZ.Extensions.ScaleLimit.SchwartzFourierTranslation
import Mathlib.Analysis.Complex.Basic

/-! # Shape comparison for the stochastic Schwartz extension -/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The extension's square moment is the angular Fourier energy. -/
theorem schwartzExt_integral_sq (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) :
    (∫ ω, schwartzExt hD ψ ω ^ 2 ∂P) = ∫ ξ, ‖Spectral.fourierKPZ ψ ξ‖ ^ 2 ∂ν := by
  have hh := schwartzExt_covariance hD ψ ψ
  simp only [← pow_two] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (Spectral.fourierKPZ ψ ξ * starRingEnd ℂ (Spectral.fourierKPZ ψ ξ)).re = _
  rw [Complex.mul_conj']
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Translations do not change square moments of a Schwartz pairing. -/
theorem schwartzExt_translate_integral_sq (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (x : Plane) :
    (∫ ω, schwartzExt hD (translateSchwartz x ψ) ω ^ 2 ∂P) =
      ∫ ξ, ‖Spectral.fourierKPZ ψ ξ‖ ^ 2 ∂ν := by
  rw [schwartzExt_integral_sq]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [fourierKPZ_translateSchwartz, norm_mul, norm_translation_phase, one_mul]


/-- The deterministic shape lemma transfers directly to the selected L2 extension. -/
theorem schwartzExt_shape_comparison (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (hψ : schwartzFourier ψ 0 = 0) (x : Plane) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      (∫ ω, schwartzExt hD (translateSchwartz x (shapeDilate ε ε.property.ne' ψ)) ω ^ 2 ∂P) /
        Real.log (Real.log (ε : ℝ)⁻¹))
      (comap Subtype.val (𝓝[>] 0)) (𝓝 0) := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  have hs := (shape_comparison ν hD.ballAsymp (schwartzFourier ψ) hψ).comp
    (tendsto_comap : Tendsto (Subtype.val : {ε : ℝ // 0 < ε} → ℝ)
      (comap Subtype.val (𝓝[>] 0)) (𝓝[>] 0))
  apply hs.congr
  intro ε
  have heq : (∫ ω, schwartzExt hD
      (translateSchwartz x (shapeDilate ε ε.property.ne' ψ)) ω ^ 2 ∂P) =
      ∫ ξ, ‖schwartzFourier ψ ((ε : ℝ) • ξ)‖ ^ 2 ∂ν := by
    rw [schwartzExt_translate_integral_sq]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [fourierKPZ_shapeDilate ψ ε.property, schwartzFourier_apply]
  exact congrArg (fun v : ℝ => v / Real.log (Real.log (ε : ℝ)⁻¹)) heq.symm

/-- At the canonical scale, a zero-frequency shape has vanishing normalized
second moment. This is stated entirely in the L² stochastic Schwartz extension. -/
theorem schwartzExt_shape_at_scaleRadius (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (hψ : schwartzFourier ψ 0 = 0) (x : Plane)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ *
      ∫ ω, schwartzExt hD (translateSchwartz x
        (shapeDilate (scaleRadius L s) (scaleRadius_pos L s).ne' ψ)) ω ^ 2 ∂P)
      atTop (𝓝 0) := by
  let ε : Set.Ioi (0 : ℝ) → {ε : ℝ // 0 < ε} :=
    fun L => ⟨scaleRadius L s, scaleRadius_pos L s⟩
  have hε : Tendsto ε atTop (comap Subtype.val (𝓝[>] 0)) := by
    apply tendsto_comap_iff.mpr
    exact tendsto_nhdsWithin_iff.mpr ⟨scaleRadius_tendsto_zero hs,
      Eventually.of_forall fun L => scaleRadius_pos L s⟩
  have hh := ((schwartzExt_shape_comparison hD ψ hψ x).comp hε).const_mul s
  have hh' : Tendsto (fun L : Set.Ioi (0 : ℝ) => s *
      ((∫ ω, schwartzExt hD (translateSchwartz x
        (shapeDilate (scaleRadius L s) (scaleRadius_pos L s).ne' ψ)) ω ^ 2 ∂P) /
          Real.log (Real.log (scaleRadius L s)⁻¹))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hh
  apply hh'.congr
  intro L
  rw [log_log_inv_scaleRadius]
  field_simp [hs.ne']

end Critical2DKPZ.Extensions.ScaleLimit
