/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralRemainderCurve
import Mathlib.Tactic

/-! # Sharp L2 bounds for the high remainder and its radius derivative -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The derivative energy has exactly the high-frequency multiplier and the
factor `r^-2` dictated by radius differentiation. -/
theorem norm_bandHighRemainderDerivative_sq_le (hD : StationarySpectralData P D ν)
    (a : ℝ) (φ : TestFn) (x : Plane) {r : ℝ} (hr : 0 < r) :
    ‖bandHighRemainderDerivative hD a φ x r‖ ^ 2 ≤ r⁻¹ ^ 2 *
      ∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * radialSchwartzDerivative
        (schwartzFourier (Spectral.testFnToRealSchwartz φ)) (r • ξ)‖ ^ 2 ∂ν := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  let m := radialSchwartzDerivative (schwartzFourier (Spectral.testFnToRealSchwartz φ))
  let V := spectralMultipliedDilate ν (highFrequencyPhase a x) (measurable_highFrequencyPhase a x)
    (norm_highFrequencyPhase_le a x) m r
  have hn : ‖spectralPairingMap hD V‖ ≤ ‖V‖ := by
    calc
      _ ≤ ‖spectralPairingMap hD‖ * ‖V‖ := (spectralPairingMap hD).le_opNorm V
      _ ≤ 1 * ‖V‖ := mul_le_mul_of_nonneg_right (norm_spectralPairingMap_le hD) (norm_nonneg _)
      _ = _ := one_mul _
  calc
    _ = r⁻¹ ^ 2 * ‖spectralPairingMap hD V‖ ^ 2 := by
      change ‖r⁻¹ • spectralPairingMap hD V‖ ^ 2 = _
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ ≤ r⁻¹ ^ 2 * ‖V‖ ^ 2 := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn) (sq_nonneg _)
    _ = _ := by
      congr 1
      rw [norm_Lp_two_sq]
      apply integral_congr_ae
      filter_upwards [spectralMultipliedDilate_ae_eq ν (highFrequencyPhase a x)
        (measurable_highFrequencyPhase a x) (norm_highFrequencyPhase_le a x) m hr.ne'] with ξ hξ
      change ‖V ξ‖ ^ 2 = ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2
      rw [hξ]
      have heq : highFrequencyPhase a x ξ * m (r • ξ) =
          Complex.exp (-(Complex.I * (inner ℝ x ξ : ℂ))) *
            ((1 - (chi (a • ξ) : ℂ)) * m (r • ξ)) := by rw [highFrequencyPhase, mul_assoc]
      rw [heq, norm_mul, Complex.norm_exp]
      simp

/-- Uniform high-frequency bounds at all positive averaging radii, for all
sufficiently fine band widths. The constants precede both radii. -/
theorem high_remainder_raw_bounds (hD : StationarySpectralData P D ν)
    (φ : TestFn) (x : Plane) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ r : ℝ, 0 < r →
      ‖bandHighRemainder hD a φ x r‖ ^ 2 ≤ C * (a / r) ^ 2 * specMass ν a⁻¹ ∧
      ‖bandHighRemainderDerivative hD a φ x r‖ ^ 2 ≤
        C * r⁻¹ ^ 2 * (a / r) ^ 2 * specMass ν a⁻¹ := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  let m := schwartzFourier (Spectral.testFnToRealSchwartz φ)
  let m' := radialSchwartzDerivative m
  have hdec (ψ : SchwartzMap Plane ℂ) (ξ : Plane) :
      ‖ξ‖ * ‖ψ ξ‖ ≤ (SchwartzMap.seminorm ℝ 1 0) ψ := by
    simpa only [pow_one] using ψ.norm_pow_mul_le_seminorm ℝ 1 ξ
  obtain ⟨C₀, hC₀, h₀⟩ := high_band_energy_bound ν hD.ballAsymp m m.continuous
    (apply_nonneg _ m) (hdec m)
  obtain ⟨C₁, hC₁, h₁⟩ := high_band_energy_bound ν hD.ballAsymp m' m'.continuous
    (apply_nonneg _ m') (hdec m')
  let C := max C₀ C₁ + 1
  have hC : 0 < C := by dsimp [C]; linarith only [le_max_left C₀ C₁, hC₀]
  have h0C : C₀ ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num))
  have h1C : C₁ ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right (by norm_num))
  refine ⟨C, hC, ?_⟩
  filter_upwards [self_mem_nhdsWithin, h₀, h₁] with a ha h0 h1
  have ha' : 0 < a := ha
  intro r hr
  constructor
  · have heq : (∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * Spectral.fourierKPZ φ (r • ξ)‖ ^ 2 ∂ν) =
        ∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2 ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by dsimp only [m]; rw [schwartzFourier_apply]; rfl
    calc
      _ ≤ ∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2 ∂ν :=
        (norm_bandHighRemainder_sq_le hD φ x ha' hr).trans_eq heq
      _ ≤ C₀ * (a / r) ^ 2 * specMass ν a⁻¹ := (h0 r hr).2
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h0C (sq_nonneg _)) ENNReal.toReal_nonneg
  · calc
      _ ≤ r⁻¹ ^ 2 * (∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * m' (r • ξ)‖ ^ 2 ∂ν) :=
        norm_bandHighRemainderDerivative_sq_le hD a φ x hr
      _ ≤ r⁻¹ ^ 2 * (C₁ * (a / r) ^ 2 * specMass ν a⁻¹) :=
        mul_le_mul_of_nonneg_left (h1 r hr).2 (sq_nonneg _)
      _ ≤ r⁻¹ ^ 2 * (C * (a / r) ^ 2 * specMass ν a⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1C (sq_nonneg _)) ENNReal.toReal_nonneg) (sq_nonneg _)
      _ = _ := by ring

end Critical2DKPZ.Extensions.ScaleLimit
