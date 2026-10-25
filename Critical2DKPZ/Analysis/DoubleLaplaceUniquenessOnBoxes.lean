/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.DoubleLaplaceUniqueness
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-! # Local uniqueness of the double Laplace transform -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.Analysis

/-- Nonnegative densities on the positive quadrant are determined by their double Laplace transform on an open rectangle of rates. -/
theorem ae_eq_of_bivariate_laplace_eq_on_boxes {rate₁ rate₂ ε : ℝ}
    (hε : 0 < ε)
    {F G : Plane → ℝ}
    (hFm : AEMeasurable F (volume.restrict positiveQuadrant))
    (hGm : AEMeasurable G (volume.restrict positiveQuadrant))
    (hF0 : ∀ᵐ x ∂(volume.restrict positiveQuadrant), 0 ≤ F x)
    (hG0 : ∀ᵐ x ∂(volume.restrict positiveQuadrant), 0 ≤ G x)
    (hFint : ∀ rateA rateB : ℝ, rateA ∈ Ioo (rate₁ - ε) (rate₁ + ε) →
      rateB ∈ Ioo (rate₂ - ε) (rate₂ + ε) →
      Integrable (fun x : Plane => Real.exp (-(rateA * x 0 + rateB * x 1)) * F x)
        (volume.restrict positiveQuadrant))
    (hGint : ∀ rateA rateB : ℝ, rateA ∈ Ioo (rate₁ - ε) (rate₁ + ε) →
      rateB ∈ Ioo (rate₂ - ε) (rate₂ + ε) →
      Integrable (fun x : Plane => Real.exp (-(rateA * x 0 + rateB * x 1)) * G x)
        (volume.restrict positiveQuadrant))
    (hLap : ∀ rateA rateB : ℝ, rateA ∈ Ioo (rate₁ - ε) (rate₁ + ε) →
      rateB ∈ Ioo (rate₂ - ε) (rate₂ + ε) →
      (∫ x : Plane, Real.exp (-(rateA * x 0 + rateB * x 1)) * F x
          ∂(volume.restrict positiveQuadrant)) =
        ∫ x : Plane, Real.exp (-(rateA * x 0 + rateB * x 1)) * G x
          ∂(volume.restrict positiveQuadrant)) :
    F =ᵐ[volume.restrict positiveQuadrant] G := by
  let μ₀ : Measure Plane := volume.restrict positiveQuadrant
  let ρF : Plane → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * F x)
  let ρG : Plane → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * G x)
  let νF : Measure Plane := μ₀.withDensity ρF
  let νG : Measure Plane := μ₀.withDensity ρG
  have hr₁ : rate₁ ∈ Ioo (rate₁ - ε) (rate₁ + ε) := by simp [hε]
  have hr₂ : rate₂ ∈ Ioo (rate₂ - ε) (rate₂ + ε) := by simp [hε]
  have hExp : AEMeasurable
      (fun x : Plane => Real.exp (-(rate₁ * x 0 + rate₂ * x 1))) μ₀ := by
    fun_prop
  have hρF : AEMeasurable ρF μ₀ := by
    exact (hExp.mul hFm).ennreal_ofReal
  have hρG : AEMeasurable ρG μ₀ := by
    exact (hExp.mul hGm).ennreal_ofReal
  have hρFtop : ∀ᵐ x ∂μ₀, ρF x < ⊤ := by
    filter_upwards [] with x
    simp only [ρF, ENNReal.ofReal_lt_top]
  have hρGtop : ∀ᵐ x ∂μ₀, ρG x < ⊤ := by
    filter_upwards [] with x
    simp only [ρG, ENNReal.ofReal_lt_top]
  have hBaseF : Integrable
      (fun x : Plane => Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * F x) μ₀ :=
    hFint rate₁ rate₂ hr₁ hr₂
  have hBaseG : Integrable
      (fun x : Plane => Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * G x) μ₀ :=
    hGint rate₁ rate₂ hr₁ hr₂
  have hνFfinite : IsFiniteMeasure νF := by
    dsimp [νF, ρF, μ₀]
    exact isFiniteMeasure_withDensity_ofReal hBaseF.2
  have hνGfinite : IsFiniteMeasure νG := by
    dsimp [νG, ρG, μ₀]
    exact isFiniteMeasure_withDensity_ofReal hBaseG.2
  have hF0' : ∀ᵐ x ∂μ₀, 0 ≤ F x := hF0
  have hG0' : ∀ᵐ x ∂μ₀, 0 ≤ G x := hG0
  have hρFto (x : Plane) (hx : 0 ≤ F x) :
      (ρF x).toReal = Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * F x := by
    change (ENNReal.ofReal (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * F x)).toReal = _
    exact ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hx)
  have hρGto (x : Plane) (hx : 0 ≤ G x) :
      (ρG x).toReal = Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * G x := by
    change (ENNReal.ofReal (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * G x)).toReal = _
    exact ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hx)
  have hTiltF (r s : ℝ) (hr : r ∈ Ioo (-ε) ε) (hs : s ∈ Ioo (-ε) ε) :
      (fun x : Plane => Real.exp (-((rate₁ - r) * x 0 + (rate₂ - s) * x 1)) * F x) =ᵐ[μ₀]
        fun x => (ρF x).toReal * Real.exp (r * x 0 + s * x 1) := by
    filter_upwards [hF0'] with x hx
    have he : -((rate₁ - r) * x 0 + (rate₂ - s) * x 1) =
        -(rate₁ * x 0 + rate₂ * x 1) + (r * x 0 + s * x 1) := by ring
    calc
      Real.exp (-((rate₁ - r) * x 0 + (rate₂ - s) * x 1)) * F x =
          Real.exp (-(rate₁ * x 0 + rate₂ * x 1) + (r * x 0 + s * x 1)) * F x := by
            rw [he]
      _ = (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) *
            Real.exp (r * x 0 + s * x 1)) * F x := by rw [Real.exp_add]
      _ = (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * F x) *
            Real.exp (r * x 0 + s * x 1) := by ring
      _ = (ρF x).toReal * Real.exp (r * x 0 + s * x 1) := by
            rw [← hρFto x hx]
  have hTiltG (r s : ℝ) (hr : r ∈ Ioo (-ε) ε) (hs : s ∈ Ioo (-ε) ε) :
      (fun x : Plane => Real.exp (-((rate₁ - r) * x 0 + (rate₂ - s) * x 1)) * G x) =ᵐ[μ₀]
        fun x => (ρG x).toReal * Real.exp (r * x 0 + s * x 1) := by
    filter_upwards [hG0'] with x hx
    have he : -((rate₁ - r) * x 0 + (rate₂ - s) * x 1) =
        -(rate₁ * x 0 + rate₂ * x 1) + (r * x 0 + s * x 1) := by ring
    calc
      Real.exp (-((rate₁ - r) * x 0 + (rate₂ - s) * x 1)) * G x =
          Real.exp (-(rate₁ * x 0 + rate₂ * x 1) + (r * x 0 + s * x 1)) * G x := by
            rw [he]
      _ = (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) *
            Real.exp (r * x 0 + s * x 1)) * G x := by rw [Real.exp_add]
      _ = (Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * G x) *
            Real.exp (r * x 0 + s * x 1) := by ring
      _ = (ρG x).toReal * Real.exp (r * x 0 + s * x 1) := by
            rw [← hρGto x hx]
  have hRate₁ (r : ℝ) (hr : r ∈ Ioo (-ε) ε) :
      rate₁ - r ∈ Ioo (rate₁ - ε) (rate₁ + ε) := by
    rcases hr with ⟨hrl, hru⟩
    constructor <;> linarith
  have hRate₂ (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      rate₂ - s ∈ Ioo (rate₂ - ε) (rate₂ + ε) := by
    rcases hs with ⟨hsl, hsu⟩
    constructor <;> linarith
  have hIntF (r s : ℝ) (hr : r ∈ Ioo (-ε) ε) (hs : s ∈ Ioo (-ε) ε) :
      Integrable (fun x : Plane => Real.exp (r * x 0 + s * x 1)) νF := by
    rw [integrable_withDensity_iff_integrable_smul₀' hρF hρFtop]
    have h := hFint (rate₁ - r) (rate₂ - s) (hRate₁ r hr) (hRate₂ s hs)
    simpa only [smul_eq_mul] using h.congr (hTiltF r s hr hs)
  have hIntG (r s : ℝ) (hr : r ∈ Ioo (-ε) ε) (hs : s ∈ Ioo (-ε) ε) :
      Integrable (fun x : Plane => Real.exp (r * x 0 + s * x 1)) νG := by
    rw [integrable_withDensity_iff_integrable_smul₀' hρG hρGtop]
    have h := hGint (rate₁ - r) (rate₂ - s) (hRate₁ r hr) (hRate₂ s hs)
    simpa only [smul_eq_mul] using h.congr (hTiltG r s hr hs)
  have hMGF (r s : ℝ) (hr : r ∈ Ioo (-ε) ε) (hs : s ∈ Ioo (-ε) ε) :
      (∫ x : Plane, Real.exp (r * x 0 + s * x 1) ∂νF) =
        ∫ x : Plane, Real.exp (r * x 0 + s * x 1) ∂νG := by
    have hIF := integral_withDensity_eq_integral_toReal_smul₀ hρF hρFtop
      (fun x : Plane => Real.exp (r * x 0 + s * x 1))
    have hIG := integral_withDensity_eq_integral_toReal_smul₀ hρG hρGtop
      (fun x : Plane => Real.exp (r * x 0 + s * x 1))
    calc
      (∫ x : Plane, Real.exp (r * x 0 + s * x 1) ∂νF) =
          ∫ x : Plane, (ρF x).toReal * Real.exp (r * x 0 + s * x 1) ∂μ₀ := by
            simpa only [smul_eq_mul] using hIF
      _ = ∫ x : Plane,
          Real.exp (-((rate₁ - r) * x 0 + (rate₂ - s) * x 1)) * F x ∂μ₀ := by
            apply integral_congr_ae
            filter_upwards [hTiltF r s hr hs] with x hx
            exact hx.symm
      _ = ∫ x : Plane,
          Real.exp (-((rate₁ - r) * x 0 + (rate₂ - s) * x 1)) * G x ∂μ₀ :=
            hLap (rate₁ - r) (rate₂ - s) (hRate₁ r hr) (hRate₂ s hs)
      _ = ∫ x : Plane, (ρG x).toReal * Real.exp (r * x 0 + s * x 1) ∂μ₀ := by
            apply integral_congr_ae
            filter_upwards [hTiltG r s hr hs] with x hx
            exact hx
      _ = ∫ x : Plane, Real.exp (r * x 0 + s * x 1) ∂νG := by
            simpa only [smul_eq_mul, mul_comm] using hIG.symm
  have hmeas := @measure_eq_of_bivariate_mgf_eq_on_Ioo νF νG hνFfinite hνGfinite
    ε hε hIntF hIntG hMGF
  have hρeq : ρF =ᵐ[μ₀] ρG :=
    (withDensity_eq_iff_of_sigmaFinite hρF hρG).mp (by simpa only [νF, νG] using hmeas)
  filter_upwards [hρeq, hF0', hG0'] with x hρ hx hy
  have hreal := congrArg ENNReal.toReal (by simpa only [ρF, ρG] using hρ)
  have hreal' : Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * F x =
      Real.exp (-(rate₁ * x 0 + rate₂ * x 1)) * G x := by
    simpa only [ENNReal.toReal_ofReal
      (mul_nonneg (Real.exp_pos _).le hx), ENNReal.toReal_ofReal
      (mul_nonneg (Real.exp_pos _).le hy)] using hreal
  exact mul_left_cancel₀ (Real.exp_ne_zero _) hreal'

end Critical2DKPZ.Analysis

end
