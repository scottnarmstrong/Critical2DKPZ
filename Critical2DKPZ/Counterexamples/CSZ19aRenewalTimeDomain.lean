/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib.Tactic

/-! # Renewal parameters and Gaussian diffusion clocks

The renewal optimizer is evaluated inside the positive Gamma domain at `n = N = 2`, and the Gaussian comparison uses positive diffusion clocks. -/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata

open MeasureTheory Set DeltaBose

/-- At `A = c = sbar = 1`, `θ = 0` and `n = N = 2`, the optimizer equation holds with positive Gamma and logarithm arguments while the proposed bound fails. -/
theorem csz19a_11_strict_optimizer_counterexample :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < (2 : ℝ) / 2 ∧ Real.Gamma (1 * 1) > 0 ∧
    deriv (fun y : ℝ => Real.log (Real.Gamma y)) (1 * 1) =
      Real.log ((2 : ℝ) / 2) + 1 / 1 * 0 - Real.eulerMascheroniConstant ∧
    ¬ (1 : ℝ) ≤ 1 * 0 / 1 - Real.eulerMascheroniConstant := by
  have hΓ : Real.Gamma (1 : ℝ) ≠ 0 := by simp
  have hd := Real.hasDerivAt_Gamma_one.log hΓ
  have he : deriv (fun y : ℝ => Real.log (Real.Gamma y)) 1 = -Real.eulerMascheroniConstant := by
    simpa [Real.Gamma_one] using hd.deriv
  refine ⟨by norm_num, by norm_num, by simp, ?_, ?_⟩
  · simpa using he
  · have hγ := Real.one_half_lt_eulerMascheroniConstant
    norm_num only [mul_zero, zero_div, zero_sub]
    linarith

/-- At `d = 2`, `c = t = 1`, `θ = 2` and `w = 0`, the two positive-time Gaussian factors differ. -/
theorem csz19a_16_positive_clock_factors_differ :
    heatKernel ((1 : ℝ) * 2) (0 : Plane) ≠ heatKernel ((1 : ℝ) * 1) 0 := by
  simp only [one_mul, heatKernel_at_zero]
  intro he
  have hh := congrArg (fun x : ℝ => x⁻¹) he
  simp only [inv_inv] at hh
  nlinarith [Real.pi_pos]

/-- The tilted Dickman integrand at unit time.
The integration domain is `s > 0`, where Gamma is strictly positive. -/
def csz19aUnitTilt (θ s : ℝ) : ℝ :=
  Real.exp (θ * s) * (Real.exp (-Real.eulerMascheroniConstant * s) / Real.Gamma s)

/-- Agreement with the unit-time tilted Dickman density formula on its
printed domain `s > 0`; the Gamma denominator is strictly positive. -/
theorem csz19aUnitTilt_eq_source (θ s : ℝ) (hs : 0 < s) :
    csz19aUnitTilt θ s = Real.exp (θ * s) *
      (s * (1 : ℝ) ^ (s - 1) * Real.exp (-Real.eulerMascheroniConstant * s) /
        Real.Gamma (s + 1)) := by
  rw [Real.one_rpow, Real.Gamma_add_one hs.ne']
  dsimp [csz19aUnitTilt]
  field_simp [hs.ne', (Real.Gamma_pos_of_pos hs).ne']

private theorem csz19aUnitTilt_eq (θ : ℝ) :
    csz19aUnitTilt θ = gammaLaplaceIntegrand (θ - Real.eulerMascheroniConstant) := by
  funext s
  dsimp [csz19aUnitTilt, gammaLaplaceIntegrand]
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Absolute convergence of the scalar and spatial source integrals used below. -/
theorem csz19a_16_unit_integrable (θ : ℝ) (c : ℝ) (w : Plane) :
    IntegrableOn (csz19aUnitTilt θ) (Ioi 0) ∧
    IntegrableOn (fun s => csz19aUnitTilt θ s * heatKernel c w) (Ioi 0) := by
  have h : IntegrableOn (csz19aUnitTilt θ) (Ioi 0) := by
    rw [csz19aUnitTilt_eq]
    exact integrableOn_gammaLaplaceIntegrand _
  exact ⟨h, h.mul_const _⟩

/-- At unit time, the spatial renewal potential factors with Gaussian clock `c`, independently of the tilt. -/
theorem csz19a_16_corrected_unit_factorization (θ c : ℝ) (_hc : 0 < c) (w : Plane) :
    (∫ s in Ioi (0 : ℝ), csz19aUnitTilt θ s * heatKernel (c * 1) w) =
      (∫ s in Ioi (0 : ℝ), csz19aUnitTilt θ s) * heatKernel (c * 1) w := by
  exact integral_mul_const _ _

/-- At `d = 2`, `θ = 2`, `c = t = 1` and `w = 0`, the two potential integrals differ, with absolute convergence supplied by `csz19a_16_unit_integrable`. -/
theorem csz19a_16_strict_unit_counterexample :
    (∫ s in Ioi (0 : ℝ), csz19aUnitTilt 2 s * heatKernel (1 * 1) 0) ≠
      (∫ s in Ioi (0 : ℝ), csz19aUnitTilt 2 s) * heatKernel (1 * 2) 0 := by
  have hpos : 0 < ∫ s in Ioi (0 : ℝ), csz19aUnitTilt 2 s := by
    rw [csz19aUnitTilt_eq]
    have h := scalarDensity_pos (2 - Real.eulerMascheroniConstant)
      (show (0 : ℝ) < 1 by norm_num)
    simpa [scalarDensity_eq_laplace, Real.log_one] using h
  rw [csz19a_16_corrected_unit_factorization 2 1 (by norm_num)]
  exact fun he => csz19a_16_positive_clock_factors_differ
    ((mul_left_cancel₀ hpos.ne' he).symm)

end Critical2DKPZ.Errata
