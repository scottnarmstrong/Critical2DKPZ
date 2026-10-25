/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Seminorm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FunProp

/-!
# Gamma mixtures of heat-damped Fourier energies

Tonelli applies to nonnegative Fourier energies, so these identities hold without a finite-energy
assumption. The order of integration is suitable for all positive Sobolev orders, including `a ≤ 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ

/-- The Gamma representation as an equality of nonnegative integrals. -/
theorem negSobolev_weight_eq_gamma_lintegral {a : ℝ} (ha : 0 < a) (ξ : Plane) :
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) = ENNReal.ofReal (Real.Gamma a)⁻¹ *
      ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
        ENNReal.ofReal (Real.exp (-u * ‖ξ‖ ^ 2)) := by
  rw [negSobolev_weight_eq_gamma_integral ha, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (integrableOn_negSobolev_weight_integrand ha ξ)]
  · congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _)
      (Real.exp_nonneg _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _)
      (Real.exp_nonneg _)) (Real.exp_nonneg _)

/-- Tonelli's Gamma-mixture formula for any measurable nonnegative Fourier energy density. -/
theorem lintegral_negSobolev_weight_mul {a : ℝ} (ha : 0 < a)
    {H : Plane → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ξ : Plane, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) * H ξ =
      ENNReal.ofReal (Real.Gamma a)⁻¹ *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
          ∫⁻ ξ : Plane, ENNReal.ofReal (Real.exp (-u * ‖ξ‖ ^ 2)) * H ξ := by
  have hm : Measurable (fun p : Plane × ℝ =>
      ENNReal.ofReal (p.2 ^ (a - 1) * Real.exp (-p.2)) *
        ENNReal.ofReal (Real.exp (-p.2 * ‖p.1‖ ^ 2)) * H p.1) := by
    fun_prop
  have hmU (ξ : Plane) : Measurable (fun u : ℝ =>
      ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
        ENNReal.ofReal (Real.exp (-u * ‖ξ‖ ^ 2))) := by fun_prop
  have hmX (u : ℝ) : Measurable (fun ξ : Plane =>
      ENNReal.ofReal (Real.exp (-u * ‖ξ‖ ^ 2)) * H ξ) := by fun_prop
  simp_rw [negSobolev_weight_eq_gamma_lintegral ha, mul_assoc,
    ← lintegral_mul_const _ (hmU _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap hm.aemeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [] with u
  simp only [mul_assoc]
  exact lintegral_const_mul _ (hmX u)

/-- The nonnegative Fourier energy after damping at heat time `2u`. -/
def heatDampedFourierEnergy (u : ℝ) (T : Distr) (χ : TestFn) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
    ∫⁻ ξ : Plane, ENNReal.ofReal (Real.exp (-u * ‖ξ‖ ^ 2)) *
      ENNReal.ofReal (‖localizedFourier T χ ξ‖ ^ 2)

/-- The local negative Sobolev energy is the Gamma mixture of its heat-damped Fourier energies. -/
theorem localNegSobolevSq_eq_gamma_mixture {a : ℝ} (ha : 0 < a) (T : Distr) (χ : TestFn) :
    localNegSobolevSq a T χ = ENNReal.ofReal (Real.Gamma a)⁻¹ *
      ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
        heatDampedFourierEnergy u T χ := by
  have hH : Measurable (fun ξ : Plane => ENNReal.ofReal (‖localizedFourier T χ ξ‖ ^ 2)) := by
    simpa only [Pi.pow_apply] using
      ((continuous_localizedFourier T χ).norm.pow 2).measurable.ennreal_ofReal
  unfold localNegSobolevSq
  simp_rw [← norm_localizedFourier_sq,
    ENNReal.ofReal_mul (negSobolev_weight_nonneg a _)]
  rw [lintegral_negSobolev_weight_mul ha hH]
  unfold heatDampedFourierEnergy
  simp_rw [mul_left_comm (ENNReal.ofReal (_ ^ (a - 1) * Real.exp (-_)))
    (ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  ac_rfl

end Critical2DKPZ

end
