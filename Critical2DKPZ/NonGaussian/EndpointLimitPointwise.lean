/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitMeasures
import Mathlib.Tactic

/-! # The logarithmic terminal perturbation at a fixed endpoint start -/

@[expose] public noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- At a positive normalization, `log Z(1 + eφ) - log Z(1) = log (1 + e μ(φ))`,
where `μ` is the normalized endpoint pairing. -/
theorem log_heat_pairing_perturbation_eq (μ : Measure (Plane × Plane))
    {r : ℝ} (hr : 0 < r) (x : Plane) (φ : C_c(Plane, ℝ)) (hφ : ∀ y, |φ y| ≤ 1)
    {e : ℝ} (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hden : 0 < ∫ p, heatKernel r (p.1 - x) ∂μ) :
    Real.log (∫ p, heatKernel r (p.1 - x) * (1 + e * φ p.2) ∂μ) -
      Real.log (∫ p, heatKernel r (p.1 - x) ∂μ) =
      Real.log (1 + e * ∫ y, φ y ∂endpointTerminalMeasure μ r x) := by
  let ν := endpointTerminalMeasure μ r x
  let : IsFiniteMeasure ν :=
    ⟨(endpointTerminalMeasure_mass_le_one μ hr x).trans_lt ENNReal.one_lt_top⟩
  have hφi : Integrable (fun y => φ y) ν :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hone : (∫ _y, (1 : ℝ) ∂ν) = 1 := by
    rw [integral_endpointTerminalMeasure μ hr x (fun _ => 1) stronglyMeasurable_const]
    simp only [mul_one, div_self hden.ne']
  have hreal : ν.real Set.univ = 1 := by
    simpa only [integral_const, smul_eq_mul, mul_one] using hone
  have hbound : |∫ y, φ y ∂ν| ≤ 1 := by
    have hb : ∀ᵐ y ∂ν, ‖φ y‖ ≤ 1 :=
      Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hφ y
    simpa only [Real.norm_eq_abs, hreal, one_mul] using norm_integral_le_of_norm_le_const hb
  have hratio := integral_endpointTerminalMeasure μ hr x
    (fun y => 1 + e * φ y) (by fun_prop)
  change (∫ y, 1 + e * φ y ∂ν) = _ at hratio
  rw [integral_add (integrable_const _) (hφi.const_mul e), integral_const_mul, hone] at hratio
  have harg : 0 < 1 + e * ∫ y, φ y ∂ν := by
    have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hbound).1 he.le
    linarith only [hlow, hehalf]
  have hnum : (∫ p, heatKernel r (p.1 - x) * (1 + e * φ p.2) ∂μ) ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hratio
    linarith only [harg, hratio]
  rw [← Real.log_div hnum hden.ne', ← hratio]

end Critical2DKPZ.NonGaussian
