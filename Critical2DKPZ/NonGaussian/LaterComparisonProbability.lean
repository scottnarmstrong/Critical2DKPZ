/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
import Mathlib.Tactic

/-! # A logarithmic lower-tail estimate -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.NonGaussian

universe u

/-- For an integrable `X > 0` with `E X ≤ 1`, integrable logarithm and `E log X ≥ -C`,
one has `P(X < a) ≤ (1+C) / log (1/a)` for `0 < a < 1`. -/
theorem measure_lt_of_log_mean_lower (Ω : Type u) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (C a : ℝ)
    (ha : 0 < a) (ha1 : a < 1)
    (hX : ∀ᵐ ω ∂P, 0 < X ω) (hXint : Integrable X P) (hXmean : ∫ ω, X ω ∂P ≤ 1)
    (hlog : Integrable (fun ω => Real.log (X ω)) P)
    (hlogmean : -C ≤ ∫ ω, Real.log (X ω) ∂P) :
    P {ω | X ω < a} ≤ ENNReal.ofReal ((1 + C) / Real.log a⁻¹) := by
  let p : Ω → ℝ := fun ω => max (Real.log (X ω)) 0
  let q : Ω → ℝ := fun ω => max (-(Real.log (X ω))) 0
  have hpint : Integrable p P := by
    exact hlog.pos_part
  have hqint : Integrable q P := by
    exact hlog.neg_part
  have hp_le_X : p ≤ᵐ[P] X := by
    filter_upwards [hX] with ω hω
    dsimp [p]
    exact max_le (Real.log_le_self hω.le) (le_of_lt hω)
  have hq_eq : q =ᵐ[P] fun ω => p ω - Real.log (X ω) := by
    filter_upwards [hX] with ω hω
    dsimp [p, q]
    nlinarith [max_zero_sub_max_neg_zero_eq_self (Real.log (X ω))]
  have hq_integral : (∫ ω, q ω ∂P) =
      (∫ ω, p ω ∂P) - ∫ ω, Real.log (X ω) ∂P := by
    calc
      _ = ∫ ω, (p ω - Real.log (X ω)) ∂P := integral_congr_ae hq_eq
      _ = _ := integral_sub hpint hlog
  have hp_integral : (∫ ω, p ω ∂P) ≤ ∫ ω, X ω ∂P :=
    integral_mono_ae hpint hXint hp_le_X
  have hq_bound : (∫ ω, q ω ∂P) ≤ 1 + C := by
    rw [hq_integral]
    linarith
  have hL : 0 < Real.log a⁻¹ := by
    apply Real.log_pos
    rw [one_lt_inv₀ ha]
    exact ha1
  have hloginv : Real.log a⁻¹ = -Real.log a := by
    rw [Real.log_inv]
  have hmarkov := hqint.div_const (Real.log a⁻¹)
  have hq_nonneg : 0 ≤ᵐ[P] fun ω => q ω / Real.log a⁻¹ := by
    filter_upwards [] with ω
    exact div_nonneg (le_max_right _ _) hL.le
  have hset : ∀ ω ∈ {ω | X ω < a ∧ 0 < X ω},
      1 ≤ q ω / Real.log a⁻¹ := by
    intro ω hω
    have hωX := hω.2
    have hloglt : Real.log (X ω) < Real.log a := Real.log_lt_log hωX hω.1
    have hq : Real.log a⁻¹ ≤ q ω := by
      dsimp [q]
      rw [hloginv]
      exact (by linarith : -Real.log a ≤ -Real.log (X ω)).trans (le_max_left _ _)
    exact (le_div_iff₀ hL).2 (by simpa using hq)
  have hmeasure' := hmarkov.measure_le_integral hq_nonneg hset
  have hmeasure : P {ω | X ω < a} ≤
      ENNReal.ofReal (∫ ω, q ω / Real.log a⁻¹ ∂P) := by
    calc
      P {ω | X ω < a} = P {ω | X ω < a ∧ 0 < X ω} := by
        apply measure_congr
        filter_upwards [hX] with ω hω
        simp [hω]
      _ ≤ ENNReal.ofReal (∫ ω, q ω / Real.log a⁻¹ ∂P) := hmeasure'
  apply hmeasure.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div]
  exact div_le_div_of_nonneg_right hq_bound hL.le

end Critical2DKPZ.NonGaussian

end
