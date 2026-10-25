/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # From positive `Lᵖ` action bounds to bilinear kernel bounds -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A positive kernel action bounded on `Lᵖ` gives its zero-weight bilinear
bound, by Hölder. No finiteness assumption on the input test is required. -/
theorem WeightedFormBound.of_rpow_action_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite ν]
    {p : ℝ} (hp : 1 < p) {K : X → Y → ℝ≥0∞} {c : ℝ≥0∞}
    (hK : Measurable (Function.uncurry K))
    (hbound : ∀ f : Y → ℝ≥0∞, Measurable f →
      (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ p ∂μ) ≤ c ^ p * ∫⁻ y, f y ^ p ∂ν) :
    WeightedFormBound μ ν (fun _ => 0) (fun _ => 0) p (p / (p - 1)) K c := by
  intro f g hf hg
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  let A : X → ℝ≥0∞ := fun x => ∫⁻ y, K x y * f y ∂ν
  have hA : Measurable A := measurable_kernelAction ν hK hf
  have hnorm : (∫⁻ x, A x ^ p ∂μ) ^ (1 / p : ℝ) ≤
      c * (∫⁻ y, f y ^ p ∂ν) ^ (1 / p : ℝ) := by
    have hh := ENNReal.rpow_le_rpow (hbound f hf) (by positivity : 0 ≤ 1 / p)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p),
      ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at hh
    exact hh
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hA.aemeasurable hg.aemeasurable
  have hholder : (∫⁻ x, g x * A x ∂μ) ≤
      (∫⁻ x, A x ^ p ∂μ) ^ (1 / p : ℝ) *
        (∫⁻ x, g x ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1)) : ℝ) := by
    simpa only [Pi.mul_apply, mul_comm] using hh
  simpa only [Real.exp_zero, ENNReal.ofReal_one, mul_one] using
    hholder.trans (mul_le_mul' hnorm le_rfl)

end Critical2DKPZ.SHF.Tsai

end
