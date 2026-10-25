/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.DistributionBounds
import Mathlib.Tactic

/-! # Open-set transfer of one-sided ratio tails

Only the limiting denominator must be almost surely positive. The event used
for Portmanteau includes positivity explicitly, and division is removed by
multiplication before checking openness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Lower ratio tails pass under joint convergence and positivity of the limit denominator. -/
theorem measure_ratio_lt_le_of_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → Fin 2 → ℝ} {Y : Ω' → Fin 2 → ℝ}
    (hX : TendstoInDistribution X atTop Y (fun _ => P) Q)
    (hp : ∀ᵐ ω ∂Q, 0 < Y ω 1) (c : ℝ) (C : ℝ≥0∞)
    (hb : ∀ᶠ n in atTop, P {ω | X n ω 0 / X n ω 1 < c} ≤ C) :
    Q {ω | Y ω 0 / Y ω 1 < c} ≤ C := by
  let G : Set (Fin 2 → ℝ) := {v | 0 < v 1 ∧ v 0 < c * v 1}
  have hG : IsOpen G := (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_lt (continuous_apply 0) (continuous_const.mul (continuous_apply 1)))
  have hbG : ∀ᶠ n in atTop, P (X n ⁻¹' G) ≤ C := by
    filter_upwards [hb] with n hn
    apply (measure_mono ?_).trans hn
    intro ω hω
    exact (div_lt_iff₀ hω.1).mpr hω.2
  have h := measure_open_le_of_tendstoInDistribution hX G hG C hbG
  have heq : (Y ⁻¹' G) =ᵐ[Q] {ω | Y ω 0 / Y ω 1 < c} := by
    filter_upwards [hp] with ω hω
    apply propext
    exact ⟨fun h => (div_lt_iff₀ hω).mpr h.2, fun h => ⟨hω, (div_lt_iff₀ hω).mp h⟩⟩
  rw [measure_congr heq] at h
  exact h

/-- Upper ratio tails pass under the same assumptions. -/
theorem measure_lt_ratio_le_of_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → Fin 2 → ℝ} {Y : Ω' → Fin 2 → ℝ}
    (hX : TendstoInDistribution X atTop Y (fun _ => P) Q)
    (hp : ∀ᵐ ω ∂Q, 0 < Y ω 1) (c : ℝ) (C : ℝ≥0∞)
    (hb : ∀ᶠ n in atTop, P {ω | c < X n ω 0 / X n ω 1} ≤ C) :
    Q {ω | c < Y ω 0 / Y ω 1} ≤ C := by
  let G : Set (Fin 2 → ℝ) := {v | 0 < v 1 ∧ c * v 1 < v 0}
  have hG : IsOpen G := (isOpen_lt continuous_const (continuous_apply 1)).inter
    (isOpen_lt (continuous_const.mul (continuous_apply 1)) (continuous_apply 0))
  have hbG : ∀ᶠ n in atTop, P (X n ⁻¹' G) ≤ C := by
    filter_upwards [hb] with n hn
    apply (measure_mono ?_).trans hn
    intro ω hω
    exact (lt_div_iff₀ hω.1).mpr hω.2
  have h := measure_open_le_of_tendstoInDistribution hX G hG C hbG
  have heq : (Y ⁻¹' G) =ᵐ[Q] {ω | c < Y ω 0 / Y ω 1} := by
    filter_upwards [hp] with ω hω
    apply propext
    exact ⟨fun h => (lt_div_iff₀ hω).mpr h.2, fun h => ⟨hω, (lt_div_iff₀ hω).mp h⟩⟩
  rw [measure_congr heq] at h
  exact h

end Critical2DKPZ.Extensions.ScaleLimit
