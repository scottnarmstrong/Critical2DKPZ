/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryAveraging
public import Critical2DKPZ.Extensions.ScaleLimit.MaximalLocalization

/-! # The stationary maximal inequality

Apply the deterministic weak inequality after cutting the field off on a ball
of twice the spatial averaging radius. Its volume is four times the inner
volume, so a universal constant follows without a spatial limiting argument.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A universal weak bound, uniformly in the radius truncation. -/
theorem stationary_maximalFnLe : ∃ C : ℝ≥0, ∀ (g : Plane → Ω → ℝ),
    Measurable (Function.uncurry g) →
    (∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P) →
    (∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀)) → Integrable (g 0) P →
    ∀ (R Λ : ℝ),
      ENNReal.ofReal Λ * P {ω | ENNReal.ofReal Λ < maximalFnLe R (fun z => g z ω) 0}
        ≤ C * ∫⁻ ω, ‖g 0 ω‖ₑ ∂P := by
  obtain ⟨C, hHL⟩ := hardyLittlewood_weak11
  refine ⟨4 * C, fun g hg hstat hcont hint R Λ => ?_⟩
  let k := max 1 R
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let U := ball (0 : Plane) k
  let V := ball (0 : Plane) (2 * k)
  let level := ENNReal.ofReal Λ
  let Y : Ω → ℝ≥0∞ := fun ω => ∫⁻ y in U, maximalEvent R level g (y, ω)
  let cut : Ω → Plane → ℝ := fun ω => V.indicator (fun z => g z ω)
  have hfinite : volume V ≠ ⊤ := measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hfinite
  have hp := integrable_stationary_prod (volume.restrict V) hg
    (identDistrib_eval_zero hstat) hint
  have hcut : ∀ᵐ ω ∂P, Integrable (cut ω) := by
    filter_upwards [hp.prod_left_ae] with ω hω
    exact (integrable_indicator_iff measurableSet_ball).mpr hω
  have hI (ω : Ω) : (∫⁻ z, ‖cut ω z‖ₑ) = ∫⁻ z in V, ‖g z ω‖ₑ := by
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr_ae
    filter_upwards with z
    change ‖V.indicator (fun z => g z ω) z‖ₑ = V.indicator (fun z => ‖g z ω‖ₑ) z
    by_cases hz : z ∈ V
    · rw [indicator_of_mem hz, indicator_of_mem hz]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, enorm_zero]
  have hY (ω : Ω) : Y ω ≤ volume {y | level < maximalFn (cut ω) y} := by
    rw [show Y ω = ∫⁻ y in U, maximalEvent R level g (y, ω) from rfl,
      setLIntegral_maximalEvent hg]
    apply measure_mono
    intro y hy
    exact hy.2.trans_le (maximalFnLe_indicator_ball_le (fun z => g z ω)
      (le_max_right 1 R) hy.1)
  have hpath : ∀ᵐ ω ∂P, level * Y ω ≤ (C : ℝ≥0∞) * ∫⁻ z in V, ‖g z ω‖ₑ := by
    filter_upwards [hcut] with ω hω
    exact (mul_le_mul' le_rfl (hY ω)).trans ((hHL (cut ω) hω level).trans_eq (by rw [hI]))
  have hi := lintegral_mono_ae hpath
  rw [lintegral_const_mul' level Y ENNReal.ofReal_ne_top,
    lintegral_const_mul' (C : ℝ≥0∞) _ ENNReal.coe_ne_top] at hi
  change level * (∫⁻ ω, ∫⁻ y in U, maximalEvent R level g (y, ω) ∂volume ∂P) ≤ _ at hi
  rw [expected_maximalEvent_volume hg hstat hcont hint,
    expected_spatial_mass hg (identDistrib_eval_zero hstat)] at hi
  have hv : volume V = 4 * volume U := volume_ball_two_mul 0 k
  have hbound : (level * P {ω | level < maximalFnLe R (fun z => g z ω) 0}) * volume U ≤
      ((4 * C : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, ‖g 0 ω‖ₑ ∂P) * volume U := by
    calc
      (level * P {ω | level < maximalFnLe R (fun z => g z ω) 0}) * volume U =
          level * (P {ω | level < maximalFnLe R (fun z => g z ω) 0} * volume U) := mul_assoc _ _ _
      _ ≤ (C : ℝ≥0∞) * ((∫⁻ ω, ‖g 0 ω‖ₑ ∂P) * volume V) := hi
      _ = ((4 * C : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, ‖g 0 ω‖ₑ ∂P) * volume U := by
        rw [hv]
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring
  exact (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume 0 hk).ne' measure_ball_lt_top.ne).mp hbound

/-- The stationary maximal inequality, with the universal constant before the field. -/
theorem stationary_maximal : ∃ C : ℝ≥0, ∀ (g : Plane → Ω → ℝ),
    Measurable (Function.uncurry g) →
    (∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P) →
    (∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀)) → Integrable (g 0) P →
    Measurable (fun ω => maximalFn (fun z => g z ω) 0) ∧
      ∀ Λ > 0, P {ω | ENNReal.ofReal Λ < maximalFn (fun z => g z ω) 0}
        ≤ ENNReal.ofReal (1 / Λ) * C * ∫⁻ ω, ‖g 0 ω‖ₑ ∂P := by
  obtain ⟨C, hC⟩ := stationary_maximalFnLe (P := P)
  refine ⟨C, fun g hg hstat hcont hint => ⟨measurable_maximalFn hg 0, fun Λ hΛ => ?_⟩⟩
  let level := ENNReal.ofReal Λ
  have hsets : {ω | level < maximalFn (fun z => g z ω) 0} =
      ⋃ n : ℕ, {ω | level < maximalFnLe n (fun z => g z ω) 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, maximalFn_eq_iSup, lt_iSup_iff]
  have hmono : Monotone (fun n : ℕ => {ω | level < maximalFnLe n (fun z => g z ω) 0}) := by
    intro n m hnm ω hω
    exact hω.trans_le (maximalFnLe_mono (fun z => g z ω) 0 (by exact_mod_cast hnm))
  have hmass : level * P {ω | level < maximalFn (fun z => g z ω) 0} ≤
      (C : ℝ≥0∞) * ∫⁻ ω, ‖g 0 ω‖ₑ ∂P := by
    rw [hsets, hmono.measure_iUnion, ENNReal.mul_iSup]
    exact iSup_le fun n => hC g hg hstat hcont hint n Λ
  have hlevel0 : level ≠ 0 := (ENNReal.ofReal_pos.mpr hΛ).ne'
  calc
    P {ω | level < maximalFn (fun z => g z ω) 0} =
        level⁻¹ * (level * P {ω | level < maximalFn (fun z => g z ω) 0}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlevel0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ level⁻¹ * ((C : ℝ≥0∞) * ∫⁻ ω, ‖g 0 ω‖ₑ ∂P) := mul_le_mul' le_rfl hmass
    _ = ENNReal.ofReal (1 / Λ) * C * ∫⁻ ω, ‖g 0 ω‖ₑ ∂P := by
      rw [ENNReal.ofReal_div_of_pos hΛ, ENNReal.ofReal_one, one_div]
      exact (mul_assoc _ _ _).symm

end Critical2DKPZ.Extensions.ScaleLimit

end
