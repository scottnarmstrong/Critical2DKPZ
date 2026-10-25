/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.LawFatou
public import Critical2DKPZ.SHF.Tsai.ConvergenceApproximation
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Transfer of approximate-flow error bounds to subsequential limits -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- A common integral bound for integrable squared differences is preserved under joint convergence in distribution. -/
theorem lintegral_sq_sub_le_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X Y : ℕ → Ω' → ℝ} {Xlim Ylim : Ω → ℝ} {C : ℝ}
    (hdist : TendstoInDistribution (fun N ω => (X N ω, Y N ω)) atTop
      (fun ω => (Xlim ω, Ylim ω)) μ P)
    (hbound : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => (X N ω - Y N ω) ^ 2) (μ N) ∧
        ∫ ω, (X N ω - Y N ω) ^ 2 ∂(μ N) ≤ C) :
    ∫⁻ ω, ENNReal.ofReal ((Xlim ω - Ylim ω) ^ 2) ∂P ≤ ENNReal.ofReal C := by
  let U : ℕ → Ω' → ℝ := fun N ω => (X N ω - Y N ω) ^ 2
  let V : Ω → ℝ := fun ω => (Xlim ω - Ylim ω) ^ 2
  have hdist' : TendstoInDistribution U atTop V μ P := by
    exact hdist.continuous_comp (g := fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (by fun_prop)
  have hU (N : ℕ) (ω : Ω') : 0 ≤ U N ω := by
    exact sq_nonneg _
  have hV (ω : Ω) : 0 ≤ V ω := by
    exact sq_nonneg _
  have hlinN : ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal (U N ω) ∂(μ N) ≤ ENNReal.ofReal C := by
    filter_upwards [hbound] with N hN
    rw [← ofReal_integral_eq_lintegral_ofReal hN.1
      (Filter.Eventually.of_forall fun ω => hU N ω)]
    exact ENNReal.ofReal_le_ofReal hN.2
  have hliminf : atTop.liminf
      (fun N => ∫⁻ ω, ENNReal.ofReal (U N ω) ∂(μ N)) ≤ ENNReal.ofReal C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨N, hN⟩ := (hb.and hlinN).exists
    exact hN.1.trans hN.2
  exact (Critical2DKPZ.SHF.Positivity.lintegral_ofReal_le_liminf_of_tendstoInDistribution_nonneg
    hdist' hU hV).trans hliminf

/-- Vanishing second-moment bounds imply convergence in measure on a finite measure space. -/
theorem tendstoInMeasure_of_lintegral_sq_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEMeasurable (f n) P)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂P ≤ ENNReal.ofReal ε) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro a ha
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let η : ℝ := δ * a ^ 2 / 2
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [hbound η hη] with n hn
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal ((f n ω) ^ 2)) P := by
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_id.pow 2).measurable.comp_aemeasurable (hf n)))
  have hthreshold : ENNReal.ofReal (a ^ 2) ≠ 0 :=
    (ENNReal.ofReal_ne_zero_iff).2 (sq_pos_of_pos ha)
  have hthresholdTop : ENNReal.ofReal (a ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov := meas_ge_le_lintegral_div hmeas hthreshold hthresholdTop
  have hset : {ω | a ≤ ‖f n ω‖} ⊆
      {ω | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal ((f n ω) ^ 2)} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    have hmul : 0 ≤ (‖f n ω‖ - a) * (‖f n ω‖ + a) :=
      mul_nonneg (sub_nonneg.mpr hω) (by positivity)
    have hsq : a ^ 2 ≤ ‖f n ω‖ ^ 2 := by nlinarith [hmul]
    simpa only [Real.norm_eq_abs, sq_abs] using hsq
  have hratio :
      (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂P) / ENNReal.ofReal (a ^ 2) ≤
        ENNReal.ofReal (δ / 2) := by
    calc
      _ ≤ ENNReal.ofReal η / ENNReal.ofReal (a ^ 2) :=
        ENNReal.div_le_div_right hn (ENNReal.ofReal (a ^ 2))
      _ = ENNReal.ofReal (δ / 2) := by
        rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos ha)]
        congr 1
        dsimp [η]
        field_simp
  have hmeasure : P {ω | a ≤ ‖f n ω‖} ≤ ENNReal.ofReal (δ / 2) := by
    exact (measure_mono hset).trans (hmarkov.trans hratio)
  have hreal : P.real {ω | a ≤ ‖f n ω‖} ≤ δ / 2 := by
    rw [measureReal_def]
    calc
      (P {ω | a ≤ ‖f n ω‖}).toReal ≤ (ENNReal.ofReal (δ / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
      _ = δ / 2 := ENNReal.toReal_ofReal (by positivity)
  have hreal' : P.real {ω | a ≤ ‖f n ω - 0‖} < δ := by
    simpa only [sub_zero] using lt_of_le_of_lt hreal (by linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hreal'


end Critical2DKPZ.SHF.Flow

end
