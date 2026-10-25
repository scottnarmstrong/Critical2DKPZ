/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitCompactness
public import Critical2DKPZ.NonGaussian.EndpointScalar
import Mathlib.Tactic

/-! # Centering and approximation in the endpoint concentration argument -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Convergence of the L¹ quantity to zero implies convergence of the mean absolute value to zero. -/
theorem tendsto_integral_abs_of_eLpNorm_one
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (l : Filter ι)
    (F : ι → Ω → ℝ)
    (h : Tendsto (fun i => eLpNorm (F i) 1 P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, |F i ω| ∂P) l (𝓝 0) := by
  have hsmall := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have hreal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp h
  simp only [ENNReal.toReal_zero] at hreal
  apply hreal.congr'
  filter_upwards [hsmall] with i hi
  have hm := aestronglyMeasurable_of_eLpNorm_ne_top (ne_of_lt (hi.trans_le le_top))
  change (eLpNorm (F i) 1 P).toReal = ∫ ω, |F i ω| ∂P
  rw [eLpNorm_one_eq_lintegral_enorm hm, ← integral_norm_eq_lintegral_enorm hm]
  simp only [Real.norm_eq_abs]

/-- Centering at the expectation at most doubles a uniform approximation error. -/
theorem integral_abs_centered_le_of_approx {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P) {δ : ℝ}
    (hδ : ∀ᵐ ω ∂P, |X ω - Y ω| ≤ δ) :
    (∫ ω, |X ω - ∫ ω', X ω' ∂P| ∂P) ≤
      (∫ ω, |Y ω - ∫ ω', Y ω' ∂P| ∂P) + 2 * δ := by
  have hmean : |(∫ ω, X ω ∂P) - ∫ ω, Y ω ∂P| ≤ δ := by
    rw [← integral_sub hX hY, ← Real.norm_eq_abs]
    have hnorm : ∀ᵐ ω ∂P, ‖X ω - Y ω‖ ≤ δ := by
      simpa only [Real.norm_eq_abs] using hδ
    simpa using (norm_integral_le_of_norm_le_const (μ := P) hnorm)
  have hi : Integrable (fun ω => |Y ω - ∫ ω', Y ω' ∂P|) P :=
    (hY.sub (integrable_const _)).abs
  calc
    _ ≤ ∫ ω, |Y ω - ∫ ω', Y ω' ∂P| + 2 * δ ∂P := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
        (hi.add (integrable_const _))
      filter_upwards [hδ] with ω hω
      change |X ω - ∫ ω', X ω' ∂P| ≤ |Y ω - ∫ ω', Y ω' ∂P| + 2 * δ
      have h := abs_sub_le (X ω - ∫ ω', X ω' ∂P)
        (Y ω - ∫ ω', Y ω' ∂P) 0
      have hdiff : |(X ω - ∫ ω', X ω' ∂P) - (Y ω - ∫ ω', Y ω' ∂P)| ≤ 2 * δ := by
        calc
          _ = |(X ω - Y ω) - ((∫ ω', X ω' ∂P) - ∫ ω', Y ω' ∂P)| := by congr 1; ring
          _ ≤ |X ω - Y ω| + |(∫ ω', X ω' ∂P) - ∫ ω', Y ω' ∂P| := abs_sub _ _
          _ ≤ 2 * δ := by linarith only [hω, hmean]
      simp only [sub_zero] at h
      linarith only [h, hdiff]
    _ = _ := by rw [integral_add hi (integrable_const _)]; simp

/-- Uniformly approximating a random family at every small perturbation scale
transfers concentration from the approximations to that family. -/
theorem tendsto_integral_abs_centered_of_approximations
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : Filter ι) (X : ι → Ω → ℝ) (Y : ℝ → ι → Ω → ℝ)
    (hX : ∀ᶠ i in l, Integrable (X i) P)
    (hY : ∀ e : ℝ, 0 < e → e ≤ 1 / 2 → ∀ᶠ i in l, Integrable (Y e i) P)
    (happrox : ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      ∀ᶠ i in l, ∀ᵐ ω ∂P, |X i ω - Y e i ω| ≤ 2 * e)
    (hconc : ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      Tendsto (fun i => ∫ ω, |Y e i ω - ∫ ω', Y e i ω' ∂P| ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, |X i ω - ∫ ω', X i ω' ∂P| ∂P) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun i =>
      ha.trans_le (integral_nonneg fun ω => abs_nonneg _)
  · intro a ha
    let e : ℝ := min (a / 16) (1 / 4)
    have he : 0 < e := lt_min (by positivity) (by norm_num)
    have hehalf : e ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
    have hea : 4 * e ≤ a / 4 := by
      have h := min_le_left (a / 16) (1 / 4 : ℝ)
      dsimp [e]
      linarith only [h]
    have hsmall := (hconc e he hehalf).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 2))
    filter_upwards [hX, hY e he hehalf, happrox e he hehalf, hsmall] with i hiX hiY hiA hiS
    have hb := integral_abs_centered_le_of_approx P hiX hiY hiA
    linarith only [hb, hiS, hea, ha]

end Critical2DKPZ.NonGaussian
