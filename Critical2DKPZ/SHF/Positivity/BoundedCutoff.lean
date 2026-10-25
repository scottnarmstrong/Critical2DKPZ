/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.HeatBoundedIntegrability
public import Critical2DKPZ.SHF.Tsai.Cutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Compact cutoffs for bounded heat-start pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace Critical2DKPZ.SHF.Positivity

/-- Compactly supported cutoff of the heat-start kernel with bounded continuous terminal data. -/
def heatBoundedTerminalCutoffTest (δ : ℝ) (x : Plane) (g : Plane →ᵇ ℝ) (R : ℝ) :
    C_c(Plane × Plane, ℝ) where
  toFun p := heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2
  continuous_toFun := by
    exact (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
      (g.continuous.comp continuous_snd) |>.mul
        ((continuous_ballCutoff R).comp continuous_fst) |>.mul
          ((continuous_ballCutoff R).comp continuous_snd))
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : Plane) (R + 1)).prod
        (isCompact_closedBall (0 : Plane) (R + 1)))
    intro p hp
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.1 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.2 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]

private theorem integrable_heatBoundedTerminalCutoff
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) (R : ℝ)
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) :
    Integrable (fun p : Plane × Plane => heatBoundedTerminalCutoffTest δ x g R p) μ := by
  have hF := integrable_heatKernel_mul_boundedTerminal μ hδ x g hK
  have hCut : Integrable (fun p : Plane × Plane =>
      heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2) μ := by
    have hmajor : Integrable (fun p : Plane × Plane =>
        ‖g‖ * heatKernel δ (p.1 - x)) μ := hK.const_mul ‖g‖
    apply hmajor.mono'
      (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
        (g.continuous.comp continuous_snd) |>.mul
          ((continuous_ballCutoff R).comp continuous_fst) |>.mul
            ((continuous_ballCutoff R).comp continuous_snd) |>.measurable.aestronglyMeasurable)
    filter_upwards [] with p
    have hk := heatKernel_nonneg hδ.le (p.1 - x)
    have h1 := ballCutoff_mem_Icc R p.1
    have h2 := ballCutoff_mem_Icc R p.2
    have hKg : ‖heatKernel δ (p.1 - x) * g p.2‖ ≤
        ‖g‖ * heatKernel δ (p.1 - x) := by
      calc
        ‖heatKernel δ (p.1 - x) * g p.2‖ =
            heatKernel δ (p.1 - x) * ‖g p.2‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hk]
        _ ≤ heatKernel δ (p.1 - x) * ‖g‖ :=
          mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk
        _ = ‖g‖ * heatKernel δ (p.1 - x) := by ring
    calc
      ‖heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2‖ =
          ‖heatKernel δ (p.1 - x) * g p.2‖ * ‖ballCutoff R p.1‖ * ‖ballCutoff R p.2‖ := by
            simp only [norm_mul]
      _ ≤ (‖g‖ * heatKernel δ (p.1 - x)) * 1 * 1 := by
            have hc1 : ‖ballCutoff R p.1‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_of_nonneg h1.1]
              exact h1.2
            have hc2 : ‖ballCutoff R p.2‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
              exact h2.2
            have hcprod : ‖ballCutoff R p.1‖ * ‖ballCutoff R p.2‖ ≤ 1 := by
              calc
                _ ≤ 1 * 1 := mul_le_mul hc1 hc2 (norm_nonneg _) (by norm_num)
                _ = 1 := by ring
            calc
              _ ≤ (‖g‖ * heatKernel δ (p.1 - x)) * ‖ballCutoff R p.1‖ *
                    ‖ballCutoff R p.2‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hKg (norm_nonneg _)) (norm_nonneg _)
              _ = (‖g‖ * heatKernel δ (p.1 - x)) *
                    (‖ballCutoff R p.1‖ * ‖ballCutoff R p.2‖) := by ring
              _ ≤ (‖g‖ * heatKernel δ (p.1 - x)) * 1 :=
                mul_le_mul_of_nonneg_left hcprod (by positivity)
              _ = (‖g‖ * heatKernel δ (p.1 - x)) * 1 * 1 := by ring
      _ = ‖g‖ * heatKernel δ (p.1 - x) := by ring
  change Integrable (fun p : Plane × Plane =>
    heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2) μ
  exact hCut

/-- A compact bounded-terminal heat cutoff is integrable whenever the uncut heat start is. -/
theorem integrable_heatBoundedTerminalCutoffTest
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) (R : ℝ)
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) :
    Integrable (fun p : Plane × Plane => heatBoundedTerminalCutoffTest δ x g R p) μ :=
  integrable_heatBoundedTerminalCutoff μ hδ x g R hK


end Critical2DKPZ.SHF.Positivity

end
