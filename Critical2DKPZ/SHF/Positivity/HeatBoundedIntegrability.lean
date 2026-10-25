/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.HeatStartLimit
public import Critical2DKPZ.SHF.Positivity.MeasurablePairing
public import Critical2DKPZ.Definitions.ShfPairing
import Mathlib.Tactic

/-! # Integrability and first-moment bounds for bounded heat-start pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.SHF.Positivity

/-- Multiplying the heat-start by bounded continuous terminal data preserves integrability. -/
theorem integrable_heatKernel_mul_boundedTerminal
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ)
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) :
    Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) μ := by
  have hmajor : Integrable (fun p : Plane × Plane => ‖g‖ * heatKernel δ (p.1 - x)) μ :=
    hK.const_mul ‖g‖
  apply hmajor.mono'
    (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
      (g.continuous.comp continuous_snd)).measurable.aestronglyMeasurable
  filter_upwards [] with p
  have hk := heatKernel_nonneg hδ.le (p.1 - x)
  calc
    ‖heatKernel δ (p.1 - x) * g p.2‖ =
        ‖heatKernel δ (p.1 - x)‖ * ‖g p.2‖ := norm_mul _ _
    _ = heatKernel δ (p.1 - x) * ‖g p.2‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hk]
    _ ≤ heatKernel δ (p.1 - x) * ‖g‖ :=
      mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk
    _ = ‖g‖ * heatKernel δ (p.1 - x) := by ring

private theorem heatKernel_mul_boundedTerminal_integral_norm_le
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ)
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) :
    |∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ| ≤
      ‖g‖ * ∫ p, heatKernel δ (p.1 - x) ∂μ := by
  have hF := integrable_heatKernel_mul_boundedTerminal μ hδ x g hK
  have hmajor : Integrable (fun p : Plane × Plane => ‖g‖ * heatKernel δ (p.1 - x)) μ :=
    hK.const_mul ‖g‖
  calc
    |∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ| =
        ‖∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ p, ‖heatKernel δ (p.1 - x) * g p.2‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, ‖g‖ * heatKernel δ (p.1 - x) ∂μ := by
      apply integral_mono hF.norm hmajor
      intro p
      have hk := heatKernel_nonneg hδ.le (p.1 - x)
      calc
        ‖heatKernel δ (p.1 - x) * g p.2‖ =
            ‖heatKernel δ (p.1 - x)‖ * ‖g p.2‖ := norm_mul _ _
        _ = heatKernel δ (p.1 - x) * ‖g p.2‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hk]
        _ ≤ heatKernel δ (p.1 - x) * ‖g‖ :=
          mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk
        _ = ‖g‖ * heatKernel δ (p.1 - x) := by ring
    _ = ‖g‖ * ∫ p, heatKernel δ (p.1 - x) ∂μ := integral_const_mul _ _

/-- With bounded continuous terminal data, a fixed heat-start pairing is spatially integrable almost surely and integrable as a random variable, with expected absolute value at most the terminal sup norm. -/
theorem isCriticalSHF_heat_bounded_pairing_integrable_bound (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) :
    (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
      heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
    Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
    ∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖ := by
  have hmass := isCriticalSHF_heat_start_integrable_bound ϑ P Z hZ hs hst hδ x
  have hmassAE := isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ hs hst hδ x
  have hpairAE : ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (Z s t ω) := by
    filter_upwards [hmassAE] with ω hω
    exact integrable_heatKernel_mul_boundedTerminal (Z s t ω) hδ x g hω
  have hpairMeas := aemeasurable_integral_of_measurable_measure P (Z s t)
    (hZ.1 s t hs hst)
    (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2)
    (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
      (g.continuous.comp continuous_snd)).measurable hpairAE
  have hpairInt : Integrable
      (fun ω => shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω) P := by
    have hmajor : Integrable (fun ω => ‖g‖ *
        ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω)) P := hmass.1.const_mul ‖g‖
    apply hmajor.mono' hpairMeas.aestronglyMeasurable
    filter_upwards [hmassAE] with ω hω
    rw [Real.norm_eq_abs]
    exact heatKernel_mul_boundedTerminal_integral_norm_le (Z s t ω) hδ x g hω
  refine ⟨hpairAE, hpairInt, ?_⟩
  have hmajor : Integrable (fun ω => ‖g‖ *
      ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω)) P := hmass.1.const_mul ‖g‖
  have hbound : ∀ᵐ ω ∂P, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ≤
      ‖g‖ * ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω) := by
    filter_upwards [hmassAE] with ω hω
    exact heatKernel_mul_boundedTerminal_integral_norm_le (Z s t ω) hδ x g hω
  calc
    (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P) ≤
        ∫ ω, ‖g‖ * ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω) ∂P :=
      integral_mono_ae hpairInt.abs hmajor hbound
    _ = ‖g‖ * ∫ ω, ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω) ∂P :=
      integral_const_mul _ _
    _ ≤ ‖g‖ := by
      exact (mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg _)).trans_eq (mul_one _)

end Critical2DKPZ.SHF.Positivity

end
