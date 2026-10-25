/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatStartCompactRatio
public import Critical2DKPZ.SHF.Tsai.Cutoff
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-! # The mean bound for the flat-terminal normalized ratio -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai Critical2DKPZ.LocalSobolev
open scoped CompactlySupported BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- The flat-terminal normalized heat-start ratio is integrable and has mean at most one. -/
theorem integral_heatStart_div_le_one_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (_hsym : ShfSymmetriesAt ϑ P Z) (hdense : DenseSHFAt ϑ P Z)
    {r s t δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    Integrable (fun ω => shfPairing Z r t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) P ∧
    ∫ ω, shfPairing Z r t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω ∂P ≤ 1 := by
  let f : Plane → ℝ := fun y => heatKernel δ (y - x)
  let g (n : ℕ) : C_c(Plane, ℝ) :=
    ⟨⟨ballCutoff (n : ℝ), continuous_ballCutoff _⟩, hasCompactSupport_ballCutoff _⟩
  let A (ω : Ω) := ∫ p, f p.1 ∂Z r s ω
  let F (n : ℕ) (ω : Ω) := (∫ p, f p.1 * g n p.2 ∂Z r t ω) / A ω
  let G (ω : Ω) := (∫ p, f p.1 ∂Z r t ω) / A ω
  have hg0 (n : ℕ) (y : Plane) : 0 ≤ g n y := (ballCutoff_mem_Icc (n : ℝ) y).1
  have hg1 (n : ℕ) (y : Plane) : g n y ≤ 1 := (ballCutoff_mem_Icc (n : ℝ) y).2
  have hEst (n : ℕ) : Integrable (F n) P ∧ (∫ ω, F n ω ∂P) ≤ 1 := by
    simpa only [F, A, f, shfPairing, mul_one] using
      integral_heatStart_cc_div_le_one_of ϑ P Z hZ hdense hr hrs hst hδ x (g n) (hg0 n) (hg1 n)
  have hF0 (n : ℕ) : 0 ≤ᵐ[P] F n := Eventually.of_forall fun ω =>
    div_nonneg (integral_nonneg fun p : Plane × Plane =>
      mul_nonneg (heatKernel_nonneg hδ.le (p.1 - x)) (hg0 n p.2))
      (integral_nonneg fun p : Plane × Plane => heatKernel_nonneg hδ.le (p.1 - x))
  have hInner : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1) (Z r t ω) := by
    have h := (SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr (hrs.trans hst) hδ x
      (1 : Plane →ᵇ ℝ)).1
    simpa only [f, BoundedContinuousFunction.coe_one, Pi.one_apply, mul_one] using h
  have hNumLimit : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ p, f p.1 * g n p.2 ∂Z r t ω)
      atTop (𝓝 (∫ p, f p.1 ∂Z r t ω)) := by
    filter_upwards [hInner] with ω hω
    apply tendsto_integral_of_dominated_convergence (fun p : Plane × Plane => f p.1)
    · intro n
      have hc : Continuous (fun p : Plane × Plane => f p.1 * g n p.2) :=
        ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
          ((g n).continuous.comp continuous_snd)
      exact hc.measurable.aestronglyMeasurable
    · exact hω
    · intro n
      exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg hδ.le (p.1 - x)) (hg0 n p.2))]
        exact mul_le_of_le_one_right (heatKernel_nonneg hδ.le (p.1 - x)) (hg1 n p.2)
    · exact Eventually.of_forall fun p => by
        have hcut : Tendsto (fun n : ℕ => g n p.2) atTop (𝓝 1) :=
          (tendsto_ballCutoff p.2).comp tendsto_natCast_atTop_atTop
        simpa only [mul_one] using tendsto_const_nhds.mul hcut
  have hRatioLimit : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hNumLimit] with ω hω
    exact hω.div_const (A ω)
  let η : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hf : Measurable f := (measurable_heatKernel δ).comp (measurable_id.sub measurable_const)
  have hA : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, f p.1 ∂μ) :=
    ((hf.comp measurable_fst).stronglyMeasurable.integral_kernel (κ := η)).measurable
  have hG : AEMeasurable G P :=
    ((hA.comp (hZ.1 r t hr (hrs.trans hst))).div (hA.comp (hZ.1 r s hr hrs))).aemeasurable
  have hFatou := integrable_and_integral_le_of_ae_tendsto_nonneg P F (fun n => (hEst n).1)
    hF0 G hG hRatioLimit 1 zero_le_one (fun n => (hEst n).2)
  simpa only [G, A, f, shfPairing, mul_one] using hFatou.2

end Critical2DKPZ.NonGaussian

end
