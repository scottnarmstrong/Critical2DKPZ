/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsCriticalKPZ
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Mathlib.Tactic

/-! # Measurability of scalar KPZ observables -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.NonGaussian

private theorem aemeasurable_flat_regularized_test (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (ψ : TestFn) :
    AEMeasurable (fun ω => ∫ x, ψ x * kpzRegularized P Z t δ 0 x ω) P := by
  let μ (ω : Ω) := (Z 0 (t - δ) ω).map Prod.swap
  have hμ : Measurable μ := (Measure.measurable_map Prod.swap measurable_swap).comp
    (hZ.1 0 (t - δ) le_rfl (sub_pos.2 hδt))
  have hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 0 (t - δ) le_rfl (sub_pos.2 hδt)] with ω hω
    exact CovarianceKernel.locallyFinite_map_homeomorph
      (Homeomorph.prodComm Plane Plane) (Z 0 (t - δ) ω) hω.1
  let c : ℝ := ∫ ω', Real.log (shfPairing Z 0 (t - δ) (fun _ => 1)
    (fun y => heatKernel δ y) ω') ∂P
  have hbase := JointConvergence.aemeasurable_integral_log_heatPairing P μ hμ hLF δ c hδ
    (fun _ => 1) ψ measurable_const (fun _ => zero_le_one) ψ.continuous.measurable
  have hPair (ω : Ω) (x : Plane) :
      (∫ p : Plane × Plane, heatKernel δ (p.1 - x) * 1 ∂μ ω) =
        shfPairing Z 0 (t - δ) (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y))
          (fun y => heatKernel δ (y - x)) ω := by
    have htest : Measurable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * 1) :=
      ((measurable_heatKernel δ).comp (measurable_fst.sub measurable_const)).mul measurable_const
    dsimp only [μ]
    rw [integral_map measurable_swap.aemeasurable htest.aestronglyMeasurable]
    simp [shfPairing]
  have hpoint (ω : Ω) (x : Plane) : kpzRegularized P Z t δ 0 x ω =
      Real.log (∫ p : Plane × Plane, heatKernel δ (p.1 - x) * 1 ∂μ ω) - c := by
    change Real.log (shfPairing Z 0 (t - δ) (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y))
      (fun y => heatKernel δ (y - x)) ω) - c = _
    rw [hPair]
  apply hbase.congr
  exact Eventually.of_forall fun ω => integral_congr_ae (Eventually.of_forall fun x =>
    congrArg (fun a : ℝ => ψ x * a) (hpoint ω x).symm)

/-- Every scalar pairing of a flat-initial critical KPZ process with a smooth compact test
is almost everywhere measurable. -/
theorem aemeasurable_criticalKPZ_flat_pairing (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) :
    AEMeasurable (fun ω => H t 0 ω ψ) P := by
  let δ : ℕ → ℝ := fun n => t / ((n : ℝ) + 2)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδlt (n : ℕ) : δ n < t := by
    dsimp only [δ]
    exact div_lt_self ht (by linarith : (1 : ℝ) < (n : ℝ) + 2)
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (2 : ℝ) + (n : ℝ)) atTop atTop := by
      apply tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      linarith
    have hnat' : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      simpa only [add_comm] using hnat
    have hden := tendsto_inv_atTop_zero.comp hnat'
    simpa only [δ, div_eq_mul_inv, Function.comp_apply, mul_zero] using hden.const_mul t
  have hδlim : Tendsto δ atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδzero, Eventually.of_forall hδpos⟩
  exact TendstoInMeasure.aemeasurable
    (fun n => aemeasurable_flat_regularized_test ϑ P Z hZ (hδpos n) (hδlt n) ψ)
    ((hH t ht 0 ψ).comp hδlim)

end Critical2DKPZ.NonGaussian

end
