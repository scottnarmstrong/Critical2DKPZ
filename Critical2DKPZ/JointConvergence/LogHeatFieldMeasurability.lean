/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.RandomMeasureIntegralMeasurability
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/-! # Measurability of spatially integrated log heat pairings -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.JointConvergence

set_option linter.style.haveILetI false in
/-- Joint measurability of the logarithm of a heat pairing. The nonnegative random-measure
integral is obtained by an exhaustion with compact cutoffs; local finiteness supplies finite mass
on each cutoff. -/
theorem aemeasurable_log_heatPairing_joint
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (δ : ℝ) (hδ : 0 < δ) (g : Plane → ℝ)
    (hg : Measurable g) (hgn : ∀ y, 0 ≤ g y) :
    AEMeasurable (fun q : Plane × Ω => Real.log
      (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2)) (volume.prod P) := by
  let K : ℕ → Set (Plane × Plane) := fun n => Metric.closedBall 0 (n : ℝ)
  have hKmeas : ∀ n, MeasurableSet (K n) := fun n =>
    Metric.isClosed_closedBall.measurableSet
  have hKmono : Monotone K := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
  have hKcover : ⋃ n, K n = Set.univ := by
    simpa only [K] using Metric.iUnion_closedBall_nat (0 : Plane × Plane)
  have hKfinite : ∀ᵐ ω ∂P, ∀ n, μ ω (K n) < ∞ := by
    filter_upwards [hlocal] with ω hω
    intro n
    letI : IsLocallyFiniteMeasure (μ ω) := hω
    exact (isCompact_closedBall (0 : Plane × Plane) (n : ℝ)).measure_lt_top
  let f : Plane → Plane × Plane → ℝ≥0∞ := fun x p =>
    ENNReal.ofReal (heatKernel δ (p.1 - x) * g p.2)
  have hf : Measurable (Function.uncurry f) := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_heatKernel δ).comp (measurable_snd.fst.sub measurable_fst) |>.mul
      (hg.comp measurable_snd.snd)
  have hlin := measurable_lintegral_measurableMeasure volume P μ hμ K hKmeas
    hKmono hKcover hKfinite f hf
  have hpairingEq (q : Plane × Ω) :
      (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2) =
        (∫⁻ p, f q.1 p ∂μ q.2).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (heatKernel_nonneg hδ.le _) (hgn p.2)
    · exact ((measurable_heatKernel δ).comp
        (measurable_fst.sub_const q.1) |>.mul (hg.comp measurable_snd)).aestronglyMeasurable
  have hpairing : AEMeasurable
      (fun q : Plane × Ω => ∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2)
      (volume.prod P) := by
    exact hlin.ennreal_toReal.congr
      (Filter.Eventually.of_forall fun q => (hpairingEq q).symm)
  exact Real.measurable_log.comp_aemeasurable hpairing

set_option linter.style.haveILetI false in
/-- A compactly supported spatial test paired with the logarithm of a heat-start measure
pairing is a measurable function of the random measure. Local finiteness gives the compact
exhaustion needed to make the inner nonnegative integral jointly measurable. -/
theorem aemeasurable_integral_log_heatPairing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (δ c : ℝ) (hδ : 0 < δ) (g φ : Plane → ℝ)
    (hg : Measurable g) (hgn : ∀ y, 0 ≤ g y) (hφ : Measurable φ) :
    AEMeasurable (fun ω => ∫ x, φ x *
      (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c) ∂volume) P := by
  classical
  let K : ℕ → Set (Plane × Plane) := fun n => Metric.closedBall 0 (n : ℝ)
  have hKmeas : ∀ n, MeasurableSet (K n) := fun n =>
    Metric.isClosed_closedBall.measurableSet
  have hKmono : Monotone K := by
    intro i j hij
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hij)
  have hKcover : ⋃ n, K n = Set.univ := by
    simpa only [K] using Metric.iUnion_closedBall_nat (0 : Plane × Plane)
  have hKfinite : ∀ᵐ ω ∂P, ∀ n, μ ω (K n) < ∞ := by
    filter_upwards [hlocal] with ω hω
    intro n
    letI : IsLocallyFiniteMeasure (μ ω) := hω
    exact (isCompact_closedBall (0 : Plane × Plane) (n : ℝ)).measure_lt_top
  let f : Plane → Plane × Plane → ℝ≥0∞ := fun x p =>
    ENNReal.ofReal (heatKernel δ (p.1 - x) * g p.2)
  have hf : Measurable (Function.uncurry f) := by
    apply ENNReal.measurable_ofReal.comp
    exact (measurable_heatKernel δ).comp (measurable_snd.fst.sub measurable_fst) |>.mul
      (hg.comp measurable_snd.snd)
  have hlin := measurable_lintegral_measurableMeasure volume P μ hμ K hKmeas hKmono
    hKcover hKfinite f hf
  have hpairingEq (q : Plane × Ω) :
      (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2) =
        (∫⁻ p, f q.1 p ∂μ q.2).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (heatKernel_nonneg hδ.le _) (hgn p.2)
    · exact ((measurable_heatKernel δ).comp
        (measurable_fst.sub_const q.1) |>.mul (hg.comp measurable_snd)).aestronglyMeasurable
  have hpairing : AEMeasurable
      (fun q : Plane × Ω => ∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2)
      (volume.prod P) := by
    exact hlin.ennreal_toReal.congr
      (Filter.Eventually.of_forall fun q => (hpairingEq q).symm)
  have hlog : AEMeasurable
      (fun q : Plane × Ω => Real.log
        (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2)) (volume.prod P) :=
    Real.measurable_log.comp_aemeasurable hpairing
  have hφprod : AEStronglyMeasurable (fun q : Plane × Ω => φ q.1) (volume.prod P) :=
    (hφ.comp measurable_fst).aestronglyMeasurable
  have hcprod : AEStronglyMeasurable (fun _ : Plane × Ω => c) (volume.prod P) :=
    measurable_const.aestronglyMeasurable
  have hfield : AEStronglyMeasurable
      (fun q : Plane × Ω => φ q.1 *
        (Real.log (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂μ q.2) - c))
      (volume.prod P) := hφprod.mul (hlog.aestronglyMeasurable.sub hcprod)
  exact hfield.prod_swap.integral_prod_right'.aemeasurable

end Critical2DKPZ.JointConvergence

end
