/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordSpatialL1
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureContinuity
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Tactic

/-! # Renewal-time Fubini for the complete tested two-particle future -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

private theorem measurable_joint_heat : Measurable (fun p : ℝ × Plane => heatKernel p.1 p.2) := by
  unfold heatKernel
  fun_prop

private theorem testedFuture_proxy_measurable
    (θ q : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Measurable (fun p : ℝ × (Plane × Plane) =>
      φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) * (DeltaBose.scalarDensity θ p.1 *
        (heatKernel (2 * (q - p.1)) (p.2.2 - p.2.1) *
          heatKernel (q / 2) ((1 / 2 : ℝ) • (p.2.1 + p.2.2) - z)))) := by
  have hφ₀ : Measurable (fun p : ℝ × (Plane × Plane) => φ 0 (a 0, p.2.1)) :=
    (φ 0).measurable.comp (measurable_const.prodMk measurable_snd.fst)
  have hφ₁ : Measurable (fun p : ℝ × (Plane × Plane) => φ 1 (a 1, p.2.2)) :=
    (φ 1).measurable.comp (measurable_const.prodMk measurable_snd.snd)
  have hρ : Measurable (fun p : ℝ × (Plane × Plane) => DeltaBose.scalarDensity θ p.1) :=
    DeltaBose.measurable_scalarDensity.comp
    (measurable_const.prodMk (measurable_fst : Measurable (fun p : ℝ × (Plane × Plane) => p.1)))
  have harg : Measurable (fun p : ℝ × (Plane × Plane) =>
      (2 * (q - p.1), p.2.2 - p.2.1)) := by fun_prop
  have hgap : Measurable (fun p : ℝ × (Plane × Plane) =>
      heatKernel (2 * (q - p.1)) (p.2.2 - p.2.1)) := measurable_joint_heat.comp harg
  have hcenter : Measurable (fun p : ℝ × (Plane × Plane) =>
      heatKernel (q / 2) ((1 / 2 : ℝ) • (p.2.1 + p.2.2) - z)) :=
    (measurable_heatKernel (q / 2)).comp (by fun_prop)
  exact (hφ₀.mul hφ₁).mul (hρ.mul (hgap.mul hcenter))

/-- Joint integrability over the complete renewal-time interval and both
terminal locations. The scalar-density majorant includes both endpoints. -/
theorem integrable_pairTwo_testedFuture_time_terminal
    (θ q : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Integrable (fun p : ℝ × (Plane × Plane) =>
      φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
        pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2])
      ((volume.restrict (Set.Ioo 0 q)).prod ((volume : Measure Plane).prod volume)) := by
  let ν : Measure (Plane × Plane) := (volume : Measure Plane).prod volume
  let F : ℝ × (Plane × Plane) → ℝ := fun p =>
    φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) * pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2]
  let G : ℝ × (Plane × Plane) → ℝ := fun p =>
    φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) * (DeltaBose.scalarDensity θ p.1 *
      (heatKernel (2 * (q - p.1)) (p.2.2 - p.2.1) *
        heatKernel (q / 2) ((1 / 2 : ℝ) • (p.2.1 + p.2.2) - z)))
  have htime : ∀ᵐ p ∂(volume.restrict (Set.Ioo 0 q)).prod ν, p.1 ∈ Set.Ioo 0 q := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Eventually.of_forall fun _ => hu
  have heq : F =ᵐ[(volume.restrict (Set.Ioo 0 q)).prod ν] G := by
    filter_upwards [htime] with p hp
    dsimp only [F, G]
    rw [pairTwoFutureSpatialProfile_eq_centerGap hp.1 hp.2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hm : AEStronglyMeasurable F ((volume.restrict (Set.Ioo 0 q)).prod ν) :=
    (testedFuture_proxy_measurable θ q φ a z).aestronglyMeasurable.congr heq.symm
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (pairTwoFutureSpatialProfile_test_integrable_bound θ hu.1 hu.2 φ a z).1
  · let M : ℝ := ‖(φ 0).toBoundedContinuousFunction‖ * ‖(φ 1).toBoundedContinuousFunction‖
    have hρ : IntegrableOn (DeltaBose.scalarDensity θ) (Set.Ioo 0 q) :=
      (Renewal.integrableOn_scalarDensity_Ioc θ q).mono_set Set.Ioo_subset_Ioc_self
    apply (hρ.mul_const M).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hb := (pairTwoFutureSpatialProfile_test_integrable_bound θ hu.1 hu.2 φ a z).2
    convert hb using 1
    dsimp [M]
    ring


end Critical2DKPZ.SHF.Moments
