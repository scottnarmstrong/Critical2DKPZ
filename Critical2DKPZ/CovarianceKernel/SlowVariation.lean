/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Integral asymptotics for monotone slowly varying functions -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel


/-- For a nonnegative monotone slowly varying function, its first-moment integral is asymptotic to half the squared radius times its value at that radius. -/
theorem tendsto_integral_mul_div_of_slowlyVarying (M : ℝ → ℝ) (hM : Monotone M)
    (hM0 : 0 ≤ M 0) (hpos : ∀ᶠ R in atTop, 0 < M R)
    (hslow : ∀ u : ℝ, 0 < u → Tendsto (fun R => M (R * u) / M R) atTop (𝓝 1)) :
    Tendsto (fun R => 2 / R ^ 2 * (∫ a in (0 : ℝ)..R, a * M a) / M R)
      atTop (𝓝 1) := by
  let F : ℝ → ℝ → ℝ := fun R u => 2 * u * (M (R * u) / M R)
  have hmeas : ∀ R, AEStronglyMeasurable (F R) (volume.restrict (Ioc 0 1)) := by
    intro R
    exact ((measurable_const.mul measurable_id).mul
      ((hM.measurable.comp (measurable_const.mul measurable_id)).div_const _)).aestronglyMeasurable
  have hbound : ∀ᶠ R in atTop, ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      ‖F R u‖ ≤ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with R hR hMR
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hRu : 0 ≤ R * u := mul_nonneg hR.le hu.1.le
    have hratio0 : 0 ≤ M (R * u) / M R := div_nonneg (hM0.trans (hM hRu)) hMR.le
    have hratio1 : M (R * u) / M R ≤ 1 :=
      (div_le_one hMR).2 (hM (by nlinarith [hu.2]))
    dsimp [F]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu.1.le) hratio0)]
    calc
      2 * u * (M (R * u) / M R) ≤ 2 * u * 1 :=
        mul_le_mul_of_nonneg_left hratio1 (mul_nonneg (by norm_num) hu.1.le)
      _ ≤ 2 := by nlinarith [hu.2]
  have hlim : ∀ᵐ u ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun R => F R u) atTop (𝓝 (2 * u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa [F] using (hslow u hu.1).const_mul (2 * u)
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ => (2 : ℝ)) (Eventually.of_forall hmeas) hbound (integrable_const 2) hlim
  have hval : (∫ u in Ioc (0 : ℝ) 1, 2 * u) = 1 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul]
    norm_num [integral_id]
  rw [hval] at hconv
  apply hconv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with R hR hMR
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := fun a : ℝ => a * M a) (a := 0) (b := 1) R
  simp only [smul_eq_mul, mul_zero, mul_one] at hscale
  have heq : (∫ u in Ioc (0 : ℝ) 1, F R u) =
      (2 / (R * M R)) * (∫ u in (0 : ℝ)..1, (R * u) * M (R * u)) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp [F]
    field_simp
  rw [heq]
  have hRn : R ≠ 0 := ne_of_gt hR
  have hMRn : M R ≠ 0 := ne_of_gt hMR
  rw [← hscale]
  field_simp

end Critical2DKPZ.CovarianceKernel
