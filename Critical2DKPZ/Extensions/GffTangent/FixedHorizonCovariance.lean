/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.LinearCovariance
public import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Covariance normalization at a fixed positive horizon -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- At a fixed horizon the collision primitive converges under every integrable
heat form. The upper endpoint is excluded before applying pointwise convergence. -/
theorem tendsto_integral_mul_uFun_fixed_horizon {T : ℝ} (hT : 0 < T)
    (H : ℝ → ℝ) (hH : IntegrableOn H (Ioo 0 T)) :
    Tendsto (fun l : ℝ => l * ∫ s in Ioc 0 T, H s * uFun l (T - s)) atTop
      (𝓝 (∫ s in Ioc 0 T, H s)) := by
  let μ := volume.restrict (Ioo 0 T)
  let F : ℝ → ℝ → ℝ := fun l s => H s * (l * uFun l (T - s))
  have hlarge : ∀ᶠ l : ℝ in atTop, max 1 (2 * Real.log T) < l := eventually_gt_atTop _
  have hFm : ∀ l : ℝ, AEStronglyMeasurable (F l) μ := fun l =>
    hH.aestronglyMeasurable.mul
      (((measurable_uFun.comp (measurable_const.prodMk
        (measurable_const.sub measurable_id))).const_mul l).aestronglyMeasurable)
  have hb : ∀ᶠ l : ℝ in atTop, ∀ᵐ s ∂μ, ‖F l s‖ ≤ 2 * |H s| := by
    filter_upwards [hlarge] with l hl
    have hl0 : 0 < l := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hl)
    have hl2 : 2 * Real.log T < l := (le_max_right _ _).trans_lt hl
    have hlT : Real.log T < l := by linarith only [hl0, hl2]
    have hden : 0 < l - Real.log T := sub_pos.mpr hlT
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hU : uFun l (T - s) ≤ 1 / (l - Real.log T) :=
      (uFun_mono (sub_pos.mpr hs.2) (sub_le_self _ hs.1.le)).trans (uFun_pos_le hT hlT).2
    have htwo : l * uFun l (T - s) ≤ 2 := by
      calc
        _ ≤ l * (1 / (l - Real.log T)) := mul_le_mul_of_nonneg_left hU hl0.le
        _ ≤ 2 := by rw [mul_one_div, div_le_iff₀ hden]; linarith only [hl2]
    change ‖H s * (l * uFun l (T - s))‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hl0.le (uFun_nonneg _ _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htwo (abs_nonneg (H s))
  have hp : ∀ᵐ s ∂μ, Tendsto (fun l => F l s) atTop (𝓝 (H s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hr : Tendsto (fun l : ℝ => Real.log (T - s) / l) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa only [F, mul_one] using
      (tendsto_mul_uFun (fun _ => T - s) (fun _ => sub_pos.mpr hs.2) hr).const_mul (H s)
  have hd : Tendsto (fun l => ∫ s, F l s ∂μ) atTop (𝓝 (∫ s, H s ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun s => 2 * |H s|)
    · exact Eventually.of_forall hFm
    · exact hb
    · exact hH.abs.const_mul 2
    · exact hp
  rw [integral_Ioc_eq_integral_Ioo]
  apply hd.congr'
  filter_upwards [] with l
  dsimp only [F, μ]
  rw [integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  ring

/-- The covariance matrix in the fixed-horizon CLT is the limit of the exact
rescaled flow covariance. No Gaussian limit is inferred from covariance alone. -/
theorem covariance_fixed_horizon_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    {T : ℝ} (hT : 0 < T) (f g : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0) :
    Tendsto (fun l => l * covariance
      (shfPairing (Z l) 0 T f (fun _ => 1))
      (shfPairing (Z l) 0 T g (fun _ => 1)) P) atTop
      (𝓝 (4 * Real.pi * ∫ s in Ioc 0 T, ∫ x : Plane, f x * heatSmooth (2 * s) g x)) := by
  have hf : Integrable (f : Plane → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable (g : Plane → ℝ) := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  obtain ⟨Cf, hCf⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  obtain ⟨Cg, hCg⟩ := g.hasCompactSupport.exists_bound_of_continuous g.continuous
  have hH : IntegrableOn (fun s => ∫ x : Plane, f x * heatSmooth (2 * s) g x) (Ioo 0 T) :=
    (integral_inner_heatSemigroup_testFn f g hfzero hgzero).1.mono_set Ioo_subset_Ioi_self
  have hh := (tendsto_integral_mul_uFun_fixed_horizon hT _ hH).const_mul (4 * Real.pi)
  apply hh.congr'
  filter_upwards [] with l
  rw [covariance_shfPairing_start l P (Z l) (hZ l) (le_refl 0) hT
    f.continuous.measurable g.continuous.measurable hf hg
    (by simpa only [Real.norm_eq_abs] using hCf) (by simpa only [Real.norm_eq_abs] using hCg)]
  simp only [sub_zero]
  ring

end Critical2DKPZ.Extensions.GffTangent
