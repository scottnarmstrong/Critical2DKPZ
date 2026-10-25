/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralShapeTail
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The deterministic shape comparison -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A continuous, bounded shape vanishing at zero with first-order decay has negligible
spectral energy on the double-logarithmic scale. -/
theorem shape_comparison_of_decay (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    (m : Plane → ℂ) (hm : Continuous m) (hm0 : m 0 = 0)
    {B M₀ : ℝ} (hB : 0 ≤ B) (hM₀ : 0 ≤ M₀)
    (hdecay : ∀ z : Plane, ‖z‖ * ‖m z‖ ≤ B) (hbounded : ∀ z : Plane, ‖m z‖ ≤ M₀) :
    Tendsto (fun ε : ℝ => (∫ ξ, ‖m (ε • ξ)‖ ^ 2 ∂ν) /
      Real.log (Real.log ε⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, houter⟩ := spectral_outer_energy_bound ν hball m hm hB hdecay
  have hden : Tendsto (fun ε : ℝ => Real.log (Real.log ε⁻¹)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  apply tendsto_order.mpr
  constructor
  · intro q hq
    filter_upwards [hden.eventually_gt_atTop 0] with ε hε
    exact hq.trans_le (div_nonneg (integral_nonneg fun _ => sq_nonneg _) hε.le)
  · intro q hq
    let M := Real.sqrt (q / 4)
    have hMpos : 0 < M := Real.sqrt_pos.mpr (by positivity)
    have hMsq : M ^ 2 = q / 4 := Real.sq_sqrt (by positivity)
    obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp hm.continuousAt M hMpos
    let a := r / 2
    have ha : 0 < a := by dsimp [a]; positivity
    have hlocal : ∀ z : Plane, ‖z‖ ≤ a → ‖m z‖ ≤ M := by
      intro z hz
      have hz' : dist z 0 < r := by rw [dist_zero_right]; dsimp [a] at hz; linarith
      simpa only [hm0, dist_zero_right] using (hnear hz').le
    have hdecK : Tendsto (fun K : ℝ => C / K ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    obtain ⟨K, hKa, hCK⟩ := ((eventually_gt_atTop (max a 1)).and
      (hdecK.eventually (Iio_mem_nhds (by positivity : 0 < q / 4)))).exists
    have hK : 0 < K := zero_lt_one.trans ((le_max_right a 1).trans_lt hKa)
    have haK : a ≤ K := ((le_max_left a 1).trans_lt hKa).le
    let mid := fun ε : ℝ =>
      ∫ ξ in Metric.closedBall (0 : Plane) (K / ε) \ Metric.closedBall 0 (a / ε),
        ‖m (ε • ξ)‖ ^ 2 ∂ν
    have hmiddle := spectral_middle_energy_tendsto ν hball m hm ha hK haK hM₀ hbounded
    have hup := (((specMass_scaled_inv_tendsto ν hball ha).const_mul (M ^ 2)).add
      hmiddle).add ((specMass_scaled_inv_tendsto ν hball hK).const_mul (C / K ^ 2))
    have hlim : M ^ 2 * 1 + 0 + C / K ^ 2 * 1 < q := by rw [hMsq]; linarith
    filter_upwards [self_mem_nhdsWithin, hden.eventually_gt_atTop 0,
      houter K hK, hup.eventually (Iio_mem_nhds hlim)] with ε hε hεden hout hu
    have hεpos : 0 < ε := hε
    let A := Metric.closedBall (0 : Plane) (a / ε)
    let E := Metric.closedBall (0 : Plane) (K / ε)
    have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet
    have hE : MeasurableSet E := Metric.isClosed_closedBall.measurableSet
    have hAE : A ⊆ E := Metric.closedBall_subset_closedBall
      (div_le_div_of_nonneg_right haK hεpos.le)
    have hiE : IntegrableOn (fun ξ => ‖m (ε • ξ)‖ ^ 2) E ν :=
      ((hm.comp (continuous_const_smul ε)).norm.pow 2).locallyIntegrable.integrableOn_isCompact
        (isCompact_closedBall _ _)
    have hi : Integrable (fun ξ => ‖m (ε • ξ)‖ ^ 2) ν := by
      have hh := hiE.union hout.1
      simpa only [E, Set.union_compl_self, integrableOn_univ] using hh
    have hsplit : (∫ ξ, ‖m (ε • ξ)‖ ^ 2 ∂ν) =
        (∫ ξ in A, ‖m (ε • ξ)‖ ^ 2 ∂ν) + mid ε +
        (∫ ξ in Eᶜ, ‖m (ε • ξ)‖ ^ 2 ∂ν) := by
      dsimp [mid]
      rw [setIntegral_sdiff hA hiE hAE]
      linarith [integral_add_compl hE hi]
    have hinner := spectral_inner_integral_bound ν m hm hεpos hMpos.le hlocal
    have hbound : (∫ ξ, ‖m (ε • ξ)‖ ^ 2 ∂ν) / Real.log (Real.log ε⁻¹) ≤
        M ^ 2 * (specMass ν (a / ε) / Real.log (Real.log ε⁻¹)) +
        mid ε / Real.log (Real.log ε⁻¹) +
        (C / K ^ 2) * (specMass ν (K / ε) / Real.log (Real.log ε⁻¹)) := by
      rw [hsplit]
      have hh := div_le_div_of_nonneg_right
        (add_le_add (add_le_add hinner (le_refl (mid ε))) hout.2) hεden.le
      simpa only [A, E, add_div, mul_div_assoc] using hh
    exact hbound.trans_lt hu

/-- The deterministic assertion of the shape lemma for a Schwartz function. -/
theorem shape_comparison (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    (m : SchwartzMap Plane ℂ) (hm : m 0 = 0) :
    Tendsto (fun ε : ℝ => (∫ ξ, ‖m (ε • ξ)‖ ^ 2 ∂ν) /
      Real.log (Real.log ε⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  apply shape_comparison_of_decay ν hball m m.continuous hm
    (apply_nonneg (SchwartzMap.seminorm ℝ 1 0) m)
    (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) m)
  · intro z
    simpa only [pow_one] using m.norm_pow_mul_le_seminorm ℝ 1 z
  · exact m.norm_le_seminorm ℝ

end Critical2DKPZ.Extensions.ScaleLimit
