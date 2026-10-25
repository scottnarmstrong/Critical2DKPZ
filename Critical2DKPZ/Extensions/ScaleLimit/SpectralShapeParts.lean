/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralShapeScale
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Inner frequency estimates for the deterministic shape comparison -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- On an inner ball the spectral energy is bounded by a local supremum times its mass. -/
theorem spectral_inner_integral_bound (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (m : Plane → ℂ) (hm : Continuous m) {ε R M : ℝ} (hε : 0 < ε)
    (hM : 0 ≤ M) (hbound : ∀ z : Plane, ‖z‖ ≤ R → ‖m z‖ ≤ M) :
    (∫ ξ in Metric.closedBall (0 : Plane) (R / ε), ‖m (ε • ξ)‖ ^ 2 ∂ν) ≤
      M ^ 2 * specMass ν (R / ε) := by
  let B := Metric.closedBall (0 : Plane) (R / ε)
  have hB : IsCompact B := isCompact_closedBall _ _
  have hc : Continuous (fun ξ : Plane => ‖m (ε • ξ)‖ ^ 2) :=
    (hm.comp (continuous_const_smul ε)).norm.pow 2
  have hi : IntegrableOn (fun ξ : Plane => ‖m (ε • ξ)‖ ^ 2) B ν :=
    hc.locallyIntegrable.integrableOn_isCompact hB
  have hconst : IntegrableOn (fun _ : Plane => M ^ 2) B ν :=
    integrableOn_const hB.measure_lt_top.ne
  calc
    _ ≤ ∫ _ in B, M ^ 2 ∂ν := by
      apply integral_mono_ae hi hconst
      filter_upwards [ae_restrict_mem hB.measurableSet] with ξ hξ
      have hnorm : ‖ξ‖ ≤ R / ε := mem_closedBall_zero_iff.mp hξ
      have hz : ‖ε • ξ‖ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        simpa only [mul_comm] using (le_div_iff₀ hε).mp hnorm
      exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hbound _ hz)
    _ = M ^ 2 * specMass ν (R / ε) := by
      simp only [setIntegral_const, smul_eq_mul, Measure.real, specMass, mul_comm, B]

/-- The middle frequency energy is bounded by the mass of the rescaled annulus. -/
theorem spectral_middle_integral_bound (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (m : Plane → ℂ) (hm : Continuous m) {ε a b M : ℝ} (hε : 0 < ε)
    (hab : a ≤ b) (hM : 0 ≤ M) (hbound : ∀ z : Plane, ‖m z‖ ≤ M) :
    (∫ ξ in Metric.closedBall (0 : Plane) (b / ε) \ Metric.closedBall 0 (a / ε),
      ‖m (ε • ξ)‖ ^ 2 ∂ν) ≤
      M ^ 2 * (specMass ν (b / ε) - specMass ν (a / ε)) := by
  let B := Metric.closedBall (0 : Plane) (b / ε)
  let A := Metric.closedBall (0 : Plane) (a / ε)
  have hA : IsCompact A := isCompact_closedBall _ _
  have hB : IsCompact B := isCompact_closedBall _ _
  have hAB : A ⊆ B := Metric.closedBall_subset_closedBall
    (div_le_div_of_nonneg_right hab hε.le)
  have hc : Continuous (fun ξ : Plane => ‖m (ε • ξ)‖ ^ 2) :=
    (hm.comp (continuous_const_smul ε)).norm.pow 2
  have hi : IntegrableOn (fun ξ : Plane => ‖m (ε • ξ)‖ ^ 2) (B \ A) ν :=
    (hc.locallyIntegrable.integrableOn_isCompact hB).mono_set Set.sdiff_subset
  have hfinite : ν (B \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top hB.measure_lt_top.ne (measure_mono Set.sdiff_subset)
  have hconst : IntegrableOn (fun _ : Plane => M ^ 2) (B \ A) ν := integrableOn_const hfinite
  calc
    _ ≤ ∫ _ in B \ A, M ^ 2 ∂ν := by
      apply integral_mono_ae hi hconst
      exact Eventually.of_forall fun ξ => (sq_le_sq₀ (norm_nonneg _) hM).mpr (hbound _)
    _ = M ^ 2 * (specMass ν (b / ε) - specMass ν (a / ε)) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real,
        measure_sdiff hAB hA.measurableSet.nullMeasurableSet hA.measure_lt_top.ne,
        ENNReal.toReal_sub_of_le (measure_mono hAB) hB.measure_lt_top.ne]
      exact mul_comm _ _

/-- A fixed middle annulus contributes a vanishing normalized energy. -/
theorem spectral_middle_energy_tendsto (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    (m : Plane → ℂ) (hm : Continuous m) {a b M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hM : 0 ≤ M) (hbound : ∀ z : Plane, ‖m z‖ ≤ M) :
    Tendsto (fun ε : ℝ => (∫ ξ in Metric.closedBall (0 : Plane) (b / ε) \
      Metric.closedBall 0 (a / ε), ‖m (ε • ξ)‖ ^ 2 ∂ν) / Real.log (Real.log ε⁻¹))
      (𝓝[>] 0) (𝓝 0) := by
  have hden : Tendsto (fun ε : ℝ => Real.log (Real.log ε⁻¹)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have hupper := (specMass_scaled_annulus_tendsto ν hball ha hb).const_mul (M ^ 2)
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hupper)
  · filter_upwards [hden.eventually_gt_atTop 0] with ε hε
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) hε.le
  · filter_upwards [self_mem_nhdsWithin, hden.eventually_gt_atTop 0] with ε hε hεden
    have hh := div_le_div_of_nonneg_right
      (spectral_middle_integral_bound ν m hm hε hab hM hbound) hεden.le
    simpa only [mul_div_assoc] using hh

end Critical2DKPZ.Extensions.ScaleLimit
