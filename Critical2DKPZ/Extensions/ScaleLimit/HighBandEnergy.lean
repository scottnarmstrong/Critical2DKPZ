/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandAverageSpectrum
public import Critical2DKPZ.Extensions.ScaleLimit.SpectralShapeTail
import Mathlib.Tactic

/-! # High-frequency remainder energy, uniformly over averaging radii -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Removing the band cutoff is a contraction at each frequency. -/
theorem norm_one_sub_chi_le (ξ : Plane) : ‖1 - (chi ξ : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (chi_bounds ξ).2)]
  linarith only [(chi_bounds ξ).1]

/-- Outside the fine band, the first Schwartz decay bound gives a factor
`(a/r)^2`, uniformly in `r`. The radial layer-cake estimate sums all shells. -/
theorem high_band_energy_bound (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    (m : Plane → ℂ) (hm : Continuous m) {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ ξ, ‖ξ‖ * ‖m ξ‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ r : ℝ, 0 < r →
      Integrable (fun ξ => ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2) ν ∧
      (∫ ξ, ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2 ∂ν) ≤
        C * (a / r) ^ 2 * specMass ν a⁻¹ := by
  obtain ⟨A, hA, hg, hd⟩ := specMass_common_log_bounds ν hball
  refine ⟨10 * A * B ^ 2, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    tendsto_inv_nhdsGT_zero.eventually_ge_atTop 1,
    tendsto_inv_nhdsGT_zero.eventually hd] with a ha hS hdS
  have ha' : 0 < a := ha
  intro r hr
  let f : Plane → ℝ := fun ξ => ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hpoint (ξ : Plane) : ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ≤ ‖m (r • ξ)‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_one_sub_chi_le _) (norm_nonneg _)).trans_eq (one_mul _)
  have hdec (ξ : Plane) (hξ : a⁻¹ < ‖ξ‖) :
      f ξ ≤ (B ^ 2 * (a / r) ^ 2) * (a⁻¹ / ‖ξ‖) ^ 2 := by
    have hn : 0 < ‖ξ‖ := (inv_pos.mpr ha').trans hξ
    have hh := hdecay (r • ξ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hh
    have hdv : ‖m (r • ξ)‖ ≤ B / (r * ‖ξ‖) :=
      (le_div_iff₀ (mul_pos hr hn)).mpr (by simpa only [mul_comm] using hh)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B / (r * ‖ξ‖))).mpr
      ((hpoint ξ).trans hdv)
    change ‖(1 - (chi (a • ξ) : ℂ)) * m (r • ξ)‖ ^ 2 ≤ _
    convert hs using 1
    field_simp
  obtain ⟨hi, hb⟩ := spectral_exterior_integral_bound ν hA hS
    (by positivity : 0 ≤ B ^ 2 * (a / r) ^ 2) hg hdS f hf.aestronglyMeasurable
      (fun _ => sq_nonneg _) hdec
  let E := (Metric.closedBall (0 : Plane) a⁻¹)ᶜ
  have hE : MeasurableSet E := Metric.isClosed_closedBall.measurableSet.compl
  have heq : E.indicator f = f := by
    funext ξ
    by_cases hξ : ξ ∈ E
    · exact Set.indicator_of_mem hξ _
    · have hn : ‖ξ‖ ≤ a⁻¹ := by simpa only [E, Set.mem_compl_iff, not_not,
        mem_closedBall_zero_iff] using hξ
      have hnorm : ‖a • ξ‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha']
        calc
          _ ≤ a * a⁻¹ := mul_le_mul_of_nonneg_left hn ha'.le
          _ = 1 := mul_inv_cancel₀ ha'.ne'
      rw [Set.indicator_of_notMem hξ]
      simp only [f, chi_eq_one hnorm, Complex.ofReal_one, sub_self, zero_mul, norm_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hfi : Integrable f ν := by
    rw [← heq]
    exact (integrable_indicator_iff hE).mpr hi
  refine ⟨hfi, ?_⟩
  have hInt : (∫ ξ, f ξ ∂ν) = ∫ ξ in E, f ξ ∂ν := by
    rw [← integral_indicator hE, heq]
  change (∫ ξ, f ξ ∂ν) ≤ _
  rw [hInt]
  convert hb using 1
  ring

end Critical2DKPZ.Extensions.ScaleLimit
