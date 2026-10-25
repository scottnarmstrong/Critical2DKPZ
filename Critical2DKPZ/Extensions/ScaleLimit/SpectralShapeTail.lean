/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralShapeParts
import Critical2DKPZ.CovarianceKernel.RadialInversion
import Critical2DKPZ.CovarianceKernel.RadialAsymptotic

/-! # Exterior energy bounds using the radial layer-cake estimate -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The quadratic radial envelope is dominated by an inverse square root envelope. -/
theorem quadratic_ratio_le_sqrt_ratio {S t : ℝ} (hS : 0 < S) (ht : S ≤ t) :
    (S / t) ^ 2 ≤ Real.sqrt S / Real.sqrt t := by
  have htpos : 0 < t := hS.trans_le ht
  have hq : 0 ≤ S / t := div_nonneg hS.le htpos.le
  have hq1 : S / t ≤ 1 := (div_le_one htpos).mpr ht
  have hsq : (S / t) ^ 2 ≤ S / t := by nlinarith
  calc
    (S / t) ^ 2 ≤ S / t := hsq
    _ ≤ Real.sqrt (S / t) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt S / Real.sqrt t := Real.sqrt_div hS.le _

/-- A quadratic envelope outside a ball has energy controlled by its spectral mass.
The radial layer-cake estimate supplies the summation over all exterior scales. -/
theorem spectral_exterior_integral_bound (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    {A S C : ℝ} (hA : 0 ≤ A) (hS : 1 ≤ S) (hC : 0 ≤ C)
    (hgrowth : ∀ R : ℝ, 1 ≤ R →
      specMass ν R ≤ A * (1 + Real.log R))
    (hdilation : ∀ u : ℝ, 1 ≤ u →
      specMass ν (S * u) ≤ A * (1 + Real.log u) * specMass ν S)
    (f : Plane → ℝ) (hf : AEStronglyMeasurable f ν) (hn : ∀ ξ, 0 ≤ f ξ)
    (hb : ∀ ξ, S < ‖ξ‖ → f ξ ≤ C * (S / ‖ξ‖) ^ 2) :
    IntegrableOn f (Metric.closedBall (0 : Plane) S)ᶜ ν ∧
      (∫ ξ in (Metric.closedBall (0 : Plane) S)ᶜ, f ξ ∂ν) ≤
        10 * A * C * specMass ν S := by
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.mpr hSpos
  obtain ⟨hi, hib⟩ := CovarianceKernel.integrable_inverseSqrtTailAbove_integral_bound
    ν hA hS hgrowth hdilation
  let E := (Metric.closedBall (0 : Plane) S)ᶜ
  have hE : MeasurableSet E := Metric.isClosed_closedBall.measurableSet.compl
  have hmajor : ∀ ξ, E.indicator f ξ ≤
      (C * Real.sqrt S) * CovarianceKernel.spectralInverseSqrtTailAbove S ξ := by
    intro ξ
    by_cases hξ : ξ ∈ E
    · have ht : S < ‖ξ‖ := by simpa [E, mem_closedBall_zero_iff] using hξ
      rw [Set.indicator_of_mem hξ]
      have hh := mul_le_mul_of_nonneg_left
        (quadratic_ratio_le_sqrt_ratio hSpos ht.le) hC
      simpa [CovarianceKernel.spectralInverseSqrtTailAbove,
        CovarianceKernel.spectralInverseSqrtTail, ht, hS.trans ht.le, div_eq_mul_inv,
        mul_assoc] using (hb ξ ht).trans hh
    · have ht : ¬ S < ‖ξ‖ := by simpa [E, mem_closedBall_zero_iff] using hξ
      simp [Set.indicator_of_notMem hξ,
        CovarianceKernel.spectralInverseSqrtTailAbove, ht]
  have hiMajor := hi.const_mul (C * Real.sqrt S)
  have hiF : Integrable (E.indicator f) ν := hiMajor.mono'
    (hf.indicator hE) (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ξ _ => hn ξ) _)]
      exact hmajor ξ)
  refine ⟨(integrable_indicator_iff hE).mp hiF, ?_⟩
  calc
    _ = ∫ ξ, E.indicator f ξ ∂ν := (integral_indicator hE).symm
    _ ≤ ∫ ξ, (C * Real.sqrt S) *
        CovarianceKernel.spectralInverseSqrtTailAbove S ξ ∂ν :=
      integral_mono hiF hiMajor hmajor
    _ = (C * Real.sqrt S) *
        ∫ ξ, CovarianceKernel.spectralInverseSqrtTailAbove S ξ ∂ν := integral_const_mul _ _
    _ ≤ (C * Real.sqrt S) * (10 * A * specMass ν S / Real.sqrt S) :=
      mul_le_mul_of_nonneg_left hib (mul_nonneg hC hsqrt.le)
    _ = 10 * A * C * specMass ν S := by field_simp

/-- The two radial growth bounds can be chosen with a common nonnegative constant. -/
theorem specMass_common_log_bounds (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ R : ℝ, 1 ≤ R → specMass ν R ≤ A * (1 + Real.log R)) ∧
      ∀ᶠ S : ℝ in atTop, ∀ u : ℝ, 1 ≤ u →
        specMass ν (S * u) ≤ A * (1 + Real.log u) * specMass ν S := by
  obtain ⟨G, hG, hg⟩ := CovarianceKernel.spectralBallMass_logGrowth_of_tendsto ν hball
  obtain ⟨D, hd⟩ := CovarianceKernel.spectralBallMass_logDilationBound_of_tendsto ν hball
  refine ⟨max G D, hG.trans (le_max_left _ _), ?_, ?_⟩
  · intro R hR
    exact (hg R hR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by linarith [Real.log_nonneg hR]))
  · filter_upwards [hd] with S hS u hu
    exact (hS u hu).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right G D)
        (by linarith [Real.log_nonneg hu])) ENNReal.toReal_nonneg)

/-- A first-order Schwartz decay bound yields a small exterior energy uniformly in
the inverse scaling parameter, with the exterior cutoff fixed first. -/
theorem spectral_outer_energy_bound (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    (m : Plane → ℂ) (hm : Continuous m) {B : ℝ} (hB : 0 ≤ B)
    (hdecay : ∀ z : Plane, ‖z‖ * ‖m z‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        IntegrableOn (fun ξ => ‖m (ε • ξ)‖ ^ 2)
          (Metric.closedBall (0 : Plane) (K / ε))ᶜ ν ∧
        (∫ ξ in (Metric.closedBall (0 : Plane) (K / ε))ᶜ, ‖m (ε • ξ)‖ ^ 2 ∂ν) ≤
          C / K ^ 2 * specMass ν (K / ε) := by
  obtain ⟨A, hA, hg, hd⟩ := specMass_common_log_bounds ν hball
  refine ⟨10 * A * B ^ 2, by positivity, ?_⟩
  intro K hK
  have ht : Tendsto (fun ε : ℝ => K / ε) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hK
  filter_upwards [self_mem_nhdsWithin, ht.eventually_ge_atTop 1, ht.eventually hd]
    with ε hε hS hdS
  have hdec : ∀ ξ, K / ε < ‖ξ‖ →
      ‖m (ε • ξ)‖ ^ 2 ≤ (B ^ 2 / K ^ 2) * ((K / ε) / ‖ξ‖) ^ 2 := by
    intro ξ hξ
    have hεpos : 0 < ε := hε
    have htpos : 0 < ‖ξ‖ := (div_pos hK hεpos).trans hξ
    have hz := hdecay (ε • ξ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos] at hz
    have hdiv : ‖m (ε • ξ)‖ ≤ B / (ε * ‖ξ‖) :=
      (le_div_iff₀ (mul_pos hεpos htpos)).mpr (by simpa only [mul_comm] using hz)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B / (ε * ‖ξ‖))).mpr hdiv
    convert hsq using 1
    field_simp
  obtain ⟨hi, hb⟩ := spectral_exterior_integral_bound ν hA hS
    (by positivity : 0 ≤ B ^ 2 / K ^ 2) hg hdS
    (fun ξ => ‖m (ε • ξ)‖ ^ 2)
    ((hm.comp (continuous_const_smul ε)).norm.pow 2).aestronglyMeasurable
    (fun ξ => sq_nonneg _) hdec
  refine ⟨hi, ?_⟩
  convert hb using 1
  ring

end Critical2DKPZ.Extensions.ScaleLimit
