/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitKernel
public import Critical2DKPZ.NonGaussian.EndpointLimitConcentration
import Mathlib.Tactic

/-! # Logarithmic linearization of averaged endpoint kernels -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- The spatial average of a terminal pairing of an endpoint kernel. -/
def endpointKernelAverage {Ω : Type*} [MeasurableSpace Ω]
    (K : Kernel (Plane × Ω) Plane) (ρ : Measure Plane) (f : Plane → ℝ) (ω : Ω) : ℝ :=
  ∫ x, (∫ y, f y ∂K (x, ω)) ∂ρ

/-- The logarithmic approximation to an averaged endpoint pairing. -/
def endpointKernelLogApprox {Ω : Type*} [MeasurableSpace Ω]
    (K : Kernel (Plane × Ω) Plane) (ρ : Measure Plane) (e : ℝ)
    (f : Plane → ℝ) (ω : Ω) : ℝ :=
  ∫ x, e⁻¹ * Real.log (1 + e * ∫ y, f y ∂K (x, ω)) ∂ρ

/-- The scalar logarithmic estimate gives a uniform approximation after
spatial averaging, with integrability of both random observables. -/
theorem endpoint_kernel_log_linearization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (K : Kernel (Plane × Ω) Plane) [IsFiniteKernel K]
    (hmass : ∀ q, K q Set.univ ≤ 1) (φ : C_c(Plane, ℝ)) (hφ : ∀ y, |φ y| ≤ 1)
    {e : ℝ} (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    Integrable (endpointKernelAverage K ρ φ) P ∧
      Integrable (endpointKernelLogApprox K ρ e φ) P ∧
      ∀ ω, |endpointKernelAverage K ρ φ ω - endpointKernelLogApprox K ρ e φ ω| ≤ 2 * e := by
  let F : Plane × Ω → ℝ := fun q => ∫ y, φ y ∂K q
  let G : Plane × Ω → ℝ := fun q => e⁻¹ * Real.log (1 + e * F q)
  have hFm : StronglyMeasurable F := φ.continuous.stronglyMeasurable.integral_kernel
  have hFbound (q : Plane × Ω) : |F q| ≤ 1 := by
    have hreal : (K q).real Set.univ ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by simpa only [ENNReal.ofReal_one] using hmass q)
    have hnorm : ∀ᵐ y ∂K q, ‖φ y‖ ≤ 1 :=
      Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hφ y
    simpa only [Real.norm_eq_abs, one_mul] using
      (norm_integral_le_of_norm_le_const hnorm).trans (by simpa only [one_mul] using hreal)
  have hGm : StronglyMeasurable G := by
    exact (measurable_const.mul (Real.measurable_log.comp
      (measurable_const.add (measurable_const.mul hFm.measurable)))).stronglyMeasurable
  have herr (q : Plane × Ω) : |G q - F q| ≤ 2 * e :=
    abs_inv_mul_log_one_add_sub_le he hehalf (hFbound q)
  have hGbound (q : Plane × Ω) : |G q| ≤ 2 := by
    have h := abs_sub_le (G q) (F q) 0
    simp only [sub_zero] at h
    linarith only [h, herr q, hFbound q, hehalf]
  have hFi : Integrable F (ρ.prod P) := Integrable.of_bound hFm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hFbound q)
  have hGi : Integrable G (ρ.prod P) := Integrable.of_bound hGm.aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hGbound q)
  refine ⟨hFi.integral_prod_right, hGi.integral_prod_right, ?_⟩
  intro ω
  have hFx : Integrable (fun x => F (x, ω)) ρ := Integrable.of_bound
    (hFm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hFbound (x, ω))
  have hGx : Integrable (fun x => G (x, ω)) ρ := Integrable.of_bound
    (hGm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hGbound (x, ω))
  change |(∫ x, F (x, ω) ∂ρ) - ∫ x, G (x, ω) ∂ρ| ≤ 2 * e
  rw [← integral_sub hFx hGx, ← Real.norm_eq_abs]
  have hnorm : ∀ᵐ x ∂ρ, ‖F (x, ω) - G (x, ω)‖ ≤ 2 * e := by
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_sub_comm] using herr (x, ω)
  simpa using norm_integral_le_of_norm_le_const hnorm

end Critical2DKPZ.NonGaussian
