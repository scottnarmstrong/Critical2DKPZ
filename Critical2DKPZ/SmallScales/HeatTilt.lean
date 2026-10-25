/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.GaussianJensen

/-! # Normalizing a measure by a Gaussian heat weight -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace Critical2DKPZ.SmallScales

/-- The heat tilt at the comparison point, normalized by its heat pairing. -/
def heatTilt (μ : Measure Plane) (δ : ℝ) (b : Plane) : Measure Plane :=
  (ENNReal.ofReal (∫ u, heatKernel δ (u - b) ∂μ))⁻¹ •
    μ.withDensity (fun u => ENNReal.ofReal (heatKernel δ (u - b)))

/-- The heat tilt is a probability measure whenever its normalization is finite and positive. -/
theorem isProbabilityMeasure_heatTilt (μ : Measure Plane) {δ : ℝ} (hδ : 0 < δ) (b : Plane)
    (hi : Integrable (fun u => heatKernel δ (u - b)) μ)
    (hp : 0 < ∫ u, heatKernel δ (u - b) ∂μ) :
    IsProbabilityMeasure (heatTilt μ δ b) := by
  constructor
  rw [heatTilt, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun u => (heatKernel_pos hδ _).le))]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.2 hp)) ENNReal.ofReal_ne_top

/-- Integration against the heat tilt is normalized heat-weighted integration. -/
theorem integral_heatTilt (μ : Measure Plane) {δ : ℝ} (hδ : 0 < δ) (b : Plane) (f : Plane → ℝ) :
    (∫ u, f u ∂heatTilt μ δ b) =
      (∫ u, heatKernel δ (u - b) * f u ∂μ) /
        (∫ u, heatKernel δ (u - b) ∂μ) := by
  have hm : Measurable (fun u : Plane => ENNReal.ofReal (heatKernel δ (u - b))) :=
    ((measurable_heatKernel δ).comp (measurable_id.sub_const b)).ennreal_ofReal
  rw [heatTilt, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (heatKernel_pos hδ _).le, smul_eq_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (integral_nonneg
    (fun _ => (heatKernel_pos hδ _).le))]
  ring

/-- The tilted Gaussian ratio has exactly the difference of the two original heat logs. -/
theorem heatRatioLog_heatTilt (μ : Measure Plane) {δ : ℝ} (hδ : 0 < δ) (b y : Plane)
    (hb : 0 < ∫ u, heatKernel δ (u - b) ∂μ)
    (hy : 0 < ∫ u, heatKernel δ (u - y) ∂μ) :
    heatRatioLog (heatTilt μ δ b) δ b y =
      Real.log (∫ u, heatKernel δ (u - y) ∂μ) -
        Real.log (∫ u, heatKernel δ (u - b) ∂μ) := by
  unfold heatRatioLog
  rw [integral_heatTilt μ hδ]
  have heq : (fun u => heatKernel δ (u - b) *
      (heatKernel δ (u - y) / heatKernel δ (u - b))) =
      (fun u => heatKernel δ (u - y)) := by
    funext u
    field_simp [ne_of_gt (heatKernel_pos hδ (u - b))]
  rw [heq, Real.log_div hy.ne' hb.ne']

/-- A finite heat-weighted first moment gives a finite first moment of the tilt. -/
theorem integrable_id_heatTilt (μ : Measure Plane) {δ : ℝ} (hδ : 0 < δ) (b : Plane)
    (hp : 0 < ∫ u, heatKernel δ (u - b) ∂μ)
    (hi : Integrable (fun u : Plane => heatKernel δ (u - b) • u) μ) :
    Integrable (fun u : Plane => u) (heatTilt μ δ b) := by
  apply Integrable.smul_measure (c := (ENNReal.ofReal (∫ u, heatKernel δ (u - b) ∂μ))⁻¹)
    ?_ (ENNReal.inv_ne_top.2 (ne_of_gt (ENNReal.ofReal_pos.2 hp)))
  apply (integrable_withDensity_iff_integrable_smul'
    (f := fun u : Plane => ENNReal.ofReal (heatKernel δ (u - b)))
    (((measurable_heatKernel δ).comp (measurable_id.sub_const b)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  simpa only [ENNReal.toReal_ofReal (heatKernel_pos hδ _).le] using hi

/-- Finiteness of a translated heat pairing supplies the exponential moment of the tilt. -/
theorem integrable_exp_heatTilt (μ : Measure Plane) {δ : ℝ} (hδ : 0 < δ) (b y : Plane)
    (hp : 0 < ∫ u, heatKernel δ (u - b) ∂μ)
    (hi : Integrable (fun u => heatKernel δ (u - y)) μ) :
    Integrable (fun u => Real.exp (inner ℝ (y - b) (u - b) / δ)) (heatTilt μ δ b) := by
  apply Integrable.smul_measure (c := (ENNReal.ofReal (∫ u, heatKernel δ (u - b) ∂μ))⁻¹)
    ?_ (ENNReal.inv_ne_top.2 (ne_of_gt (ENNReal.ofReal_pos.2 hp)))
  apply (integrable_withDensity_iff_integrable_smul'
    (f := fun u : Plane => ENNReal.ofReal (heatKernel δ (u - b)))
    (((measurable_heatKernel δ).comp (measurable_id.sub_const b)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  simp only [ENNReal.toReal_ofReal (heatKernel_pos hδ _).le, smul_eq_mul]
  have heq : (fun u => heatKernel δ (u - b) *
      Real.exp (inner ℝ (y - b) (u - b) / δ)) =
      (fun u => Real.exp (‖y - b‖ ^ 2 / (2 * δ)) * heatKernel δ (u - y)) := by
    funext u
    have hex : Real.exp (inner ℝ (y - b) (u - b) / δ) =
        Real.exp (‖y - b‖ ^ 2 / (2 * δ)) *
          Real.exp (-‖y - b‖ ^ 2 / (2 * δ) + inner ℝ (y - b) (u - b) / δ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hex, ← heatKernel_ratio_eq_exp hδ b y u]
    field_simp [ne_of_gt (heatKernel_pos hδ (u - b))]
  rw [heq]
  exact hi.const_mul _

end Critical2DKPZ.SmallScales
