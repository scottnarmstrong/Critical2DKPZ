/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.Tsai.FiniteTranslateAveraging
public import Critical2DKPZ.SHF.Tsai.MollifierOperators
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Square integrability and contraction for planar heat mollifiers

The Gaussian product identity gives integrability of the kernel square.
The normalized heat density is a probability measure. Finite averaging of
spatial translates then proves contraction of the actual heat convolution
on arbitrary `L²` representatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The square of a positive-time planar heat kernel is a constant times a half-time kernel. -/
theorem heatKernel_sq_eq {t : ℝ} (ht : 0 < t) (x : Plane) :
    heatKernel t x ^ 2 = heatKernel (2 * t) 0 * heatKernel (t / 2) x := by
  have h := heatKernel_mul_sub ht ht (0 : Plane) x
  have htime : t * t / (t + t) = t / 2 := by
    field_simp
    ring
  rw [htime] at h
  simpa only [zero_sub, heatKernel_neg, smul_zero, sub_zero, ← two_mul,
    pow_two] using h

/-- The heat-kernel square is integrable at every positive time. -/
theorem integrable_heatKernel_sq {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Plane => heatKernel t x ^ 2) := by
  simp_rw [heatKernel_sq_eq ht]
  exact (integrable_heatKernel (half_pos ht)).const_mul _

/-- Positive-time planar heat kernels belong to spatial `L²`. -/
theorem memLp_heatKernel {t : ℝ} (ht : 0 < t) : MemLp (heatKernel t) 2 :=
  (memLp_two_iff_integrable_sq (continuous_heatKernel t).aestronglyMeasurable).2
    (integrable_heatKernel_sq ht)

/-- The normalized heat density defines a probability measure. -/
theorem isProbabilityMeasure_withDensity_heatKernel {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (volume.withDensity (fun x : Plane => ENNReal.ofReal (heatKernel t x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel ht)
    (Filter.Eventually.of_forall (fun x => heatKernel_nonneg ht.le x)), integral_heatKernel ht,
    ENNReal.ofReal_one]

/-- The actual heat convolution is averaging spatial translates against its normalized density. -/
theorem mollifierAction_heat_eq_integral_withDensity {t : ℝ} (ht : 0 < t)
    (φ : Plane → ℝ) (x : Plane) :
    mollifierAction (heatKernel t) φ x =
      ∫ y, φ (x - y) ∂volume.withDensity (fun y : Plane => ENNReal.ofReal (heatKernel t y)) := by
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_heatKernel t).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg ht.le _), smul_eq_mul]
  have h := integral_sub_left_eq_self (fun y : Plane => heatKernel t (x - y) * φ y) volume x
  simpa only [mollifierAction, sub_sub_cancel] using h.symm

/-- The heat average of a bounded `L²` representative has the same pointwise bound.
The defining convolution row is absolutely integrable. -/
theorem mollifierAction_heat_integrable_norm_le {t : ℝ} (ht : 0 < t)
    (φ : Plane → ℝ) (hφ : MemLp φ 2) (C : ℝ) (hC : ∀ y, ‖φ y‖ ≤ C) (x : Plane) :
    Integrable (fun y => heatKernel t (x - y) * φ y) ∧
      ‖mollifierAction (heatKernel t) φ x‖ ≤ C := by
  refine ⟨integrable_mollifierAction_integrand (memLp_heatKernel ht) hφ x, ?_⟩
  let ν := volume.withDensity (fun y : Plane => ENNReal.ofReal (heatKernel t y))
  let : IsProbabilityMeasure ν := isProbabilityMeasure_withDensity_heatKernel ht
  rw [mollifierAction_heat_eq_integral_withDensity ht φ x]
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (Filter.Eventually.of_forall (fun y => hC (x - y)))
  simpa only [probReal_univ, mul_one] using h

/-- Heat convolution contracts the actual `L²` seminorm on measurable representatives. -/
theorem mollifierAction_heat_memLp_and_eLpNorm_le_of_measurable {t : ℝ} (ht : 0 < t)
    (φ : Plane → ℝ) (hφm : Measurable φ) (hφ : MemLp φ 2) :
    MemLp (mollifierAction (heatKernel t) φ) 2 ∧
      eLpNorm (mollifierAction (heatKernel t) φ) 2 ≤ eLpNorm φ 2 := by
  let ν := volume.withDensity (fun x : Plane => ENNReal.ofReal (heatKernel t x))
  let : IsProbabilityMeasure ν := isProbabilityMeasure_withDensity_heatKernel ht
  have hφneg : MemLp (fun x : Plane => φ (-x)) 2 :=
    hφ.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have havg := memLp_integral_translates_finite ν id measurable_id (fun x => φ (-x))
    (hφm.comp measurable_neg) hφneg
  have heq (x : Plane) : (∫ y, φ (-(y - x)) ∂ν) = mollifierAction (heatKernel t) φ x := by
    simpa only [neg_sub] using (mollifierAction_heat_eq_integral_withDensity ht φ x).symm
  have heqfun : (fun x : Plane => ∫ y, φ (-(id y - x)) ∂ν) = mollifierAction (heatKernel t) φ :=
    funext heq
  rw [heqfun] at havg
  refine ⟨havg.1, ?_⟩
  have hnorm : eLpNorm (fun x : Plane => φ (-x)) 2 = eLpNorm φ 2 := by
    exact eLpNorm_comp_measurePreserving hφ.aestronglyMeasurable (Measure.measurePreserving_neg volume)
  have hs := havg.2.2
  rw [measure_univ, one_pow, one_mul, hnorm] at hs
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).1 hs

/-- Heat convolution is an `L²` contraction on arbitrary `L²` representatives. -/
theorem mollifierAction_heat_memLp_and_eLpNorm_le {t : ℝ} (ht : 0 < t)
    (φ : Plane → ℝ) (hφ : MemLp φ 2) :
    MemLp (mollifierAction (heatKernel t) φ) 2 ∧
      eLpNorm (mollifierAction (heatKernel t) φ) 2 ≤ eLpNorm φ 2 := by
  let ψ := hφ.aestronglyMeasurable.aemeasurable.mk φ
  have hψm : Measurable ψ := hφ.aestronglyMeasurable.aemeasurable.measurable_mk
  have heq : φ =ᵐ[volume] ψ := hφ.aestronglyMeasurable.aemeasurable.ae_eq_mk
  have hψ : MemLp ψ 2 := hφ.ae_eq heq
  have h := mollifierAction_heat_memLp_and_eLpNorm_le_of_measurable ht ψ hψm hψ
  rw [← mollifierAction_congr_ae (heatKernel t) heq, ← eLpNorm_congr_ae heq] at h
  exact h

end Critical2DKPZ.SHF.Tsai

end
