/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.SHF.Tsai.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Endpoint products of measures

The smoothed product is a weighted product measure pushed to its two outer endpoints.
Its integral formula and absolute-integrability criterion are valid before imposing
any stochastic-flow axioms. The chain convention has `k + 1` input measures at index `k`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The endpoint product: retain the two outer variables of the weighted product measure. -/
def smoothedProductMeasure (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) : Measure (Plane × Plane) :=
  ((μ.prod ν).withDensity fun q => ENNReal.ofReal (w (q.1.2 - q.2.1))).map fun q => (q.1.1, q.2.2)

/-- A chain with `k` connectors and `k + 1` input measures. -/
def chainProduct (μ : ℕ → Measure (Plane × Plane)) (w : ℕ → Plane → ℝ) :
    ℕ → Measure (Plane × Plane)
  | 0 => μ 0
  | k + 1 => smoothedProductMeasure (chainProduct μ w k) (w k) (μ (k + 1))

/-- The positive integral of an endpoint product is the weighted integral on all four variables. -/
theorem lintegral_smoothedProductMeasure (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) (hw : Measurable w)
    (f : Plane × Plane → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f p ∂smoothedProductMeasure μ w ν =
      ∫⁻ q, ENNReal.ofReal (w (q.1.2 - q.2.1)) * f (q.1.1, q.2.2) ∂(μ.prod ν) := by
  rw [smoothedProductMeasure, lintegral_map hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

/-- The Bochner integral against a smoothed endpoint product equals the weighted integral against the product of its factors; `integrable_smoothedProductMeasure_iff` characterizes integrability of both expressions. -/
theorem integral_smoothedProductMeasure_eq (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (f : Plane × Plane → ℝ) (hf : Measurable f) :
    ∫ p, f p ∂smoothedProductMeasure μ w ν =
      ∫ q, f (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(μ.prod ν) := by
  rw [smoothedProductMeasure, integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by
      filter_upwards with q
      exact ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with q
  rw [ENNReal.toReal_ofReal (hw _), smul_eq_mul, mul_comm]

/-- Absolute convergence of an endpoint pairing is exactly absolute convergence of its defining product. -/
theorem integrable_smoothedProductMeasure_iff (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (f : Plane × Plane → ℝ) (hf : Measurable f) :
    Integrable f (smoothedProductMeasure μ w ν) ↔
      Integrable (fun q => f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) (μ.prod ν) := by
  rw [smoothedProductMeasure, integrable_map_measure hf.aestronglyMeasurable (by fun_prop),
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (by
      filter_upwards with q
      exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw _), smul_eq_mul, mul_comm, Function.comp_def]

/-- The exact endpoint-product pairing identity used in dense-time uniqueness. -/
theorem integral_smoothedProductMeasure (μ : Measure (Plane × Plane)) (w : Plane → ℝ)
    (ν : Measure (Plane × Plane)) [SigmaFinite μ] [SigmaFinite ν] (hw : ∀ x, 0 ≤ w x)
    (hwm : Measurable w) (f : C_c(Plane × Plane, ℝ)) (hdef : SmoothedProductWellDefined μ w ν) :
    ∫ p, f p ∂(smoothedProductMeasure μ w ν) = smoothedProductPairing μ w ν f := by
  have hfi : Integrable (f : Plane × Plane → ℝ) (smoothedProductMeasure μ w ν) :=
    (integrable_smoothedProductMeasure_iff μ w ν hw hwm f f.continuous.measurable).2 (hdef f)
  unfold smoothedProductPairing
  rw [smoothedProductMeasure, integral_map (by fun_prop) hfi.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by
      filter_upwards with q
      exact ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with q
  rw [ENNReal.toReal_ofReal (hw _), smul_eq_mul, mul_comm]

end Critical2DKPZ.SHF.Tsai

end
