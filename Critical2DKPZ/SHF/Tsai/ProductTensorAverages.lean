/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ProductAssociativity
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual tensor pairings after averaging one outer block

Absolute integrability in the actual smoothed product justifies Fubini.
Averaging the outer block produces the spatial test used in the conditional
composition argument; the resulting pairing is integrable as well.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Averaging the initial block gives the same actual tensor pairing and preserves integrability. -/
theorem integral_smoothedProduct_tensor_eq_left_average
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν]
    (w : Plane → ℝ) (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (g g' : Plane → ℝ) (hg : Measurable g) (hg' : Measurable g')
    (hI : Integrable (fun p : Plane × Plane => g p.1 * g' p.2) (smoothedProductMeasure μ w ν)) :
    Integrable (fun q : Plane × Plane => (∫ p, g p.1 * w (p.2 - q.1) ∂μ) * g' q.2) ν ∧
    (∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure μ w ν) =
      ∫ q, (∫ p, g p.1 * w (p.2 - q.1) ∂μ) * g' q.2 ∂ν := by
  have hgm : Measurable (fun p : Plane × Plane => g p.1 * g' p.2) :=
    (hg.comp measurable_fst).mul (hg'.comp measurable_snd)
  have hraw := (integrable_smoothedProductMeasure_iff μ w ν hw hwm _ hgm).1 hI
  have heq (q : Plane × Plane) :
      (∫ p : Plane × Plane, (g p.1 * g' q.2) * w (p.2 - q.1) ∂μ) =
        (∫ p : Plane × Plane, g p.1 * w (p.2 - q.1) ∂μ) * g' q.2 := by
    calc
      _ = ∫ p : Plane × Plane, (g p.1 * w (p.2 - q.1)) * g' q.2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun _ => mul_right_comm _ _ _)
      _ = _ := integral_mul_const _ _
  refine ⟨hraw.integral_prod_right.congr (Filter.Eventually.of_forall heq), ?_⟩
  rw [integral_smoothedProductMeasure_eq μ w ν hw hwm _ hgm, integral_prod_symm _ hraw]
  exact integral_congr_ae (Filter.Eventually.of_forall heq)

/-- Averaging the terminal block gives the same actual tensor pairing and preserves integrability. -/
theorem integral_smoothedProduct_tensor_eq_right_average
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν]
    (w : Plane → ℝ) (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (g g' : Plane → ℝ) (hg : Measurable g) (hg' : Measurable g')
    (hI : Integrable (fun p : Plane × Plane => g p.1 * g' p.2) (smoothedProductMeasure μ w ν)) :
    Integrable (fun p : Plane × Plane => g p.1 * ∫ q, w (p.2 - q.1) * g' q.2 ∂ν) μ ∧
    (∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure μ w ν) =
      ∫ p, g p.1 * (∫ q, w (p.2 - q.1) * g' q.2 ∂ν) ∂μ := by
  have hgm : Measurable (fun p : Plane × Plane => g p.1 * g' p.2) :=
    (hg.comp measurable_fst).mul (hg'.comp measurable_snd)
  have hraw := (integrable_smoothedProductMeasure_iff μ w ν hw hwm _ hgm).1 hI
  have heq (p : Plane × Plane) :
      (∫ q : Plane × Plane, (g p.1 * g' q.2) * w (p.2 - q.1) ∂ν) =
        g p.1 * (∫ q : Plane × Plane, w (p.2 - q.1) * g' q.2 ∂ν) := by
    calc
      _ = ∫ q : Plane × Plane, g p.1 * (w (p.2 - q.1) * g' q.2) ∂ν := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro q
        ring
      _ = _ := integral_const_mul _ _
  refine ⟨hraw.integral_prod_left.congr (Filter.Eventually.of_forall heq), ?_⟩
  rw [integral_smoothedProductMeasure_eq μ w ν hw hwm _ hgm, integral_prod _ hraw]
  exact integral_congr_ae (Filter.Eventually.of_forall heq)

/-- A three-block tensor pairing can be tested on the last two blocks after averaging the first. -/
theorem integral_threeBlock_tensor_eq_left_average
    (μ ν ρ : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] [SFinite ρ]
    (w v : Plane → ℝ) (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hvm : Measurable v)
    (g g' : Plane → ℝ) (hg : Measurable g) (hg' : Measurable g')
    (hI : Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (smoothedProductMeasure (smoothedProductMeasure μ w ν) v ρ)) :
    Integrable (fun q : Plane × Plane => (∫ p, g p.1 * w (p.2 - q.1) ∂μ) * g' q.2)
      (smoothedProductMeasure ν v ρ) ∧
    (∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (smoothedProductMeasure μ w ν) v ρ) =
      ∫ q, (∫ p, g p.1 * w (p.2 - q.1) ∂μ) * g' q.2 ∂smoothedProductMeasure ν v ρ := by
  let : SFinite (smoothedProductMeasure ν v ρ) := by
    dsimp only [smoothedProductMeasure]
    infer_instance
  rw [smoothedProductMeasure_assoc μ ν ρ w v hwm hvm] at hI ⊢
  exact integral_smoothedProduct_tensor_eq_left_average μ (smoothedProductMeasure ν v ρ)
    w hw hwm g g' hg hg' hI

end Critical2DKPZ.SHF.Tsai

end
