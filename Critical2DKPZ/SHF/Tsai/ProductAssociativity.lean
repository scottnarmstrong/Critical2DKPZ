/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Products
import Mathlib.MeasureTheory.Integral.Prod

/-! # Associativity of the actual smoothed endpoint products

Both bracketings integrate the same three input measures with the same two
connector weights. Tonelli proves equality for positive tests, including
infinite values, and therefore equality of the endpoint measures.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Both bracketings of a three-block smoothed product give the same positive pairing. -/
theorem lintegral_smoothedProductMeasure_assoc
    (μ ν ρ : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] [SFinite ρ]
    (w v : Plane → ℝ) (hw : Measurable w) (hv : Measurable v)
    (H : Plane × Plane → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p, H p ∂smoothedProductMeasure (smoothedProductMeasure μ w ν) v ρ) =
      ∫⁻ p, H p ∂smoothedProductMeasure μ w (smoothedProductMeasure ν v ρ) := by
  let η := smoothedProductMeasure μ w ν
  let ζ := smoothedProductMeasure ν v ρ
  let : SFinite η := by dsimp only [η, smoothedProductMeasure]; infer_instance
  let : SFinite ζ := by dsimp only [ζ, smoothedProductMeasure]; infer_instance
  let G (s : Plane × Plane) := ∫⁻ r, ENNReal.ofReal (v (s.2 - r.1)) * H (s.1, r.2) ∂ρ
  have hV : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ENNReal.ofReal (v (q.1.2 - q.2.1)) * H (q.1.1, q.2.2)) :=
    ((hv.comp (measurable_fst.snd.sub measurable_snd.fst)).ennreal_ofReal).mul
      (hH.comp (measurable_fst.fst.prodMk measurable_snd.snd))
  have hG : Measurable G := hV.lintegral_prod_right'
  have hW : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ENNReal.ofReal (w (q.1.2 - q.2.1)) * G (q.1.1, q.2.2)) :=
    ((hw.comp (measurable_fst.snd.sub measurable_snd.fst)).ennreal_ofReal).mul
      (hG.comp (measurable_fst.fst.prodMk measurable_snd.snd))
  let T (p q r : Plane × Plane) :=
    ENNReal.ofReal (w (p.2 - q.1)) * ENNReal.ofReal (v (q.2 - r.1)) * H (p.1, r.2)
  have hleft : (∫⁻ p, H p ∂smoothedProductMeasure η v ρ) =
      ∫⁻ p, ∫⁻ q, ∫⁻ r, T p q r ∂ρ ∂ν ∂μ := by
    rw [lintegral_smoothedProductMeasure η v ρ hv H hH, lintegral_prod _ hV.aemeasurable]
    change (∫⁻ s, G s ∂η) = _
    rw [lintegral_smoothedProductMeasure μ w ν hw G hG, lintegral_prod _ hW.aemeasurable]
    apply lintegral_congr
    intro p
    apply lintegral_congr
    intro q
    change ENNReal.ofReal (w (p.2 - q.1)) *
      (∫⁻ r, ENNReal.ofReal (v (q.2 - r.1)) * H (p.1, r.2) ∂ρ) = _
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro r
    exact (mul_assoc _ _ _).symm
  have hW' : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      ENNReal.ofReal (w (q.1.2 - q.2.1)) * H (q.1.1, q.2.2)) :=
    ((hw.comp (measurable_fst.snd.sub measurable_snd.fst)).ennreal_ofReal).mul
      (hH.comp (measurable_fst.fst.prodMk measurable_snd.snd))
  have hright : (∫⁻ p, H p ∂smoothedProductMeasure μ w ζ) =
      ∫⁻ p, ∫⁻ q, ∫⁻ r, T p q r ∂ρ ∂ν ∂μ := by
    rw [lintegral_smoothedProductMeasure μ w ζ hw H hH, lintegral_prod _ hW'.aemeasurable]
    apply lintegral_congr
    intro p
    have htest : Measurable (fun s : Plane × Plane => ENNReal.ofReal (w (p.2 - s.1)) * H (p.1, s.2)) :=
      ((hw.comp (measurable_const.sub measurable_fst)).ennreal_ofReal).mul
        (hH.comp (measurable_const.prodMk measurable_snd))
    have hjoint : Measurable (fun s : (Plane × Plane) × (Plane × Plane) =>
        ENNReal.ofReal (v (s.1.2 - s.2.1)) *
          (ENNReal.ofReal (w (p.2 - s.1.1)) * H (p.1, s.2.2))) :=
      ((hv.comp (measurable_fst.snd.sub measurable_snd.fst)).ennreal_ofReal).mul
        (htest.comp (measurable_fst.fst.prodMk measurable_snd.snd))
    rw [lintegral_smoothedProductMeasure ν v ρ hv _ htest, lintegral_prod _ hjoint.aemeasurable]
    apply lintegral_congr
    intro q
    apply lintegral_congr
    intro r
    exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
  exact hleft.trans hright.symm

/-- Associativity holds for the actual endpoint measures, including infinite positive masses. -/
theorem smoothedProductMeasure_assoc
    (μ ν ρ : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] [SFinite ρ]
    (w v : Plane → ℝ) (hw : Measurable w) (hv : Measurable v) :
    smoothedProductMeasure (smoothedProductMeasure μ w ν) v ρ =
      smoothedProductMeasure μ w (smoothedProductMeasure ν v ρ) := by
  apply Measure.ext_of_lintegral
  intro H hH
  exact lintegral_smoothedProductMeasure_assoc μ ν ρ w v hw hv H hH

end Critical2DKPZ.SHF.Tsai

end
