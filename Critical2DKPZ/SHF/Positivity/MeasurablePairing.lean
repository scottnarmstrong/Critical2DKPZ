/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Measurability of integrals against random measures -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Positivity

/-- An integrable real pairing against a measurable random measure is almost surely measurable.
The proof writes the signed integral as the difference of the positive and negative lintegrals. -/
theorem aemeasurable_integral_of_measurable_measure {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] (P : Measure Ω) (μ : Ω → Measure α) (hμ : Measurable μ)
    (f : α → ℝ) (hf : Measurable f)
    (hInt : ∀ᵐ ω ∂P, Integrable f (μ ω)) :
    AEMeasurable (fun ω => ∫ x, f x ∂(μ ω)) P := by
  let Ipos : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, ENNReal.ofReal (f x) ∂(μ ω)
  let Ineg : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ ω)
  have hpos : Measurable Ipos := by
    dsimp [Ipos]
    exact (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf)).comp hμ
  have hneg : Measurable Ineg := by
    dsimp [Ineg]
    exact (Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp hf.neg)).comp hμ
  have hcandidate : Measurable (fun ω => (Ipos ω).toReal - (Ineg ω).toReal) := by
    exact ENNReal.measurable_toReal.comp hpos |>.sub
      (ENNReal.measurable_toReal.comp hneg)
  have hEq : (fun ω => ∫ x, f x ∂(μ ω)) =ᵐ[P]
      (fun ω => (Ipos ω).toReal - (Ineg ω).toReal) := by
    filter_upwards [hInt] with ω hω
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω]
  exact hcandidate.aemeasurable.congr hEq.symm

end Critical2DKPZ.SHF.Positivity

end
