/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabPositiveConnectorForm
import Mathlib.Tactic

/-! # Signed continuum integrals as differences of positive connector forms -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- The two-replica tensor of a scalar two-endpoint connector. -/
def slabConnectorTensorKernel (κ : Plane × Plane → ℝ) (x y : Configuration 2) : ℝ≥0∞ :=
  ∏ i : Fin 2, ENNReal.ofReal (κ (x i, y i))

/-- Measurability of the scalar connector passes to its replica tensor. -/
theorem measurable_slabConnectorTensorKernel {κ : Plane × Plane → ℝ} (hκ : Measurable κ) :
    Measurable (Function.uncurry (slabConnectorTensorKernel κ)) := by
  unfold slabConnectorTensorKernel
  apply Finset.measurable_prod
  intro i _
  exact (hκ.comp (f := fun p : Configuration 2 × Configuration 2 => (p.1 i, p.2 i))
    (by fun_prop)).ennreal_ofReal

/-- The positive part of a signed endpoint source factors through the
nonnegative connector tensor, as an identity of positive integrals. -/
theorem lintegral_slabConnector_ofReal (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (Ψ : Configuration 2 → Configuration 2 → ℝ)
    (hΨ : Measurable (Function.uncurry Ψ)) (κ : Plane × Plane → ℝ)
    (hκ : Measurable κ) (hκ0 : ∀ p, 0 ≤ κ p) :
    (∫⁻ z, ENNReal.ofReal (Ψ (z 0).1 (z 1).2 *
      ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i)) ∂slabSeparatedMomentPiMeasure θ a b) =
      slabPositiveConnectorForm θ a b (fun x y => ENNReal.ofReal (Ψ x y))
        (slabConnectorTensorKernel κ) := by
  have hFactor (c : ℝ) (x y : Configuration 2) :
      ENNReal.ofReal (c * ∏ i : Fin 2, κ (x i, y i)) =
        ENNReal.ofReal c * slabConnectorTensorKernel κ x y := by
    rw [mul_comm c, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hκ0 _),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => hκ0 _), mul_comm]
    rfl
  have h := lintegral_slabSeparatedMomentPiMeasure_sourceForm θ ha hb
    (fun x y => ENNReal.ofReal (Ψ x y)) (slabConnectorTensorKernel κ)
    hΨ.ennreal_ofReal (measurable_slabConnectorTensorKernel hκ)
  simpa only [hFactor] using h

/-- Factoring a nonnegative connector separates the positive and negative
parts of the external endpoint test without any signed Fubini interchange. -/
theorem integral_slabConnector_eq_positive_sub_negative (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (Ψ : Configuration 2 → Configuration 2 → ℝ)
    (hΨ : Measurable (Function.uncurry Ψ)) (κ : Plane × Plane → ℝ)
    (hκ : Measurable κ) (hκ0 : ∀ p, 0 ≤ κ p)
    (hInt : Integrable (fun z : Fin 2 → Configuration 2 × Configuration 2 =>
      Ψ (z 0).1 (z 1).2 * ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i))
        (slabSeparatedMomentPiMeasure θ a b)) :
    (∫ z, Ψ (z 0).1 (z 1).2 * (∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i)) ∂
      slabSeparatedMomentPiMeasure θ a b) =
      (slabPositiveConnectorForm θ a b (fun x y => ENNReal.ofReal (Ψ x y))
        (slabConnectorTensorKernel κ)).toReal -
      (slabPositiveConnectorForm θ a b (fun x y => ENNReal.ofReal (-Ψ x y))
        (slabConnectorTensorKernel κ)).toReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt,
    lintegral_slabConnector_ofReal θ ha hb Ψ hΨ κ hκ hκ0]
  have hNeg := lintegral_slabConnector_ofReal θ ha hb (fun x y => -Ψ x y) hΨ.neg κ hκ hκ0
  simp only [neg_mul] at hNeg
  rw [hNeg]

/-- Integrability of the signed connector integral makes its positive
endpoint form finite. Applying this to the negated source handles the negative part. -/
theorem slabPositiveConnectorForm_ofReal_ne_top (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (Ψ : Configuration 2 → Configuration 2 → ℝ)
    (hΨ : Measurable (Function.uncurry Ψ)) (κ : Plane × Plane → ℝ)
    (hκ : Measurable κ) (hκ0 : ∀ p, 0 ≤ κ p)
    (hInt : Integrable (fun z : Fin 2 → Configuration 2 × Configuration 2 =>
      Ψ (z 0).1 (z 1).2 * ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i))
        (slabSeparatedMomentPiMeasure θ a b)) :
    slabPositiveConnectorForm θ a b (fun x y => ENNReal.ofReal (Ψ x y))
      (slabConnectorTensorKernel κ) ≠ ⊤ := by
  rw [← lintegral_slabConnector_ofReal θ ha hb Ψ hΨ κ hκ hκ0]
  have hNorm : (∫⁻ z, ENNReal.ofReal |Ψ (z 0).1 (z 1).2 *
      ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i)| ∂slabSeparatedMomentPiMeasure θ a b) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt.abs
      (Filter.Eventually.of_forall fun z => abs_nonneg _)]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hNorm (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (le_abs_self _))

end Critical2DKPZ.SHF.Flow
end
