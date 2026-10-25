/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.KernelMeasureUniqueness
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Positive tests of configuration kernel measures

Tensor integration and rectangle indicators connect the positive moment
formulas to equality of the actual measures.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Integration of endpoint factors against the kernel measure is the literal kernel form. -/
theorem lintegral_kernelMeasure_mul {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f g : Configuration n → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ q, f q.1 * g q.2 ∂volume.withDensity (Function.uncurry K)) =
      ∫⁻ x, ∫⁻ y, f x * K x y * g y := by
  have hm := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [lintegral_withDensity_eq_lintegral_mul _ hK (g := fun q => f q.1 * g q.2) hm]
  change (∫⁻ q : Configuration n × Configuration n, K q.1 q.2 * (f q.1 * g q.2)
    ∂(volume.prod volume)) = _
  rw [lintegral_prod (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n)))
    (fun q => K q.1 q.2 * (f q.1 * g q.2)) (hK.mul hm).aemeasurable]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

/-- Configuration rectangle masses are the positive tensor tests of coordinate indicators. -/
theorem measure_configurationRectangle_eq_lintegral_tensor {n : ℕ}
    (μ : Measure (Configuration n × Configuration n)) (A B : Fin n → Set Plane)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    μ ((univ.pi A) ×ˢ (univ.pi B)) =
      ∫⁻ q, (∏ i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) (q.1 i)) *
        ∏ i, (B i).indicator (fun _ => (1 : ℝ≥0∞)) (q.2 i) ∂μ := by
  have hAm : MeasurableSet (univ.pi A) := MeasurableSet.pi (Set.to_countable univ) (fun i _ => hA i)
  have hBm : MeasurableSet (univ.pi B) := MeasurableSet.pi (Set.to_countable univ) (fun i _ => hB i)
  rw [← lintegral_indicator_one (hAm.prod hBm)]
  apply lintegral_congr
  intro q
  have ha : (univ.pi A).indicator (1 : Configuration n → ℝ≥0∞) q.1 =
      ∏ i, (A i).indicator 1 (q.1 i) := by
    simpa only [Finset.coe_univ] using
      (Set.indicator_pi_one_apply (M₀ := ℝ≥0∞) Finset.univ A q.1)
  have hb : (univ.pi B).indicator (1 : Configuration n → ℝ≥0∞) q.2 =
      ∏ i, (B i).indicator 1 (q.2 i) := by
    simpa only [Finset.coe_univ] using
      (Set.indicator_pi_one_apply (M₀ := ℝ≥0∞) Finset.univ B q.2)
  change (univ.pi A ×ˢ univ.pi B).indicator (1 : Configuration n × Configuration n → ℝ≥0∞)
    (q.1, q.2) = (∏ i, (A i).indicator 1 (q.1 i)) * ∏ i, (B i).indicator 1 (q.2 i)
  rw [Set.indicator_prod_one, ha, hb]

end Critical2DKPZ.SHF.Tsai

end
