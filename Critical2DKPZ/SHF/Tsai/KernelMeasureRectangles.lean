/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Finiteness of kernel measures on finite-volume rectangles

Positive form bounds control the literal kernel measure of a rectangle by
its endpoint indicator tests. This supplies the finiteness needed for measure
uniqueness, before applying any identity to general joint endpoint tests.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A finite positive form bound gives finite kernel mass on finite-volume rectangles. -/
theorem kernelMeasure_rectangle_lt_top {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hF : FormBound volume volume K c) {A B : Set (Configuration n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAv : volume A < ⊤) (hBv : volume B < ⊤) :
    (volume.withDensity (Function.uncurry K)) (A ×ˢ B) < ⊤ := by
  classical
  let f : Configuration n → ℝ≥0∞ := B.indicator (fun _ => 1)
  let g : Configuration n → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  have hg : Measurable g := measurable_const.indicator hA
  have hsquare (S : Set (Configuration n)) (hS : MeasurableSet S) :
      (∫⁻ x, (S.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ)) = volume S := by
    have heq : (fun x => (S.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ)) =
        S.indicator (fun _ => 1) := by
      funext x
      by_cases hx : x ∈ S <;> simp [Set.indicator, hx]
    rw [heq, lintegral_indicator_const hS, one_mul]
  have hfibre (x : Configuration n) : (∫⁻ y, K x y * f y) = ∫⁻ y in B, K x y := by
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ B <;> simp [f, Set.indicator, hy]
  have hleft : (∫⁻ x, g x * ∫⁻ y, K x y * f y) =
      (volume.withDensity (Function.uncurry K)) (A ×ˢ B) := by
    rw [withDensity_apply _ (hA.prod hB)]
    change _ = ∫⁻ q in A ×ˢ B, K q.1 q.2 ∂(volume.prod volume)
    rw [setLIntegral_prod (μ := (volume : Measure (Configuration n)))
      (ν := (volume : Measure (Configuration n))) (s := A) (t := B)
      (fun q => K q.1 q.2) hK.aemeasurable.restrict]
    simp_rw [hfibre]
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ A <;> simp [g, Set.indicator, hx]
  have h := hF f g hf hg
  rw [hleft, show (∫⁻ y, f y ^ (2 : ℝ)) = volume B from hsquare B hB,
    show (∫⁻ x, g x ^ (2 : ℝ)) = volume A from hsquare A hA] at h
  exact h.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hc.lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBv.ne))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAv.ne))

end Critical2DKPZ.SHF.Tsai

end
