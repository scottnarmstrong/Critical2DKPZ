/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-! # Reversal of an ordered pair of collision times -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The ordered time integral as one planar integral on its open triangle. -/
theorem lintegral_orderedPair_eq (h : ℝ) {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, F r u) =
      ∫⁻ p : ℝ × ℝ, {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < h}.indicator
        (Function.uncurry F) p := by
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < h} := by
    measurability
  change (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, F r u) =
    ∫⁻ p : ℝ × ℝ, {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < h}.indicator
      (Function.uncurry F) p ∂(volume.prod volume)
  rw [lintegral_prod _ (hF.indicator hs).aemeasurable, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioo 0 h
  · rw [indicator_of_mem hr, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ Ioo r h
    · simp only [indicator_of_mem hu, indicator_of_mem (show (r, u) ∈
        {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < h} from ⟨hr.1, hu⟩), Function.uncurry_apply_pair]
    · rw [indicator_of_notMem hu, indicator_of_notMem]
      exact fun hp => hu hp.2
  · rw [indicator_of_notMem hr]
    have hz : (fun u : ℝ => {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < h}.indicator
        (Function.uncurry F) (r, u)) = fun _ => 0 := by
      funext u
      apply indicator_of_notMem
      exact fun hp => hr ⟨hp.1, hp.2.1.trans hp.2.2⟩
    rw [hz, lintegral_zero]

/-- Reversing both ordered times preserves the time simplex and its volume. -/
theorem lintegral_orderedPair_reverse (h : ℝ) {F : ℝ → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, F r u) =
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, F (h - u) (h - r) := by
  let τ : ℝ × ℝ → ℝ × ℝ := fun p => (h - p.2, h - p.1)
  have hτ : MeasurePreserving τ (volume : Measure (ℝ × ℝ)) volume :=
    ((volume.measurePreserving_sub_left h).prod
      (volume.measurePreserving_sub_left h)).comp (Measure.measurePreserving_swap)
  have hmτ : Measurable τ := hτ.measurable
  let S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < h}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hmem (p : ℝ × ℝ) : τ p ∈ S ↔ p ∈ S := by
    dsimp [τ, S]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by linarith only [h3], by linarith only [h2], by linarith only [h1]⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by linarith only [h3], by linarith only [h2], by linarith only [h1]⟩
  have hrev : Measurable (Function.uncurry (fun r u => F (h - u) (h - r))) := hF.comp hmτ
  rw [lintegral_orderedPair_eq h hF, lintegral_orderedPair_eq h hrev]
  have he := hτ.lintegral_comp (hF.indicator hS)
  change (∫⁻ p : ℝ × ℝ, S.indicator (Function.uncurry F) p) =
    ∫⁻ p : ℝ × ℝ, S.indicator (fun p => F (h - p.2) (h - p.1)) p
  rw [← he]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ S
  · rw [indicator_of_mem hp, indicator_of_mem ((hmem p).mpr hp)]
    rfl
  · rw [indicator_of_notMem hp, indicator_of_notMem (mt (hmem p).mp hp)]

end Critical2DKPZ.DeltaBose
