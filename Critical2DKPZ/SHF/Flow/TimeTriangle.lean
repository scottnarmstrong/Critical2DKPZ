/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CausalComposition

/-! # Exchanging the positive endpoint and collision durations -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem triangle_indicator_integral (v : ℝ) (H : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ r, ∫⁻ s, if 0 < r ∧ 0 < s ∧ r + s < v then H (r, s) else 0) =
      ∫⁻ r in Ioo 0 v, ∫⁻ s in Ioo 0 (v - r), H (r, s) := by
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioo 0 v
  · rw [indicator_of_mem hr, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro s
    have he : (0 < r ∧ 0 < s ∧ r + s < v) ↔ s ∈ Ioo 0 (v - r) := by
      simp only [mem_Ioo]
      constructor
      · rintro ⟨_, hs, hv⟩
        exact ⟨hs, by linarith⟩
      · rintro ⟨hs, hv⟩
        exact ⟨hr.1, hs, by linarith⟩
    simp only [he, indicator]
  · rw [indicator_of_notMem hr]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with s
    have he : ¬(0 < r ∧ 0 < s ∧ r + s < v) := by
      rintro ⟨hr0, hs, hv⟩
      exact hr ⟨hr0, by linarith⟩
    exact ite_eq_right he

/-- Tonelli on the triangle of positive durations with sum less than `v`. -/
theorem lintegral_timeTriangle_swap (v : ℝ) {H : ℝ × ℝ → ℝ≥0∞}
    (hH : Measurable H) :
    (∫⁻ r in Ioo 0 v, ∫⁻ s in Ioo 0 (v - r), H (r, s)) =
      ∫⁻ s in Ioo 0 v, ∫⁻ r in Ioo 0 (v - s), H (r, s) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      if 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < v then H p else 0) := by
    apply Measurable.ite _ hH measurable_const
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const))
  rw [← triangle_indicator_integral, lintegral_lintegral_swap hm.aemeasurable]
  have he : (fun s r : ℝ =>
      if 0 < r ∧ 0 < s ∧ r + s < v then H (r, s) else 0) =
      fun s r => if 0 < s ∧ 0 < r ∧ s + r < v then H (r, s) else 0 := by
    funext s r
    have hp : (0 < r ∧ 0 < s ∧ r + s < v) ↔ (0 < s ∧ 0 < r ∧ s + r < v) := by
      rw [add_comm r s]
      tauto
    simp only [hp]
  calc
    _ = ∫⁻ s, ∫⁻ r, if 0 < s ∧ 0 < r ∧ s + r < v then H (r, s) else 0 := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro r
      exact congrFun (congrFun he s) r
    _ = _ := triangle_indicator_integral v (fun p => H (p.2, p.1))

end Critical2DKPZ.SHF.Flow

end
