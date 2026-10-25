/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic

/-! # Centered normalization of logarithmic products

On the intersection of truncation events, the GT26 logarithmic product equals the appropriately centered and normalized sum, with positive logarithm arguments and integrable expectations. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Errata

/-- GT26's truncated logarithm is zero off the event where its argument lies between one half and three halves. -/
def truncatedLog (a : ℝ) : ℝ :=
  if |a| ≤ (1 / 2 : ℝ) then Real.log (1 + a) else 0

/-- Every measurable truncated logarithm in GT26 is integrable under a probability measure. -/
theorem integrable_truncatedLog {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : Ω → ℝ) (ha : Measurable a) :
    Integrable (fun ω => truncatedLog (a ω)) P := by
  let C : ℝ := |Real.log (1 / 2 : ℝ)| + |Real.log (3 / 2 : ℝ)|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have habs : Measurable (fun ω => |a ω|) := by
    simpa only [Real.norm_eq_abs] using ha.norm
  apply (integrable_const C).mono' ?_ (Filter.Eventually.of_forall ?_)
  · exact ((ha.const_add 1).log.ite
      (measurableSet_le habs measurable_const) measurable_const).aestronglyMeasurable
  · intro ω
    change |truncatedLog (a ω)| ≤ C
    unfold truncatedLog
    split_ifs with h
    · have hab := abs_le.mp h
      have hp : 0 < 1 + a ω := by linarith only [hab.1]
      have hl : Real.log (1 / 2 : ℝ) ≤ Real.log (1 + a ω) :=
        Real.log_le_log (by norm_num) (by linarith only [hab.1])
      have hu : Real.log (1 + a ω) ≤ Real.log (3 / 2 : ℝ) :=
        Real.log_le_log hp (by linarith only [hab.2])
      apply abs_le.mpr
      dsimp [C]
      constructor
      · linarith only [hl, neg_abs_le (Real.log (1 / 2 : ℝ)),
          abs_nonneg (Real.log (3 / 2 : ℝ))]
      · linarith only [hu, le_abs_self (Real.log (3 / 2 : ℝ)),
          abs_nonneg (Real.log (1 / 2 : ℝ))]
    · simpa only [abs_zero] using hC

/-- On GT26's good event, the centered sum divided by the square-root scale equals the shifted log product. -/
theorem normalized_centered_truncatedLog_sum_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] (a : ι → Ω → ℝ) (ha : ∀ i, Measurable (a i))
    {A : ℝ} (hA : 0 < A) (ω : Ω) (hω : ∀ i, |a i ω| ≤ (1 / 2 : ℝ)) :
    let Y := fun i η => truncatedLog (a i η)
    let m := ∑ i, ∫ η, Y i η ∂P
    let f := -2 * m / A - 1
    (∀ i, Integrable (Y i) P) ∧
      0 < ∏ i, (1 + a i ω) ∧
      (∑ i, (Y i ω - ∫ η, Y i η ∂P)) / Real.sqrt A =
        (Real.log (∏ i, (1 + a i ω)) + (1 + f) / 2 * A) / Real.sqrt A := by
  dsimp only
  have hp (i : ι) : 0 < 1 + a i ω := by
    have hi := (abs_le.mp (hω i)).1
    linarith only [hi]
  refine ⟨fun i => integrable_truncatedLog P (a i) (ha i),
    Finset.prod_pos (fun i _ => hp i), ?_⟩
  have hlog := Real.log_prod (s := Finset.univ) (f := fun i => 1 + a i ω)
    (fun i _ => (hp i).ne')
  rw [hlog, Finset.sum_sub_distrib]
  have hY : (∑ i, truncatedLog (a i ω)) = ∑ i, Real.log (1 + a i ω) := by
    apply Finset.sum_congr rfl
    intro i _
    exact ite_eq_left (hω i)
  rw [hY]
  congr 1
  field_simp
  ring

end Critical2DKPZ.Errata
