/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
public import Critical2DKPZ.SHF.DeltaBose.Measurability
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Flow.CollisionTimeOrdering
public import Critical2DKPZ.SHF.Flow.CollisionTimeAction
public import Critical2DKPZ.SHF.Flow.WeightedCollisionAction
public import Critical2DKPZ.SHF.Flow.WeightedDiagramBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The complete two-particle moment kernel on squared L² -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

open Critical2DKPZ.SHF.Flow

private theorem lintegral_swap_restrict {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (A : Set ℝ) (hA : MeasurableSet A) {F : ℝ → X → ℝ≥0∞}
    (hF : Measurable (fun p : ℝ × X => F p.1 p.2)) :
    (∫⁻ x, ∫⁻ t in A, F t x ∂volume ∂μ) =
      ∫⁻ t in A, ∫⁻ x, F t x ∂μ ∂volume := by
  classical
  let G : X × ℝ → ℝ≥0∞ := fun p => if p.2 ∈ A then F p.2 p.1 else 0
  have hG : Measurable G := by
    apply Measurable.ite (measurableSet_preimage measurable_snd hA)
    · exact hF.comp measurable_swap
    · exact measurable_const
  calc
    (∫⁻ x, ∫⁻ t in A, F t x ∂volume ∂μ) =
        ∫⁻ x, ∫⁻ t, G (x, t) ∂volume ∂μ := by
      apply lintegral_congr
      intro x
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro t
      simp [Set.indicator, G]
    _ = ∫⁻ t, ∫⁻ x, G (x, t) ∂μ ∂volume :=
          lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ t in A, ∫⁻ x, F t x ∂μ ∂volume := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ A <;> simp [G, ht, Set.indicator]

/-- Tonelli exchanges the spatial integral with the two ordered times on the
positive-time triangle. -/
theorem lintegral_timeTriangle_configuration_swap {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [SFinite μ] (h : ℝ) {H : ℝ → ℝ → X → ℝ≥0∞}
    (hH : Measurable (fun p : (ℝ × ℝ) × X => H p.1.1 p.1.2 p.2) ) :
    (∫⁻ x, ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, H r u x
        ∂volume ∂volume ∂μ) =
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, ∫⁻ x, H r u x
        ∂μ ∂volume ∂volume := by
  have hSlice : Measurable (fun p : ℝ × X =>
      ∫⁻ u in Ioo p.1 h, H p.1 u p.2) := by
    apply measurable_lintegral_Ioo measurable_fst measurable_const
    have hMap : Measurable (fun p : (ℝ × X) × ℝ => ((p.1.1, p.2), p.1.2)) := by
      fun_prop
    exact hH.comp hMap
  rw [lintegral_swap_restrict μ (Ioo (0 : ℝ) h) measurableSet_Ioo hSlice]
  apply lintegral_congr
  intro r
  have hMap : Measurable (fun p : ℝ × X => ((r, p.1), p.2)) := by fun_prop
  exact lintegral_swap_restrict μ (Ioo r h) measurableSet_Ioo (hH.comp hMap)










end Critical2DKPZ.DeltaBose

end
