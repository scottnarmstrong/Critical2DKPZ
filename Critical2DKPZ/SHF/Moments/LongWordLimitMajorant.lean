/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitDiagonal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-! # Locally integrable majorants for the first collision diagonal -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- An inverse pair distance has an integrable nonnegative majorant on every
compact configuration box. The value on the null pair diagonal is irrelevant. -/
theorem exists_integrable_configuration_inverse_gap_majorant {h : ℕ}
    (α : CollisionPair h) (R : ℝ) (_hR : 0 ≤ R) :
    ∃ B : Configuration h → ℝ, Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ x, (∀ i, ‖x i‖ ≤ R) →
        ‖x α.1.2 - x α.1.1‖⁻¹ ≤ B x := by
  cases h with
  | zero => exact Fin.elim0 α.1.1
  | succ h =>
    classical
    let K := Metric.closedBall (0 : Plane) (2 * R + 1)
    let g : Plane → ℝ := K.indicator (fun y : Plane => ‖y‖⁻¹)
    have hKm : MeasurableSet K := measurableSet_closedBall
    have hgm : Measurable g := measurable_norm.inv.indicator hKm
    have hg0 (y : Plane) : 0 ≤ g y := Set.indicator_nonneg (fun _ _ => by positivity) y
    have hloc : LocallyIntegrable (fun y : Plane => ‖y‖⁻¹) := by
      apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
        (by simp [Plane]) (by simp [Plane])
      · filter_upwards [] with y
        simp only [Real.norm_eq_abs, abs_inv, abs_norm, one_mul, Real.rpow_neg_one]
        exact le_rfl
      · exact measurable_norm.inv.aestronglyMeasurable
    have hg : Integrable g :=
      (hloc.integrableOn_isCompact (isCompact_closedBall (0 : Plane) (2 * R + 1))).integrable_indicator hKm
    let χ : Plane → ℝ := (Metric.closedBall (0 : Plane) R).indicator (fun _ => (1 : ℝ))
    have hχ : Integrable χ := (integrableOn_const
      (isCompact_closedBall (0 : Plane) R).measure_ne_top).integrable_indicator measurableSet_closedBall
    let F : (Fin h → Plane) → ℝ := fun x => ∏ i, χ (x i)
    have hF : Integrable F := Integrable.fintype_prod (fun _ => hχ)
    have hFm : Measurable F := by
      exact Finset.measurable_prod _ (fun i _ =>
        (measurable_const.indicator measurableSet_closedBall).comp (measurable_pi_apply i))
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (ne_of_lt α.2)
    let H : Plane × (Fin h → Plane) → ℝ := fun p => g (p.1 - p.2 j) * F p.2
    have hHm : Measurable H :=
      (hgm.comp (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).mul
        (hFm.comp measurable_snd)
    have hH : Integrable H := by
      apply (integrable_prod_iff' hHm.aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall fun y => (hg.comp_sub_right (y j)).mul_const (F y)
      · have he (y : Fin h → Plane) :
            (∫ x : Plane, ‖H (x, y)‖) = (∫ x : Plane, ‖g x‖) * ‖F y‖ := by
          simp only [H, norm_mul]
          rw [integral_mul_const]
          congr 1
          exact integral_sub_right_eq_self (fun x : Plane => ‖g x‖) (y j)
        simp_rw [he]
        exact hF.norm.const_mul _
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (h + 1) => Plane) α.1.2
    have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ _
    refine ⟨H ∘ e, (he.integrable_comp hH.aestronglyMeasurable).mpr hH, ?_, ?_⟩
    · intro x
      exact mul_nonneg (hg0 _) (Finset.prod_nonneg fun i _ =>
        Set.indicator_nonneg (fun _ _ => by norm_num) _)
    · intro x hx
      have hgx : x α.1.2 - x α.1.1 ∈ K := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_sub_le _ _).trans (by linarith only [hx α.1.2, hx α.1.1])
      change ‖x α.1.2 - x α.1.1‖⁻¹ ≤ g (x α.1.2 - x (α.1.2.succAbove j)) *
        ∏ i, χ (x (α.1.2.succAbove i))
      rw [hj]
      have hf : (∏ i : Fin h, χ (x (α.1.2.succAbove i))) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        exact Set.indicator_of_mem (by simpa only [Metric.mem_closedBall, dist_zero_right]
          using (hx (α.1.2.succAbove i))) _
      rw [hf, mul_one]
      exact le_of_eq (Set.indicator_of_mem hgx (fun y : Plane => ‖y‖⁻¹)).symm

end Critical2DKPZ.SHF.Moments
