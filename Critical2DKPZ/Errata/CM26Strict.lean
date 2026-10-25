/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! # Planar weighted heat means

The exponential envelope defining the weighted measure space in CM26 has an infinite planar heat-kernel mean already at envelope index one. -/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Critical2DKPZ.Errata

/-- The printed n=1 envelope has infinite mean for every positive heat time.
Thus finite expectation of its integral cannot justify the printed space
membership. This conclusion concerns the deterministic mean measure; it
makes no assertion that infinite expectation alone implies almost-sure
nonmembership of a random measure. -/
theorem cm26_weighted_heat_mean_strict {t : ℝ} (ht : 0 < t) :
    (∫⁻ x : Plane, ∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel t (y - x) * Real.exp (-‖x‖ + ‖y‖))) = ∞ := by
  let F : Plane → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (heatKernel t z * Real.exp (-‖z‖))
  have hFm : Measurable F := by
    dsimp [F]
    exact ((measurable_heatKernel t).mul (by fun_prop)).ennreal_ofReal
  have hFp (z : Plane) : 0 < F z :=
    ENNReal.ofReal_pos.mpr (mul_pos (heatKernel_pos ht z) (Real.exp_pos _))
  have hvol : volume (Set.univ : Set Plane) = ∞ :=
    measure_univ_of_isAddLeftInvariant volume
  have hFpos : 0 < ∫⁻ z, F z := by
    rw [lintegral_pos_iff_support hFm]
    have hs : Function.support F = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hFp z)
    rw [hs, hvol]
    exact bot_lt_top
  have hlower (x : Plane) : (∫⁻ z, F z) ≤
      ∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (y - x) * Real.exp (-‖x‖ + ‖y‖)) := by
    rw [← lintegral_sub_right_eq_self F x]
    apply lintegral_mono
    intro y
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    have hn : ‖x‖ ≤ ‖y - x‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖y - (y - x)‖ := by congr 1; abel
        _ ≤ ‖y‖ + ‖y - x‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  apply top_unique
  calc
    ∞ = ∫⁻ _x : Plane, ∫⁻ z, F z := by
      rw [lintegral_const, hvol, ENNReal.mul_top (ne_of_gt hFpos)]
    _ ≤ _ := lintegral_mono hlower

end Critical2DKPZ.Errata
