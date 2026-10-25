/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PathApi
import Mathlib.Topology.Algebra.Order.Field

/-! # Positive width clocks and their maximum -/

public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A positive clock forces widths to shrink when their logarithms have the source domain. -/
theorem width_tendsto_zero_of_clock {a : Set.Ioi (0 : ℝ) → ℝ} {s : ℝ}
    (ha : ∀ L, 0 < a L) (haone : ∀ᶠ L in atTop, a L < 1) (hs : 0 < s)
    (hclock : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * Real.log (Real.log (a L)⁻¹)) atTop (𝓝 s)) :
    Tendsto a atTop (𝓝 0) := by
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hraw : Tendsto (fun L => Real.log (Real.log (a L)⁻¹)) atTop atTop := by
    have ht := hL.atTop_mul_pos hs hclock
    apply ht.congr
    intro L
    rw [← mul_assoc, mul_inv_cancel₀ L.property.ne', one_mul]
  have hlog : Tendsto (fun L => Real.log (a L)⁻¹) atTop atTop := by
    apply (Real.tendsto_exp_atTop.comp hraw).congr'
    filter_upwards [haone] with L hLone
    have hpos : 0 < Real.log (a L)⁻¹ := Real.log_pos ((one_lt_inv₀ (ha L)).mpr hLone)
    exact Real.exp_log hpos
  apply (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlog).congr
  intro L
  change Real.exp (-Real.log (a L)⁻¹) = a L
  rw [Real.log_inv, neg_neg, Real.exp_log (ha L)]

/-- Canonical widths shrink at every positive scale time. -/
theorem scaleRadius_tendsto_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => scaleRadius L s) atTop (𝓝 0) := by
  have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hLs : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ) * s) atTop atTop :=
    hL.atTop_mul_const hs
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (Real.tendsto_exp_atTop.comp hLs)

/-- Increasing a nonnegative scale time decreases the width. -/
theorem scaleRadius_antitone {L : ℝ} (hL : 0 ≤ L) : Antitone (scaleRadius L) := by
  intro s t hst
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hL)

/-- The ordinary logarithm domain makes the doubly logarithmic clock antitone. -/
theorem antitoneOn_loglog_inv :
    AntitoneOn (fun a : ℝ => Real.log (Real.log a⁻¹)) (Set.Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  apply Real.log_le_log (Real.log_pos ((one_lt_inv₀ hb.1).mpr hb.2))
  apply Real.log_le_log (inv_pos.mpr hb.1)
  exact (inv_le_inv₀ hb.1 ha.1).mpr hab

/-- The larger width has the smaller clock on the classical logarithm domain. -/
theorem loglog_inv_max {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log (Real.log (max a b)⁻¹) =
      min (Real.log (Real.log a⁻¹)) (Real.log (Real.log b⁻¹)) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_right (antitoneOn_loglog_inv ha hb hab)]
  · rw [max_eq_left hba, min_eq_left (antitoneOn_loglog_inv hb ha hba)]

end Critical2DKPZ.Extensions.ScaleLimit
