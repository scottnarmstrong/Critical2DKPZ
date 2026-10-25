/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

/-!
# Derivative convergence for convex functions

Secant slopes squeeze the derivative of a convex function. Pointwise convergence
on a neighborhood therefore implies derivative convergence at each point where
the limiting function is differentiable.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- Pointwise convergence of convex functions controls derivatives at a differentiable limit point. -/
theorem tendsto_derivative_of_convex {F : ℕ → ℝ → ℝ} {D : ℕ → ℝ} {f : ℝ → ℝ}
    {d l x r : ℝ} (hlx : l < x) (hxr : x < r)
    (hconv : ∀ᶠ N : ℕ in atTop, ConvexOn ℝ (Icc l r) (F N))
    (hD : ∀ᶠ N : ℕ in atTop, HasDerivAt (F N) (D N) x)
    (hlim : ∀ y ∈ Icc l r, Tendsto (fun N => F N y) atTop (nhds (f y)))
    (hf : HasDerivAt f d x) : Tendsto D atTop (nhds d) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := Metric.tendsto_nhdsWithin_nhds.mp hf.tendsto_slope (ε / 2) (by positivity)
  let η := min δ (min (x - l) (r - x)) / 2
  have hη : 0 < η := half_pos (lt_min hδ (lt_min (sub_pos.mpr hlx) (sub_pos.mpr hxr)))
  have hηδ : η < δ := (half_lt_self (lt_min hδ
    (lt_min (sub_pos.mpr hlx) (sub_pos.mpr hxr)))).trans_le (min_le_left _ _)
  have hηl : η < x - l := (half_lt_self (lt_min hδ
    (lt_min (sub_pos.mpr hlx) (sub_pos.mpr hxr)))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hηr : η < r - x := (half_lt_self (lt_min hδ
    (lt_min (sub_pos.mpr hlx) (sub_pos.mpr hxr)))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hleft : dist (slope f (x - η) x) d < ε / 2 := by
    rw [slope_comm]
    apply hs (by simp only [mem_compl_iff, mem_singleton_iff]; linarith only [hη])
    simpa only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hη] using hηδ
  have hright : dist (slope f x (x + η)) d < ε / 2 := by
    apply hs (by simp only [mem_compl_iff, mem_singleton_iff]; linarith only [hη])
    simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hη] using hηδ
  have hxm : x - η ∈ Icc l r := ⟨by linarith only [hηl], by linarith only [hη, hxr]⟩
  have hxp : x + η ∈ Icc l r := ⟨by linarith only [hlx, hη], by linarith only [hηr]⟩
  have hx : x ∈ Icc l r := ⟨hlx.le, hxr.le⟩
  have hsl : Tendsto (fun N => slope (F N) (x - η) x) atTop (nhds (slope f (x - η) x)) := by
    simp only [slope_def_field]
    exact ((hlim x hx).sub (hlim _ hxm)).div_const _
  have hsr : Tendsto (fun N => slope (F N) x (x + η)) atTop (nhds (slope f x (x + η))) := by
    simp only [slope_def_field]
    exact ((hlim _ hxp).sub (hlim x hx)).div_const _
  filter_upwards [hconv, hD, Metric.tendsto_nhds.mp hsl (ε / 2) (by positivity),
    Metric.tendsto_nhds.mp hsr (ε / 2) (by positivity)] with N hN hd hl hr
  have hlower := hN.slope_le_of_hasDerivAt hxm hx (by linarith only [hη]) hd
  have hupper := hN.le_slope_of_hasDerivAt hx hxp (by linarith only [hη]) hd
  rw [Real.dist_eq] at hleft hright hl hr ⊢
  rw [abs_lt] at hleft hright hl hr ⊢
  constructor <;> linarith only [hleft.1, hright.2, hl.1, hr.2, hlower, hupper]

end Critical2DKPZ.Renewal

end
