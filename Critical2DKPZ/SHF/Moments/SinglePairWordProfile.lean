/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Interior limits for the two-particle future profile -/

@[expose] public section

noncomputable section

open Filter
open MeasureTheory
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

open DeltaBose


/-- The continuum spatial profile of a future two-particle block at remaining time
`q`, with the renewal gap time fixed at `v`. -/
def pairTwoFutureSpatialProfile (θ q v : ℝ) (x : Plane)
    (y : Fin 2 → Plane) : ℝ :=
  DeltaBose.scalarDensity θ v *
    ∫ w : Plane, heatKernel (v / 2) (w - x) *
      (heatKernel (q - v) (y 0 - w) * heatKernel (q - v) (y 1 - w))

/-- Factoring the terminal pair and convolving its center Gaussian gives the
future two-particle profile as a gap heat kernel times a center heat kernel. -/
theorem pairTwoFutureSpatialProfile_eq_centerGap
    {θ q v : ℝ} (hv : 0 < v) (hvq : v < q)
    (x : Plane) (y : Fin 2 → Plane) :
    pairTwoFutureSpatialProfile θ q v x y =
      DeltaBose.scalarDensity θ v *
        (heatKernel (2 * (q - v)) (y 1 - y 0) *
          heatKernel (q / 2) ((1 / 2 : ℝ) • (y 0 + y 1) - x)) := by
  have hqv : 0 < q - v := by linarith
  have htimes : 0 < v / 2 := by positivity
  have hhalf : 0 < (q - v) / 2 := by positivity
  have hconvolution :
      (∫ w : Plane, heatKernel (v / 2) (w - x) *
        heatKernel ((q - v) / 2) (w - (1 / 2 : ℝ) • (y 0 + y 1))) =
        heatKernel (q / 2) ((1 / 2 : ℝ) • (y 0 + y 1) - x) := by
    let c : Plane := (1 / 2 : ℝ) • (y 0 + y 1)
    let f : Plane → ℝ := fun z =>
      heatKernel (v / 2) z * heatKernel ((q - v) / 2) ((c - x) - z)
    have hfun : (fun w : Plane =>
        heatKernel (v / 2) (w - x) *
          heatKernel ((q - v) / 2) (w - c)) =
        f ∘ (fun w : Plane => w - x) := by
      funext w
      simp only [Function.comp_apply, f]
      rw [show (c - x) - (w - x) = -(w - c) by abel,
        Critical2DKPZ.heatKernel_neg]
    calc
      _ = ∫ z : Plane, f z := by
        rw [hfun]
        exact integral_sub_right_eq_self f x
      _ = heatKernel (v / 2 + (q - v) / 2) (c - x) := by
        change (∫ z : Plane, heatKernel (v / 2) z *
          heatKernel ((q - v) / 2) ((c - x) - z)) = _
        exact Critical2DKPZ.integral_heatKernel_mul_sub htimes hhalf (c - x)
      _ = heatKernel (q / 2) ((1 / 2 : ℝ) • (y 0 + y 1) - x) := by
        rw [show v / 2 + (q - v) / 2 = q / 2 by ring]
  have hfactor (w : Plane) :
      heatKernel (q - v) (y 0 - w) * heatKernel (q - v) (y 1 - w) =
        heatKernel (2 * (q - v)) (y 1 - y 0) *
          heatKernel ((q - v) / 2)
            (w - (1 / 2 : ℝ) • (y 0 + y 1)) := by
    have h0 : heatKernel (q - v) (y 0 - w) =
        heatKernel (q - v) (w - y 0) := by
      rw [show y 0 - w = -(w - y 0) by abel,
        Critical2DKPZ.heatKernel_neg]
    have h1 : heatKernel (q - v) (y 1 - w) =
        heatKernel (q - v) (w - y 1) := by
      rw [show y 1 - w = -(w - y 1) by abel,
        Critical2DKPZ.heatKernel_neg]
    rw [h0, h1]
    exact heatKernel_product_center_factorization hqv (y 0) (y 1) w
  unfold pairTwoFutureSpatialProfile
  rw [show (fun w : Plane => heatKernel (v / 2) (w - x) *
      (heatKernel (q - v) (y 0 - w) * heatKernel (q - v) (y 1 - w)) ) =
      fun w => heatKernel (2 * (q - v)) (y 1 - y 0) *
        (heatKernel (v / 2) (w - x) *
          heatKernel ((q - v) / 2)
            (w - (1 / 2 : ℝ) • (y 0 + y 1))) by
        funext w
        rw [hfactor w]
        ring]
  rw [integral_const_mul, hconvolution]





end Critical2DKPZ.SHF.Moments

end
