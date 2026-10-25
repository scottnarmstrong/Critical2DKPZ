/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.Basic
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.KpzRegularizedReversed
import Mathlib.Tactic

/-! # Pointwise time reversal for regularized KPZ fields -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.JointConvergence

/-- Reversing the coordinates of the random measure turns the forward regularized field into
the reversed regularized field, pointwise in the environment. -/
theorem kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (T t δ : ℝ)
    (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) :
    kpzRegularized P Z t δ h₀ x ω =
      kpzRegularizedReversed P
        (fun s t ω => (Z (T - t) (T - s) ω).map Prod.swap)
        (T - t) T δ h₀ x ω := by
  unfold kpzRegularized kpzRegularizedReversed
  have hnum := shfPairing_reverse Z T 0 (t - δ)
    (fun y => Real.exp (h₀ y)) (fun y => heatKernel δ (y - x)) ω
  have hcent := shfPairing_reverse Z T 0 (t - δ)
    (fun _ => 1) (fun y => heatKernel δ y) ω
  have hcentInt :
      (∫ ω', Real.log (shfPairing Z 0 (t - δ) (fun _ => 1)
        (fun y => heatKernel δ y) ω') ∂P) =
      ∫ ω', Real.log (shfPairing
        (fun s t ω' => (Z (T - t) (T - s) ω').map Prod.swap)
        ((T - t) + δ) T (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω'
    exact congrArg Real.log (by
      simpa only [sub_zero, show T - (t - δ) = (T - t) + δ by ring] using
        shfPairing_reverse Z T 0 (t - δ) (fun _ => 1)
          (fun y => heatKernel δ y) ω')
  have hnum' :
      shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y))
        (fun y => heatKernel δ (y - x)) ω =
      shfPairing (fun s t ω => (Z (T - t) (T - s) ω).map Prod.swap)
        ((T - t) + δ) T (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω := by
    simpa only [sub_zero, show T - (t - δ) = (T - t) + δ by ring] using hnum
  rw [hnum', hcentInt]

end Critical2DKPZ.JointConvergence

end
