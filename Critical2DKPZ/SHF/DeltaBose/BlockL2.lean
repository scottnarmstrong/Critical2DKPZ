/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CollisionMass
public import Critical2DKPZ.SHF.DeltaBose.SchurTest
import Mathlib.Tactic

/-! # Squared L² bounds for free and repeated-collision kernels

The nonnegative kernel-action estimates hold for arbitrary measurable nonnegative data, and finite input squared integral implies finite output squared integral. -/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The free kernel has mass one also as a nonnegative integral. -/
theorem lintegral_freeKernel_right (n : ℕ) {t : ℝ} (ht : 0 < t) (x : Configuration n) :
    (∫⁻ y : Configuration n, ENNReal.ofReal (freeKernel n t x y)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_freeKernel_right n ht x)
    (Filter.Eventually.of_forall fun y => (freeKernel_pos n ht x y).le),
    integral_freeKernel_right n ht x, ENNReal.ofReal_one]

/-- Tensorized free heat flow is an L² contraction. -/
theorem freeKernel_l2_sq_le (n : ℕ) {t : ℝ} (ht : 0 < t)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n,
      (∫⁻ y : Configuration n, ENNReal.ofReal (freeKernel n t x y) * f y) ^ 2) ≤
      ∫⁻ y : Configuration n, f y ^ 2 := by
  have hK : Measurable (fun p : Configuration n × Configuration n =>
      ENNReal.ofReal (freeKernel n t p.1 p.2)) :=
    ((measurable_freeKernel n).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hrow (x : Configuration n) :
      (∫⁻ y : Configuration n, ENNReal.ofReal (freeKernel n t x y)) ≤ 1 := by
    rw [lintegral_freeKernel_right n ht]
  have hcol (y : Configuration n) :
      (∫⁻ x : Configuration n, ENNReal.ofReal (freeKernel n t x y)) ≤ 1 := by
    simp_rw [freeKernel_symm n t]
    exact hrow y
  simpa only [one_mul] using lintegral_kernel_sq_le volume volume hK hrow hcol hf


/-- The repeated-collision operator has L² norm at most `4π j_θ(t)`. -/
theorem collisionKernel_l2_sq_le {n : ℕ} (α : CollisionPair n) (θ : ℝ) {t : ℝ}
    (ht : 0 < t) {f : FusedConfiguration α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α,
      (∫⁻ w : FusedConfiguration α, ENNReal.ofReal (collisionKernel α θ t z w) * f w) ^ 2) ≤
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) ^ 2 *
        ∫⁻ w : FusedConfiguration α, f w ^ 2 := by
  have hK : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      ENNReal.ofReal (collisionKernel α θ t p.1 p.2)) := by
    have hp : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((θ, t), p)) := measurable_const.prodMk measurable_id
    exact ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  have hrow (z : FusedConfiguration α) :
      (∫⁻ w : FusedConfiguration α, ENNReal.ofReal (collisionKernel α θ t z w)) ≤
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) := by
    rw [lintegral_collisionKernel_right α θ ht]
  have hcol (w : FusedConfiguration α) :
      (∫⁻ z : FusedConfiguration α, ENNReal.ofReal (collisionKernel α θ t z w)) ≤
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ t) := by
    simp_rw [collisionKernel_symm α θ t]
    exact hrow w
  simpa only [pow_two] using lintegral_kernel_sq_le volume volume hK hrow hcol hf

end Critical2DKPZ.DeltaBose
