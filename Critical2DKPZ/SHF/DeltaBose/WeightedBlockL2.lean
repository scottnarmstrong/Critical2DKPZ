/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ConfigurationWeight
public import Critical2DKPZ.SHF.DeltaBose.TraceL2
import Mathlib.Tactic

/-! The free and incoming heat blocks satisfy weighted operator bounds with growth `2^n exp(2 n a² t)`. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The common factor `2^n exp(2 n a² t)` in the weighted n-particle heat-kernel comparisons. -/
noncomputable def weightGrowth (n : ℕ) (a t : ℝ) : ℝ :=
  2 ^ n * Real.exp (2 * n * a ^ 2 * t)

/-- The exponential weight-growth factor is strictly positive. -/
theorem weightGrowth_pos (n : ℕ) (a t : ℝ) : 0 < weightGrowth n a t := by
  unfold weightGrowth
  positivity

/-- Incoming comparison uses the ambient weight of the collision embedding. -/
theorem incomingKernel_mul_exp_weight_le {n : ℕ} (α : CollisionPair n) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (z : FusedConfiguration α) (x : Configuration n) :
    incomingKernel α t z x * Real.exp (a * (fusedOneNorm α z - configurationOneNorm x)) ≤
      weightGrowth n a t * incomingKernel α (2 * t) z x := by
  have h := freeKernel_mul_exp_weight_le n ha ht (collisionEmbedding α z) x
  rw [configurationOneNorm_collisionEmbedding] at h
  simpa only [incomingKernel, freeKernel_symm n t x (collisionEmbedding α z),
    freeKernel_symm n (2 * t) x (collisionEmbedding α z), weightGrowth] using h

/-- The adjoint has the opposite weight ratio and the same growth constant. -/
theorem incomingKernel_adjoint_mul_exp_weight_le {n : ℕ} (α : CollisionPair n) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (x : Configuration n) (z : FusedConfiguration α) :
    incomingKernel α t z x * Real.exp (a * (configurationOneNorm x - fusedOneNorm α z)) ≤
      weightGrowth n a t * incomingKernel α (2 * t) z x := by
  have h := freeKernel_mul_exp_weight_le n ha ht x (collisionEmbedding α z)
  simpa only [configurationOneNorm_collisionEmbedding, incomingKernel, weightGrowth] using h

/-- The weighted swapping comparison includes the required exponential time growth. -/
theorem swappingKernel_mul_exp_weight_le {n : ℕ} (α β : CollisionPair n) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (z : FusedConfiguration α) (w : FusedConfiguration β) :
    swappingKernel α β t z w * Real.exp (a * (fusedOneNorm α z - fusedOneNorm β w)) ≤
      weightGrowth n a t * swappingKernel α β (2 * t) z w := by
  simpa only [configurationOneNorm_collisionEmbedding, swappingKernel, weightGrowth] using
    freeKernel_mul_exp_weight_le n ha ht (collisionEmbedding α z) (collisionEmbedding β w)

/-- Exponentially weighted free heat flow satisfies the squared L² kernel-action bound. -/
theorem freeKernel_weighted_l2_sq_le (n : ℕ) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
      ENNReal.ofReal (freeKernel n t x y *
        Real.exp (a * (configurationOneNorm x - configurationOneNorm y))) * f y) ^ 2) ≤
      ENNReal.ofReal (weightGrowth n a t) ^ 2 * ∫⁻ y : Configuration n, f y ^ 2 := by
  have hKL (x y : Configuration n) :
      ENNReal.ofReal (freeKernel n t x y *
        Real.exp (a * (configurationOneNorm x - configurationOneNorm y))) ≤
      ENNReal.ofReal (weightGrowth n a t) * ENNReal.ofReal (freeKernel n (2 * t) x y) := by
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal (freeKernel_mul_exp_weight_le n ha ht x y)
  simpa only [mul_one] using lintegral_kernel_sq_dominate volume volume (D := 1)
    ENNReal.ofReal_ne_top hKL f
      (by simpa only [one_mul] using freeKernel_l2_sq_le n (t := 2 * t) (by positivity) hf)

/-- Weighted incoming trace estimate with its explicit positive-time rate. -/
theorem incomingKernel_weighted_l2_sq_le {n : ℕ} (α : CollisionPair n) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α, (∫⁻ x : Configuration n,
      ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (fusedOneNorm α z - configurationOneNorm x))) * f x) ^ 2) ≤
      ENNReal.ofReal (weightGrowth n a t) ^ 2 * ENNReal.ofReal (4 * Real.pi * (2 * t))⁻¹ *
        ∫⁻ x : Configuration n, f x ^ 2 := by
  have hKL (z : FusedConfiguration α) (x : Configuration n) :
      ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (fusedOneNorm α z - configurationOneNorm x))) ≤
      ENNReal.ofReal (weightGrowth n a t) * ENNReal.ofReal (incomingKernel α (2 * t) z x) := by
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal (incomingKernel_mul_exp_weight_le α ha ht z x)
  exact lintegral_kernel_sq_dominate volume volume ENNReal.ofReal_ne_top hKL f
    (incomingKernel_l2_sq_le α (t := 2 * t) (by positivity) hf)

/-- Weighted adjoint trace estimate. -/
theorem incomingKernel_adjoint_weighted_l2_sq_le {n : ℕ} (α : CollisionPair n) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) {f : FusedConfiguration α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n, (∫⁻ z : FusedConfiguration α,
      ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z))) * f z) ^ 2) ≤
      ENNReal.ofReal (weightGrowth n a t) ^ 2 * ENNReal.ofReal (4 * Real.pi * (2 * t))⁻¹ *
        ∫⁻ z : FusedConfiguration α, f z ^ 2 := by
  have hKL (x : Configuration n) (z : FusedConfiguration α) :
      ENNReal.ofReal (incomingKernel α t z x *
        Real.exp (a * (configurationOneNorm x - fusedOneNorm α z))) ≤
      ENNReal.ofReal (weightGrowth n a t) * ENNReal.ofReal (incomingKernel α (2 * t) z x) := by
    rw [← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    exact ENNReal.ofReal_le_ofReal (incomingKernel_adjoint_mul_exp_weight_le α ha ht x z)
  exact lintegral_kernel_sq_dominate volume volume ENNReal.ofReal_ne_top hKL f
    (incomingKernel_adjoint_l2_sq_le α (t := 2 * t) (by positivity) hf)


end Critical2DKPZ.DeltaBose
