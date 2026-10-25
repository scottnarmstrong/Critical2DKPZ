/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
public import Critical2DKPZ.SHF.DeltaBose.LaplaceFormBounds
import Mathlib.Tactic

/-! # Laplace form bounds for collision paths

For paths without adjacent repeated collision labels, the Laplace form bound is the product of the swapping, collision and endpoint trace bounds. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The Laplace transform of a collision path has a product of the swap and
collision form bounds, followed by the endpoint trace bound. -/
theorem formBound_laplace_pathTimeKernel {n : ℕ} (θ : ℝ) {rate : ℝ}
    (hrate : 1 ≤ rate) (hθ : θ < Real.log rate)
    (α₀ : CollisionPair n) (w : List (CollisionPair n))
    (hw : (α₀ :: w).IsChain (· ≠ ·)) :
    FormBound volume volume
      (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α₀) id))
      ((integratedPotentialRowConstant *
          ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length *
        ENNReal.ofReal ((Real.sqrt rate)⁻¹)) := by
  have hratePos : 0 < rate := lt_of_lt_of_le zero_lt_one hrate
  have hword : collisionListNoAdjacentRepeat (α₀ :: w) :=
    (collisionListNoAdjacentRepeat_iff_isChain (α₀ :: w)).2 hw
  have hK : Measurable (Function.uncurry
      (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α₀) id))) :=
    measurable_laplaceTimeKernel rate
      (measurable_pathTimeKernel θ w (measurable_collisionEmbedding α₀) measurable_id)
  have hEndpoint : laplaceEndpointTraceConstant rate ≤
      ENNReal.ofReal ((Real.sqrt rate)⁻¹) := by
    simpa [laplaceEndpointTraceConstant] using
      (laplaceIncomingTimeMajorant_lintegral_le_inv_sqrt hratePos)
  have hfactor :
      integratedPotentialRowConstant ^ w.length *
          (laplaceCollisionResolventConstant θ rate ^ w.length *
            laplaceEndpointTraceConstant rate) ≤
        (integratedPotentialRowConstant *
          ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length *
          ENNReal.ofReal ((Real.sqrt rate)⁻¹) := by
    calc
      _ = (integratedPotentialRowConstant ^ w.length *
            laplaceCollisionResolventConstant θ rate ^ w.length) *
            laplaceEndpointTraceConstant rate := by
              rw [← mul_assoc]
      _ = (integratedPotentialRowConstant *
            laplaceCollisionResolventConstant θ rate) ^ w.length *
            laplaceEndpointTraceConstant rate := by
              rw [← mul_pow]
      _ ≤ (integratedPotentialRowConstant *
            laplaceCollisionResolventConstant θ rate) ^ w.length *
            ENNReal.ofReal ((Real.sqrt rate)⁻¹) :=
              mul_le_mul' le_rfl hEndpoint
      _ = _ := by rfl
  apply (formBound_iff_l2_sq_le volume volume hK
    ((integratedPotentialRowConstant *
      ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length *
      ENNReal.ofReal ((Real.sqrt rate)⁻¹))).2
  intro f hf
  have hsqRaw := laplacePathSuffix_l2_sq_le hratePos hθ w α₀ hword hf
  have hsq :
      (∫⁻ z : FusedConfiguration α₀,
        (∫⁻ x : Configuration n,
          laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α₀) id) z x * f x) ^
            (2 : ℝ)) ≤
        (integratedPotentialRowConstant ^ w.length *
          (laplaceCollisionResolventConstant θ rate ^ w.length *
            laplaceEndpointTraceConstant rate)) ^ 2 *
          ∫⁻ x : Configuration n, f x ^ 2 := by
    simpa only [ENNReal.rpow_two, mul_assoc] using hsqRaw
  have hfactorSq :
      (integratedPotentialRowConstant ^ w.length *
        (laplaceCollisionResolventConstant θ rate ^ w.length *
          laplaceEndpointTraceConstant rate)) ^ 2 ≤
        ((integratedPotentialRowConstant *
          ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length *
          ENNReal.ofReal ((Real.sqrt rate)⁻¹)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfactor 2
  have hmul :
      (integratedPotentialRowConstant ^ w.length *
        (laplaceCollisionResolventConstant θ rate ^ w.length *
          laplaceEndpointTraceConstant rate)) ^ 2 *
          ∫⁻ x : Configuration n, f x ^ 2 ≤
        ((integratedPotentialRowConstant *
          ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) ^ w.length *
          ENNReal.ofReal ((Real.sqrt rate)⁻¹)) ^ 2 *
          ∫⁻ y : Configuration n, f y ^ (2 : ℝ) := by
    have hInput : (∫⁻ x : Configuration n, f x ^ 2) ≤
        ∫⁻ y : Configuration n, f y ^ (2 : ℝ) := by
      simpa only [ENNReal.rpow_two] using
        (le_refl (∫⁻ x : Configuration n, f x ^ 2))
    exact mul_le_mul' hfactorSq hInput
  exact hsq.trans hmul

end Critical2DKPZ.DeltaBose
