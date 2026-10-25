/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.FormBounds
public import Critical2DKPZ.SHF.DeltaBose.LaplaceEndpointL2
public import Critical2DKPZ.SHF.DeltaBose.CollisionResolvent
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! # Laplace form bounds for the four basic blocks -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The Laplace endpoint trace constant is bounded by the reciprocal square
root rate. -/
theorem laplaceIncomingTimeMajorant_lintegral_le_inv_sqrt {rate : ℝ}
    (hrate : 0 < rate) :
    (∫⁻ t in Ioi (0 : ℝ), laplaceIncomingTimeMajorant rate t) ≤
      ENNReal.ofReal ((Real.sqrt rate)⁻¹) := by
  let f : ℝ → ℝ := fun t =>
    Real.exp (-(rate * t)) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
  let g : ℝ → ℝ := fun t => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(rate * t))
  let C : ℝ := (4 * Real.pi) ^ (-(1 / 2 : ℝ))
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := by
    simpa only [g, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)) one_pos hrate)
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hC : IntegrableOn (fun t => C * g t) (Ioi (0 : ℝ)) := hg.const_mul C
    apply hC.congr_fun
    · intro t ht
      have ht0 : 0 < t := ht
      have hpow : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) =
          (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) := by
        rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring,
          Real.mul_rpow (by positivity) ht0.le]
      dsimp [f, C, g]
      rw [hpow]
      ring
    · exact measurableSet_Ioi
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    exact mul_nonneg (Real.exp_pos _).le
      (Real.rpow_pos_of_pos (by positivity : 0 < 4 * Real.pi * t) _).le
  have hENN (t : ℝ) : laplaceIncomingTimeMajorant rate t = ENNReal.ofReal (f t) := by
    simp only [laplaceIncomingTimeMajorant, f, laplaceTimeWeight]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hvalue :
      (∫⁻ t in Ioi (0 : ℝ), laplaceIncomingTimeMajorant rate t) =
        ENNReal.ofReal (∫ t in Ioi (0 : ℝ), f t) := by
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t) := by
        apply lintegral_congr_ae
        filter_upwards with t
        exact hENN t
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hf hn).symm
  have hIntegral : (∫ t in Ioi (0 : ℝ), f t) =
      (1 / 2) * (Real.sqrt rate)⁻¹ := by
    have hPoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : f t = C * g t := by
      have ht0 : 0 < t := ht
      have hpow : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) =
          (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) := by
        rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring,
          Real.mul_rpow (by positivity) ht0.le]
      simp only [f, g, C]
      rw [hpow]
      ring
    calc
      _ = ∫ t in Ioi (0 : ℝ), C * g t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact hPoint
      _ = C * ∫ t in Ioi (0 : ℝ), g t := integral_const_mul C g
      _ = C * ((1 / rate) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ)) := by
        congr 2
        simpa only [g, show (-(1 / 2 : ℝ)) = (1 / 2 : ℝ) - 1 by norm_num] using
          (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) one_half_pos hrate)
      _ = (1 / 2) * (Real.sqrt rate)⁻¹ := by
        dsimp [C]
        rw [Real.Gamma_one_half_eq, Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi)
          (1 / 2 : ℝ), ← Real.sqrt_eq_rpow (4 * Real.pi),
          ← Real.sqrt_eq_rpow (1 / rate), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
        norm_num
        field_simp
  rw [hvalue, hIntegral]
  apply ENNReal.ofReal_le_ofReal
  have hrroot : 0 < Real.sqrt rate := Real.sqrt_pos.2 hrate
  have hrInv : 0 ≤ (Real.sqrt rate)⁻¹ := inv_nonneg.mpr hrroot.le
  nlinarith

/-- The damped incoming block has an `L²` bilinear form bound. -/
theorem formBound_laplace_incoming {n : ℕ} (α : CollisionPair n)
    {rate : ℝ} (hrate : 0 < rate) :
    FormBound volume volume
      (laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)))
      (ENNReal.ofReal ((Real.sqrt rate)⁻¹)) := by
  have hK : Measurable (Function.uncurry
      (laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)))) :=
    measurable_laplaceTimeKernel rate
      (measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α))
  have hE := laplaceIncomingTimeMajorant_lintegral_le_inv_sqrt hrate
  apply (formBound_iff_l2_sq_le volume volume hK
    (ENNReal.ofReal ((Real.sqrt rate)⁻¹))).2
  intro f hf
  have hsq :
      (∫⁻ x : Configuration n,
        (∫⁻ z : FusedConfiguration α,
          laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)) x z * f z) ^ 2) ≤
        (ENNReal.ofReal ((Real.sqrt rate)⁻¹)) ^ 2 *
          ∫⁻ z : FusedConfiguration α, f z ^ 2 := by
    calc
      (∫⁻ x : Configuration n,
          (∫⁻ z : FusedConfiguration α,
            laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)) x z * f z) ^ 2) ≤
          (∫⁻ t in Ioi (0 : ℝ), laplaceIncomingTimeMajorant rate t) ^ 2 *
            ∫⁻ z : FusedConfiguration α, f z ^ 2 :=
        laplaceTimeKernel_incoming_adjoint_l2_sq_le α rate hf
      _ ≤ (ENNReal.ofReal ((Real.sqrt rate)⁻¹)) ^ 2 *
            ∫⁻ z : FusedConfiguration α, f z ^ 2 := by
        exact mul_le_mul' (pow_le_pow_left₀ (by positivity) hE 2) le_rfl
  simpa only [ENNReal.rpow_two] using hsq


/-- A damped swapping block has the integrated Schur form bound. -/
theorem formBound_laplace_swapping {n : ℕ} (α β : CollisionPair n)
    (hne : α ≠ β) {rate : ℝ} (hrate : 0 ≤ rate) :
    FormBound volume volume
      (laplaceTimeKernel rate
        (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)))
      integratedPotentialRowConstant := by
  have hK : Measurable (Function.uncurry
      (laplaceTimeKernel rate
        (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)))) :=
    measurable_laplaceTimeKernel rate
      (measurable_freeTimeKernel (measurable_collisionEmbedding α)
        (measurable_collisionEmbedding β))
  apply (formBound_iff_l2_sq_le volume volume hK
    integratedPotentialRowConstant).2
  intro f hf
  simpa only [ENNReal.rpow_two] using
    (laplaceTimeKernel_swapping_l2_sq_le α β hne hrate hf)

/-- A damped repeated-collision block has its scalar resolvent form bound. -/
theorem formBound_laplace_collision {n : ℕ} (α : CollisionPair n)
    {θ rate : ℝ} (hrate : 0 < rate) (hθ : θ < Real.log rate) :
    FormBound volume volume
      (laplaceTimeKernel rate (collisionTimeKernel α θ))
      (ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹)) := by
  have hK : Measurable (Function.uncurry
      (laplaceTimeKernel rate (collisionTimeKernel α θ))) :=
    measurable_laplaceTimeKernel rate (measurable_collisionTimeKernel α θ)
  apply (formBound_iff_l2_sq_le volume volume hK
    (ENNReal.ofReal (4 * Real.pi * (Real.log rate - θ)⁻¹))).2
  intro f hf
  simpa only [laplaceTimeKernel_collisionTimeKernel, ENNReal.rpow_two] using
    (collisionResolvent_l2_sq_le α hrate hθ hf)

end Critical2DKPZ.DeltaBose
