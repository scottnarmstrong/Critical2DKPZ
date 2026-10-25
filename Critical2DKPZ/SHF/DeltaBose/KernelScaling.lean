/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.VolumeScaling
import Mathlib.Tactic

/-! # Exact parabolic scaling of the positive diagram kernels -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The density Jacobian for an `n`-particle kernel. -/
noncomputable def kernelScaleFactor (a : ℝ) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((a ^ n)⁻¹)

/-- Two time and two fused-coordinate Jacobians cancel two of the three kernel factors. -/
theorem kernelScaleFactor_cancel {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal a * ENNReal.ofReal a * ENNReal.ofReal (a ^ (n - 1)) *
      ENNReal.ofReal (a ^ (n - 1)) * kernelScaleFactor a n ^ 3 = kernelScaleFactor a n := by
  have hp : a * a ^ (n - 1) = a ^ n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have hunit : ENNReal.ofReal a * ENNReal.ofReal (a ^ (n - 1)) * kernelScaleFactor a n = 1 := by
    unfold kernelScaleFactor
    rw [← ENNReal.ofReal_mul ha.le, hp,
      ← ENNReal.ofReal_mul (pow_pos ha _).le, mul_inv_cancel₀ (pow_pos ha _).ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal a * ENNReal.ofReal a * ENNReal.ofReal (a ^ (n - 1)) *
        ENNReal.ofReal (a ^ (n - 1)) * kernelScaleFactor a n ^ 3
      = (ENNReal.ofReal a * ENNReal.ofReal (a ^ (n - 1)) * kernelScaleFactor a n) *
        (ENNReal.ofReal a * ENNReal.ofReal (a ^ (n - 1)) * kernelScaleFactor a n) *
        kernelScaleFactor a n := by simp only [pow_succ, pow_zero]; ac_rfl
    _ = kernelScaleFactor a n := by rw [hunit, one_mul, one_mul]

/-- Scaling of the product of the three factors at a first collision interval. -/
theorem diagramStep_scale {n : ℕ} (α : CollisionPair n) (w : List (CollisionPair n))
    (θ : ℝ) {a r u h : ℝ} (ha : 0 < a) (hru : r < u)
    (x y : Configuration n) (z z' : FusedConfiguration α)
    (hrec : diagramKernel θ w (a * (h - u))
      (fun i => Real.sqrt a • collisionEmbedding α z' i) (fun i => Real.sqrt a • y i) =
      kernelScaleFactor a n * diagramKernel (θ + Real.log a) w (h - u) (collisionEmbedding α z') y) :
    ENNReal.ofReal (incomingKernel α (a * r) (mapFused (fun v => Real.sqrt a • v) z)
      (fun i => Real.sqrt a • x i)) *
      ENNReal.ofReal (collisionKernel α θ (a * u - a * r)
        (mapFused (fun v => Real.sqrt a • v) z) (mapFused (fun v => Real.sqrt a • v) z')) *
      diagramKernel θ w (a * h - a * u) (collisionEmbedding α (mapFused (fun v => Real.sqrt a • v) z'))
        (fun i => Real.sqrt a • y i) =
    kernelScaleFactor a n ^ 3 *
      (ENNReal.ofReal (incomingKernel α r z x) * ENNReal.ofReal (collisionKernel α (θ + Real.log a) (u - r) z z') *
        diagramKernel (θ + Real.log a) w (h - u) (collisionEmbedding α z') y) := by
  rw [show a * u - a * r = a * (u - r) by ring,
    show a * h - a * u = a * (h - u) by ring, collisionEmbedding_map, hrec,
    incomingKernel_scale α ha, collisionKernel_scale α θ ha (sub_pos.mpr hru)]
  simp only [ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos ha _).le), kernelScaleFactor]
  simp only [pow_succ, pow_zero]
  ac_rfl

/-- Exact parabolic scaling of each diagram. -/
theorem diagramKernel_scale {n : ℕ} (w : List (CollisionPair n)) (θ : ℝ)
    {a h : ℝ} (ha : 0 < a) (x y : Configuration n) :
    diagramKernel θ w (a * h) (fun i => Real.sqrt a • x i) (fun i => Real.sqrt a • y i) =
      kernelScaleFactor a n * diagramKernel (θ + Real.log a) w h x y := by
  induction w generalizing θ h x y with
  | nil =>
    rw [diagramKernel, diagramKernel, freeKernel_scale n ha,
      ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos ha _).le)]
    rfl
  | cons α w ih =>
    let A := ENNReal.ofReal a
    let J := ENNReal.ofReal (a ^ (n - 1))
    let C := kernelScaleFactor a n
    let G : ℝ → ℝ → FusedConfiguration α → FusedConfiguration α → ℝ≥0∞ := fun r u z z' =>
      ENNReal.ofReal (incomingKernel α r z x) *
      ENNReal.ofReal (collisionKernel α (θ + Real.log a) (u - r) z z') *
      diagramKernel (θ + Real.log a) w (h - u) (collisionEmbedding α z') y
    have hsp (r u : ℝ) (hru : r < u) :
        (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α (a * r) z (fun i => Real.sqrt a • x i)) *
          ENNReal.ofReal (collisionKernel α θ (a * u - a * r) z z') *
          diagramKernel θ w (a * h - a * u) (collisionEmbedding α z') (fun i => Real.sqrt a • y i)) =
        J * (J * (C ^ 3 * ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α, G r u z z')) := by
      rw [lintegral_fused_scale_pair α ha]
      congr 2
      have he : ∀ z z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α (a * r) (mapFused (fun v => Real.sqrt a • v) z)
            (fun i => Real.sqrt a • x i)) *
          ENNReal.ofReal (collisionKernel α θ (a * u - a * r) (mapFused (fun v => Real.sqrt a • v) z)
            (mapFused (fun v => Real.sqrt a • v) z')) *
          diagramKernel θ w (a * h - a * u) (collisionEmbedding α (mapFused (fun v => Real.sqrt a • v) z'))
            (fun i => Real.sqrt a • y i) = C ^ 3 * G r u z z' := by
        intro z z'
        exact diagramStep_scale α w θ ha hru x y z z'
          (ih θ (collisionEmbedding α z') y)
      simp_rw [he, lintegral_const_mul' (C ^ 3) _ (by simp [C, kernelScaleFactor])]
    simp only [diagramKernel]
    rw [lintegral_Ioo_zero_mul ha h]
    simp_rw [lintegral_Ioo_mul ha]
    rw [lintegral_const_mul' A _ ENNReal.ofReal_ne_top]
    have he : (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h,
        ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α (a * r) z (fun i => Real.sqrt a • x i)) *
          ENNReal.ofReal (collisionKernel α θ (a * u - a * r) z z') *
          diagramKernel θ w (a * h - a * u) (collisionEmbedding α z') (fun i => Real.sqrt a • y i)) =
      J * (J * (C ^ 3 * ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h,
        ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α, G r u z z')) := by
      calc _ = ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h,
          J * (J * (C ^ 3 * ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α, G r u z z')) := by
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro r _hr
            apply setLIntegral_congr_fun measurableSet_Ioo
            intro u hu
            exact hsp r u hu.1
        _ = _ := by simp_rw [lintegral_const_mul' J _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' (C ^ 3) _ (by simp [C, kernelScaleFactor])]
    rw [he]
    have hn : 1 ≤ n := by have ht := α.1.1.isLt; omega
    have hc := kernelScaleFactor_cancel ha hn
    change A * (A * (J * (J * (C ^ 3 * _)))) = C * _
    calc _ = (A * A * J * J * C ^ 3) *
        (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, ∫⁻ z : FusedConfiguration α,
          ∫⁻ z' : FusedConfiguration α, G r u z z') := by ac_rfl
      _ = _ := by rw [hc]

/-- Exact parabolic scaling of the complete moment-kernel series. -/
theorem momentKernel_scale (n : ℕ) (θ : ℝ) {a h : ℝ} (ha : 0 < a) (x y : Configuration n) :
    momentKernel n θ (a * h) (fun i => Real.sqrt a • x i) (fun i => Real.sqrt a • y i) =
      ENNReal.ofReal ((a ^ n)⁻¹) * momentKernel n (θ + Real.log a) h x y := by
  unfold momentKernel
  rw [freeKernel_scale n ha, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos ha _).le), mul_add]
  congr 1
  simp_rw [diagramKernel_scale _ θ ha]
  simp only [← Finset.mul_sum, ENNReal.tsum_mul_left, kernelScaleFactor]

end Critical2DKPZ.DeltaBose
