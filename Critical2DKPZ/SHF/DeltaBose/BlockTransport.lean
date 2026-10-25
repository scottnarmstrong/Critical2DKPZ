/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.Tactic

/-! The elementary moment-kernel blocks satisfy spatial transport and scaling identities. -/

@[expose] public section

namespace Critical2DKPZ.DeltaBose

/-- Apply the same spatial map to the center and all spectator coordinates. -/
def mapFused {n : ℕ} {α : CollisionPair n} (f : Plane → Plane)
    (y : FusedConfiguration α) : FusedConfiguration α := (f y.1, fun i => f (y.2 i))

/-- The collision embedding commutes with every simultaneous spatial map. -/
theorem collisionEmbedding_map {n : ℕ} (α : CollisionPair n) (f : Plane → Plane)
    (y : FusedConfiguration α) :
    collisionEmbedding α (mapFused f y) = fun i => f (collisionEmbedding α y i) := by
  funext i
  unfold collisionEmbedding mapFused
  split_ifs <;> rfl

/-- Planar parabolic scaling with the exact normalization. -/
theorem heatKernel_scale {a t : ℝ} (ha : 0 < a) (z : Plane) :
    heatKernel (a * t) (Real.sqrt a • z) = a⁻¹ * heatKernel t z := by
  simp only [heatKernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a),
    mul_pow, Real.sq_sqrt ha.le]
  have he : -(a * ‖z‖ ^ 2) / (2 * (a * t)) = -‖z‖ ^ 2 / (2 * t) := by
    field_simp
  rw [he]
  ring

/-- The free `n`-particle kernel has density scaling exponent `n`. -/
theorem freeKernel_scale (n : ℕ) {a t : ℝ} (ha : 0 < a) (x y : Configuration n) :
    freeKernel n (a * t) (fun i => Real.sqrt a • x i) (fun i => Real.sqrt a • y i) =
      (a ^ n)⁻¹ * freeKernel n t x y := by
  unfold freeKernel
  simp_rw [← smul_sub, heatKernel_scale ha]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]







end Critical2DKPZ.DeltaBose
