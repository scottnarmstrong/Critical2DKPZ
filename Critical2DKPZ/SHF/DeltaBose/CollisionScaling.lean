/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.BlockTransport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! # Collision-coordinate dimensions and exact block scaling -/

public section

namespace Critical2DKPZ.DeltaBose

/-- A collision leaves exactly `n-2` spectator particles. -/
theorem card_spectator {n : ℕ} (α : CollisionPair n) : Fintype.card (Spectator α) = n - 2 := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun i : Fin n => i ≠ α.1.1 ∧ i ≠ α.1.2)) =
      (Finset.univ.erase α.1.1).erase α.1.2 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [he, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ α.1.1),
    Finset.card_univ, Fintype.card_fin]
  · omega
  · exact Finset.mem_erase.mpr ⟨(ne_of_gt α.2), Finset.mem_univ _⟩

/-- The collision space has twice `n-1` real coordinates. -/
theorem finrank_fusedConfiguration {n : ℕ} (α : CollisionPair n) :
    Module.finrank ℝ (FusedConfiguration α) = 2 * (n - 1) := by
  have hn : 2 ≤ n := by have h := α.2; have hlt := α.1.2.isLt; omega
  simp only [FusedConfiguration, Module.finrank_prod, Module.finrank_pi_fintype,
    Plane, finrank_euclideanSpace, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, card_spectator]
  omega

/-- Scaling of incoming blocks. -/
theorem incomingKernel_scale {n : ℕ} (α : CollisionPair n) {a t : ℝ} (ha : 0 < a)
    (z : FusedConfiguration α) (x : Configuration n) :
    incomingKernel α (a * t) (mapFused (fun v => Real.sqrt a • v) z)
        (fun i => Real.sqrt a • x i) = (a ^ n)⁻¹ * incomingKernel α t z x := by
  unfold incomingKernel
  rw [collisionEmbedding_map, freeKernel_scale n ha]

/-- Scaling of the resummed collision block includes the logarithmic parameter shift. -/
theorem collisionKernel_scale {n : ℕ} (α : CollisionPair n) (θ : ℝ) {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (z w : FusedConfiguration α) :
    collisionKernel α θ (a * t) (mapFused (fun v => Real.sqrt a • v) z)
        (mapFused (fun v => Real.sqrt a • v) w) =
      (a ^ n)⁻¹ * collisionKernel α (θ + Real.log a) t z w := by
  have hj : scalarDensity θ (a * t) = a⁻¹ * scalarDensity (θ + Real.log a) t := by
    have he := congrArg (fun v : ℝ => a⁻¹ * v) (scalarDensity_scale θ ha ht)
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using he
  have hn : n = Fintype.card (Spectator α) + 2 := by
    rw [card_spectator]
    have h := α.2
    have hlt := α.1.2.isLt
    omega
  unfold collisionKernel mapFused
  simp only [← smul_sub]
  rw [show a * t / 2 = a * (t / 2) by ring, heatKernel_scale ha, hj]
  simp_rw [heatKernel_scale ha]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hp : a ^ n = a ^ Fintype.card (Spectator α) * a ^ 2 := by
    conv_lhs => rw [hn]
    rw [pow_add]
  rw [hp]
  simp only [mul_inv, inv_pow, pow_two]
  ring

end Critical2DKPZ.DeltaBose
