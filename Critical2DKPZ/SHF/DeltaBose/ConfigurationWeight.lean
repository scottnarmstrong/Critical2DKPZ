/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.HeatWeight
public import Critical2DKPZ.SHF.DeltaBose.IncomingMass
import Mathlib.Tactic

/-! The exponential-weight comparisons on full and fused configurations use twice the planar weight at the collision center and an exponent quadratic in the weight parameter. -/

@[expose] public section

namespace Critical2DKPZ.DeltaBose

/-- Sum of the planar coordinate norms over the particle labels. -/
noncomputable def configurationOneNorm {n : ℕ} (x : Configuration n) : ℝ :=
  ∑ i, planeOneNorm (x i)

/-- Collision-coordinate weight, with the center counted twice. -/
noncomputable def fusedOneNorm {n : ℕ} (α : CollisionPair n) (z : FusedConfiguration α) : ℝ :=
  2 * planeOneNorm z.1 + ∑ i : Spectator α, planeOneNorm (z.2 i)

/-- The planar coordinate ℓ¹ norm is nonnegative. -/
theorem planeOneNorm_nonneg (z : Plane) : 0 ≤ planeOneNorm z := by
  unfold planeOneNorm
  positivity

/-- The difference of planar ℓ¹ norms is bounded by the ℓ¹ norm of the displacement. -/
theorem planeOneNorm_sub_le (x y : Plane) :
    planeOneNorm x - planeOneNorm y ≤ planeOneNorm (y - x) := by
  have h0 := abs_sub_abs_le_abs_sub (x 0) (y 0)
  have h1 := abs_sub_abs_le_abs_sub (x 1) (y 1)
  change |x 0| + |x 1| - (|y 0| + |y 1|) ≤ |y 0 - x 0| + |y 1 - x 1|
  rw [abs_sub_comm (y 0), abs_sub_comm (y 1)]
  linarith only [h0, h1]

/-- The doubled fused weight is precisely the ambient weight of the embedding. -/
theorem configurationOneNorm_collisionEmbedding {n : ℕ} (α : CollisionPair n)
    (z : FusedConfiguration α) : configurationOneNorm (collisionEmbedding α z) = fusedOneNorm α z := by
  classical
  have hsum : (∑ i : Fin n, planeOneNorm (collisionEmbedding α z i)) =
      planeOneNorm (collisionEmbedding α z α.1.1) +
      planeOneNorm (collisionEmbedding α z α.1.2) +
      ∑ i : Spectator α, planeOneNorm (collisionEmbedding α z i.1) := by
    exact sum_collision_labels α (fun i => planeOneNorm (collisionEmbedding α z i))
  rw [configurationOneNorm, hsum]
  simp only [collisionEmbedding, true_or, dite_true, or_true]
  unfold fusedOneNorm
  rw [two_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [i.2.1, i.2.2, or_self, dite_false]

/-- The difference of configuration ℓ¹ norms is bounded by the ℓ¹ norm of their displacement. -/
theorem configurationOneNorm_sub_le {n : ℕ} (x y : Configuration n) :
    configurationOneNorm x - configurationOneNorm y ≤
      configurationOneNorm (fun i => y i - x i) := by
  rw [configurationOneNorm, configurationOneNorm, configurationOneNorm, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => planeOneNorm_sub_le (x i) (y i)

/-- Product heat comparison with the displacement weight. -/
theorem freeKernel_mul_exp_displacement_le (n : ℕ) (a : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : Configuration n) :
    freeKernel n t x y * Real.exp (a * configurationOneNorm (fun i => y i - x i)) ≤
      2 ^ n * Real.exp (2 * n * a ^ 2 * t) * freeKernel n (2 * t) x y := by
  have hprod : freeKernel n t x y * Real.exp (a * configurationOneNorm (fun i => y i - x i)) =
      ∏ i : Fin n, heatKernel t (y i - x i) * Real.exp (a * planeOneNorm (y i - x i)) := by
    rw [freeKernel, Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    exact Finset.mul_sum _ _ _
  rw [hprod]
  calc (∏ i : Fin n, heatKernel t (y i - x i) * Real.exp (a * planeOneNorm (y i - x i)))
      ≤ ∏ i : Fin n, 2 * Real.exp (2 * a ^ 2 * t) * heatKernel (2 * t) (y i - x i) :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg (Critical2DKPZ.heatKernel_pos ht _).le (Real.exp_pos _).le)
          (fun i _ => heatKernel_mul_exp_oneNorm_le a ht _)
    _ = 2 ^ n * Real.exp (2 * n * a ^ 2 * t) * freeKernel n (2 * t) x y := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        mul_pow, ← Real.exp_nat_mul]
      congr 2
      congr 1
      ring

/-- Comparison for the conjugated free heat operator, uniform over all endpoints. -/
theorem freeKernel_mul_exp_weight_le (n : ℕ) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t)
    (x y : Configuration n) :
    freeKernel n t x y * Real.exp (a * (configurationOneNorm x - configurationOneNorm y)) ≤
      2 ^ n * Real.exp (2 * n * a ^ 2 * t) * freeKernel n (2 * t) x y := by
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (configurationOneNorm_sub_le x y) ha))
      (freeKernel_pos n ht x y).le).trans (freeKernel_mul_exp_displacement_le n a ht x y)

end Critical2DKPZ.DeltaBose
