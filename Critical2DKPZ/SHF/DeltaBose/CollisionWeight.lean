/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
public import Critical2DKPZ.SHF.DeltaBose.CollisionScaling
import Mathlib.Tactic

/-! # Weighted comparison for the repeated-collision block -/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The tensorized heat-weight estimate for any finite set of planar coordinates. -/
theorem prod_heatKernel_mul_exp_le {ι : Type*} [Fintype ι] (a : ℝ) {t : ℝ} (ht : 0 < t)
    (v : ι → Plane) :
    (∏ i, heatKernel t (v i)) * Real.exp (a * ∑ i, planeOneNorm (v i)) ≤
      2 ^ Fintype.card ι * Real.exp (2 * Fintype.card ι * a ^ 2 * t) *
        ∏ i, heatKernel (2 * t) (v i) := by
  classical
  have he : (∏ i, heatKernel t (v i)) * Real.exp (a * ∑ i, planeOneNorm (v i)) =
      ∏ i, heatKernel t (v i) * Real.exp (a * planeOneNorm (v i)) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum]
  rw [he]
  calc (∏ i, heatKernel t (v i) * Real.exp (a * planeOneNorm (v i)))
      ≤ ∏ i, 2 * Real.exp (2 * a ^ 2 * t) * heatKernel (2 * t) (v i) :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg (Critical2DKPZ.heatKernel_pos ht _).le (Real.exp_pos _).le)
          (fun i _ => heatKernel_mul_exp_oneNorm_le a ht _)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        mul_pow, ← Real.exp_nat_mul]
      congr 2
      congr 1
      ring

/-- Difference of the doubled fused weights is bounded by the displacement weight. -/
theorem fusedOneNorm_sub_le {n : ℕ} (α : CollisionPair n) (z w : FusedConfiguration α) :
    fusedOneNorm α z - fusedOneNorm α w ≤
      2 * planeOneNorm (w.1 - z.1) + ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i) := by
  have hs : (∑ i : Spectator α, planeOneNorm (z.2 i)) -
      (∑ i : Spectator α, planeOneNorm (w.2 i)) ≤
        ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => planeOneNorm_sub_le (z.2 i) (w.2 i)
  unfold fusedOneNorm
  linarith only [planeOneNorm_sub_le z.1 w.1, hs]

/-- The collision heat product satisfies an exponential-weight comparison. -/
theorem collisionKernel_mul_exp_weight_le {n : ℕ} (α : CollisionPair n) (θ : ℝ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (z w : FusedConfiguration α) :
    collisionKernel α θ t z w * Real.exp (a * (fusedOneNorm α z - fusedOneNorm α w)) ≤
      weightGrowth n a t * (scalarDensity θ t / scalarDensity θ (2 * t)) *
        collisionKernel α θ (2 * t) z w := by
  have hc := heatKernel_mul_exp_oneNorm_le (2 * a) (show 0 < t / 2 by positivity) (w.1 - z.1)
  have hs := prod_heatKernel_mul_exp_le a ht (fun i : Spectator α => w.2 i - z.2 i)
  have hk : 0 ≤ 4 * Real.pi * scalarDensity θ t := by
    exact mul_nonneg (by positivity) (scalarDensity_pos θ ht).le
  have he : 2 * (2 * a) ^ 2 * (t / 2) +
      2 * (Fintype.card (Spectator α) : ℝ) * a ^ 2 * t = 2 * n * a ^ 2 * t := by
    have hn : 2 ≤ n := by have h := α.2; have hlt := α.1.2.isLt; omega
    rw [card_spectator, Nat.cast_sub hn]
    push_cast
    ring
  have hp : 2 * 2 ^ Fintype.card (Spectator α) ≤ (2 : ℝ) ^ n := by
    rw [card_spectator]
    have hn : n - 2 + 1 ≤ n := by omega
    calc (2 : ℝ) * 2 ^ (n - 2) = 2 ^ (n - 2 + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have htime : 2 * (t / 2) = t := by ring
  have hsp : 0 ≤ (∏ i : Spectator α, heatKernel t (w.2 i - z.2 i)) *
      Real.exp (a * ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i)) :=
    mul_nonneg (Finset.prod_nonneg fun i _ => (Critical2DKPZ.heatKernel_pos ht _).le) (Real.exp_pos _).le
  have hcp : 0 ≤ 2 * Real.exp (2 * (2 * a) ^ 2 * (t / 2)) *
      heatKernel (2 * (t / 2)) (w.1 - z.1) :=
    mul_nonneg (by positivity) (Critical2DKPZ.heatKernel_pos (by positivity) _).le
  have hheat := mul_le_mul hc hs hsp hcp
  rw [htime] at hheat
  have hexp : Real.exp (a * (2 * planeOneNorm (w.1 - z.1) +
      ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i))) =
      Real.exp ((2 * a) * planeOneNorm (w.1 - z.1)) *
        Real.exp (a * ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbound : collisionKernel α θ t z w *
      Real.exp (a * (fusedOneNorm α z - fusedOneNorm α w)) ≤
      weightGrowth n a t * (4 * Real.pi * scalarDensity θ t) *
        heatKernel t (w.1 - z.1) * ∏ i : Spectator α, heatKernel (2 * t) (w.2 i - z.2 i) := by
    calc collisionKernel α θ t z w * Real.exp (a * (fusedOneNorm α z - fusedOneNorm α w))
        ≤ collisionKernel α θ t z w * Real.exp (a * (2 * planeOneNorm (w.1 - z.1) +
            ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (fusedOneNorm_sub_le α z w) ha)) (collisionKernel_pos α θ ht z w).le
      _ = (4 * Real.pi * scalarDensity θ t) *
          ((heatKernel (t / 2) (w.1 - z.1) * Real.exp ((2 * a) * planeOneNorm (w.1 - z.1))) *
          ((∏ i : Spectator α, heatKernel t (w.2 i - z.2 i)) *
            Real.exp (a * ∑ i : Spectator α, planeOneNorm (w.2 i - z.2 i)))) := by
        rw [collisionKernel, hexp]
        ring
      _ ≤ (4 * Real.pi * scalarDensity θ t) *
          ((2 * Real.exp (2 * (2 * a) ^ 2 * (t / 2)) * heatKernel t (w.1 - z.1)) *
          (2 ^ Fintype.card (Spectator α) * Real.exp (2 * Fintype.card (Spectator α) * a ^ 2 * t) *
            ∏ i : Spectator α, heatKernel (2 * t) (w.2 i - z.2 i))) :=
        mul_le_mul_of_nonneg_left hheat hk
      _ = (2 * 2 ^ Fintype.card (Spectator α)) * Real.exp (2 * n * a ^ 2 * t) *
          (4 * Real.pi * scalarDensity θ t) * heatKernel t (w.1 - z.1) *
            ∏ i : Spectator α, heatKernel (2 * t) (w.2 i - z.2 i) := by
        rw [← he, Real.exp_add]
        ring
      _ ≤ _ := by
        unfold weightGrowth
        have hrest : 0 ≤ Real.exp (2 * n * a ^ 2 * t) *
            (4 * Real.pi * scalarDensity θ t) * heatKernel t (w.1 - z.1) *
              ∏ i : Spectator α, heatKernel (2 * t) (w.2 i - z.2 i) :=
          mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hk) (Critical2DKPZ.heatKernel_pos ht _).le)
            (Finset.prod_nonneg fun i _ => (Critical2DKPZ.heatKernel_pos (by positivity) _).le)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp hrest
  apply hbound.trans_eq
  unfold collisionKernel
  rw [show 2 * t / 2 = t by ring]
  have hj := (scalarDensity_pos θ (show 0 < 2 * t by positivity)).ne'
  field_simp [hj]

/-- The weighted repeated-collision operator, with explicit scalar and weight dependence. -/
theorem collisionKernel_weighted_l2_sq_le {n : ℕ} (α : CollisionPair n) (θ : ℝ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) {f : FusedConfiguration α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z : FusedConfiguration α, (∫⁻ w : FusedConfiguration α,
      ENNReal.ofReal (collisionKernel α θ t z w *
        Real.exp (a * (fusedOneNorm α z - fusedOneNorm α w))) * f w) ^ 2) ≤
      ENNReal.ofReal (weightGrowth n a t * (4 * Real.pi * scalarDensity θ t)) ^ 2 *
        ∫⁻ w : FusedConfiguration α, f w ^ 2 := by
  have hj := scalarDensity_pos θ ht
  have hj2 := scalarDensity_pos θ (show 0 < 2 * t by positivity)
  have hC : 0 ≤ weightGrowth n a t * (scalarDensity θ t / scalarDensity θ (2 * t)) :=
    mul_nonneg (weightGrowth_pos n a t).le (div_pos hj hj2).le
  have hKL (z w : FusedConfiguration α) :
      ENNReal.ofReal (collisionKernel α θ t z w *
        Real.exp (a * (fusedOneNorm α z - fusedOneNorm α w))) ≤
      ENNReal.ofReal (weightGrowth n a t * (scalarDensity θ t / scalarDensity θ (2 * t))) *
        ENNReal.ofReal (collisionKernel α θ (2 * t) z w) := by
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (collisionKernel_mul_exp_weight_le α θ ha ht z w)
  have h := lintegral_kernel_sq_dominate volume volume ENNReal.ofReal_ne_top hKL f
    (collisionKernel_l2_sq_le α θ (t := 2 * t) (by positivity) hf)
  have he : ENNReal.ofReal (weightGrowth n a t * (scalarDensity θ t / scalarDensity θ (2 * t))) ^ 2 *
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ (2 * t)) ^ 2 =
        ENNReal.ofReal (weightGrowth n a t * (4 * Real.pi * scalarDensity θ t)) ^ 2 := by
    rw [← mul_pow, ← ENNReal.ofReal_mul hC]
    congr 2
    field_simp [hj2.ne']
  rw [he] at h
  exact h

end Critical2DKPZ.DeltaBose
