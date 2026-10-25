/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FreeOperatorBound
public import Critical2DKPZ.MomentBounds.CCR25InteractingOperatorBound
import Mathlib.Tactic

/-! # Fixed weighted operator constants on a diffusive time window -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds Polymer

/-- The inverse square-root lattice weight is positive, at most one, and
has unit squared diffusive scale. -/
theorem collisionWord_inv_sqrt_scale {N : ℕ} (hN : 1 ≤ N) :
    0 < (Real.sqrt (N : ℝ))⁻¹ ∧ (Real.sqrt (N : ℝ))⁻¹ ≤ 1 ∧
      ((Real.sqrt (N : ℝ))⁻¹) ^ 2 * N = 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  refine ⟨inv_pos.mpr hsqrt, ?_, ?_⟩
  · apply (inv_le_one₀ hsqrt).mpr
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
  · rw [inv_pow, Real.sq_sqrt hNpos.le, inv_mul_cancel₀ hNpos.ne']

/-- The squared spatial weight times every allowed duration is bounded by
the fixed macroscopic horizon. -/
theorem collisionWord_inv_sqrt_time_le {N L B : ℕ} (hN : 1 ≤ N) (hL : L ≤ B * N) :
    ((Real.sqrt (N : ℝ))⁻¹) ^ 2 * L ≤ B := by
  have hscale := (collisionWord_inv_sqrt_scale hN).2.2
  calc
    _ ≤ ((Real.sqrt (N : ℝ))⁻¹) ^ 2 * (B * N : ℕ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hL) (sq_nonneg _)
    _ = (B : ℝ) * (((Real.sqrt (N : ℝ))⁻¹) ^ 2 * N) := by push_cast; ring
    _ = _ := by rw [hscale, mul_one]

/-- Uniform CCR operator constants absorb the spatial exponential weight on a fixed diffusive time window. -/
theorem exists_collisionWord_weightedOperator_constants (h : ℕ) (hh : 3 ≤ h) (B : ℕ) :
    ∃ cI cQ : ℝ, 1 ≤ cI ∧ 1 ≤ cQ ∧
      ∀ {N L : ℕ}, 1 ≤ N → L ≤ B * N → ∀ lam β : ℝ, 0 ≤ lam →
      (∀ J : ReplicaPartition h, J ≠ ⊥ → |replicaPartitionDisorderMoment β J| ≤ sigmaSq β) →
      sigmaSq β * dampedOverlap lam L < 1 →
      (∀ (s : Finset (LatticeConfiguration h)) (I : ReplicaPartition h), I ≠ ⊥ →
        ∀ f : LatticeConfiguration h → ℝ,
        finiteLpNorm s 2 (finiteKernelApply s
          (weightedKernel (replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹))
            (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
          (1 + cI * (sigmaSq β * dampedOverlap lam L /
            (1 - sigmaSq β * dampedOverlap lam L))) * finiteLpNorm s 2 f) ∧
      (∀ (s : Finset (LatticeConfiguration h)) (I J : ReplicaPartition h),
        I ≠ ⊥ → J ≠ ⊥ → I ≠ J → ∀ f : LatticeConfiguration h → ℝ,
        finiteLpNorm s 2 (finiteKernelApply s
          (weightedKernel (replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹))
            (hattedFreeReplicaKernel L I J)) f) ≤ cQ * finiteLpNorm s 2 f) := by
  obtain ⟨CI, hCI, hI⟩ := finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le h (by omega)
  obtain ⟨CQ, hCQ, hQ⟩ := finiteLpNorm_weighted_hattedFreeReplicaKernel_le h hh
  let cI := CI * Real.exp (CI * B)
  let cQ := 4 * CQ * Real.exp (CQ * B)
  have hCI0 : 0 ≤ CI := zero_le_one.trans hCI
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hcI : 1 ≤ cI := by
    have he : 1 ≤ Real.exp (CI * B) := Real.one_le_exp (by positivity)
    exact one_le_mul_of_one_le_of_one_le hCI he
  have hcQ : 1 ≤ cQ := by
    have he : 1 ≤ Real.exp (CQ * B) := Real.one_le_exp (by positivity)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hCQ) he
  refine ⟨cI, cQ, hcI, hcQ, ?_⟩
  intro N L hN hL lam β hlam hMom hsmall
  have ht := (collisionWord_inv_sqrt_scale hN).1.le
  have htime := collisionWord_inv_sqrt_time_le hN hL
  have hcost (C : ℝ) (hC : 0 ≤ C) :
      C * Real.exp (C * ((Real.sqrt (N : ℝ))⁻¹) ^ 2 * L) ≤
        C * Real.exp (C * B) := by
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left htime hC]
  constructor
  · intro s I hpart f
    apply (hI _ ht L lam β hlam hMom hsmall 2 (by norm_num) s I hpart f).trans
    apply mul_le_mul_of_nonneg_right _ (finiteLpNorm_nonneg _ _ _)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right (hcost CI hCI0)
      (div_nonneg (mul_nonneg (sigmaSq_nonneg _) (by
        unfold dampedOverlap
        exact Finset.sum_nonneg (fun r hr =>
          mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _)))) (by linarith))
  · intro s I J hpartI hpartJ hne f
    apply (hQ _ ht L 2 (by norm_num) s I J hpartI hpartJ hne f).trans
    apply mul_le_mul_of_nonneg_right _ (finiteLpNorm_nonneg _ _ _)
    have hcostQ := hcost CQ hCQ0
    dsimp [cQ]
    norm_num only
    nlinarith only [hcostQ]

end Critical2DKPZ.SHF.Moments

end
