/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationBoundaryProfiles
public import Critical2DKPZ.MomentBounds.AiiKCollisionWeight
import Mathlib.Tactic

/-! # Weighted indicator boundary profiles for the marked remainder -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

private theorem collisionWord_finiteLpNorm_two_le_bound_sqrt_card {α : Type*}
    (A : Finset α) (f : α → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ y ∈ A, |f y| ≤ E) :
    finiteLpNorm A 2 f ≤ E * Real.sqrt (A.card : ℝ) := by
  have hsum : (∑ y ∈ A, |f y| ^ (2 : ℝ)) ≤ (A.card : ℝ) * E ^ 2 := by
    calc
      _ ≤ ∑ _y ∈ A, E ^ 2 := by
        apply Finset.sum_le_sum
        intro y hy
        rw [Real.rpow_two]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf y hy) 2
      _ = _ := by simp
  calc
    finiteLpNorm A 2 f = Real.sqrt (∑ y ∈ A, |f y| ^ (2 : ℝ)) := by
      simp only [finiteLpNorm, Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt ((A.card : ℝ) * E ^ 2) := Real.sqrt_le_sqrt hsum
    _ = E * Real.sqrt (A.card : ℝ) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hE]
      ring

/-- The weighted indicator boundary has the same cardinality scaling as the
unweighted boundary, with an explicit exponential support cost. -/
theorem finiteLpNorm_weighted_hattedBoundary_indicator_le (h : ℕ) (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ), 0 ≤ t → ∀ (L : ℕ)
      (A : Finset Site) (r : ℝ),
      (∀ y ∈ A, t * ‖siteToPlane y‖ ≤ r) →
      ∀ (s : Finset (LatticeConfiguration h)) (I : ReplicaPartition h), I ≠ ⊥ →
      finiteLpNorm s 2 (fun x => hattedReplicaBoundaryVector L I A
        (fun y => if y ∈ A then (1 : ℝ) else 0) x / replicaExponentialWeight t x) ≤
        2 * C * Real.exp (C * t ^ 2 * L) * Real.exp r ^ h *
          (A.card : ℝ) * Real.sqrt (A.card : ℝ) ^ (h - 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := finiteLpNorm_hattedReplicaBoundaryVector_le h hh
  refine ⟨C, hC, ?_⟩
  intro t ht L A r hr s I hI
  let f : Site → ℝ := fun y => if y ∈ A then 1 else 0
  let F : Site → ℝ := fun y => f y * Real.exp (t * ‖siteToPlane y‖)
  have hf : ∀ y, 0 ≤ f y := by intro y; dsimp [f]; split_ifs <;> norm_num
  have hF (y : Site) (hy : y ∈ A) : |F y| ≤ Real.exp r := by
    simpa [F, f, hy] using Real.exp_le_exp.mpr (hr y hy)
  have hnorm : finiteLpNorm A 2 F ≤ Real.exp r * Real.sqrt (A.card : ℝ) :=
    collisionWord_finiteLpNorm_two_le_bound_sqrt_card A F (Real.exp r)
      (Real.exp_nonneg _) hF
  have hsum : (∑ y ∈ A, F y) ≤ (A.card : ℝ) * Real.exp r := by
    calc
      _ ≤ ∑ _y ∈ A, Real.exp r := by
        apply Finset.sum_le_sum
        intro y hy
        exact (le_abs_self _).trans (hF y hy)
      _ = _ := by simp
  have hb := hbound t ht L 2 (by norm_num) A f hf s I hI
  norm_num only at hb
  calc
    _ ≤ C * Real.exp (C * t ^ 2 * L) * 2 *
        ((A.card : ℝ) * Real.exp r) *
          (Real.exp r * Real.sqrt (A.card : ℝ)) ^ (h - 1) := by
      apply hb.trans
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsum (by positivity)
      · exact pow_le_pow_left₀ (finiteLpNorm_nonneg _ _ _) hnorm _
      · exact pow_nonneg (finiteLpNorm_nonneg _ _ _) _
      · positivity
    _ = _ := by
      have hpow : Real.exp r ^ h = Real.exp r * Real.exp r ^ (h - 1) := by
        calc
          Real.exp r ^ h = Real.exp r ^ ((h - 1) + 1) := by congr 1; omega
          _ = _ := by rw [pow_succ]; ring
      rw [mul_pow, hpow]
      ring

end Critical2DKPZ.SHF.Moments

end
