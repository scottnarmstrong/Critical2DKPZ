/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitGapPotential
public import Critical2DKPZ.SHF.Moments.WordLimitDiagonalEntrance
public import Critical2DKPZ.SHF.Moments.WordLimitPotentialTimeTail
import all Critical2DKPZ.SHF.Moments.EntranceWalkMoments
import Mathlib.Tactic

/-! # Integrated gap-potential mass on shrinking diagonal tubes -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

private theorem wordLimit_gapPotential_early_mass_le (D : Finset Site) (n k : ℕ) (hnk : n ≤ k) :
    (∑ s ∈ Finset.Icc 1 n,
      (∑ z ∈ D, srwKernel (2 * s) z) / Real.sqrt ((s : ℝ) + 1)) ≤
        2 * Real.sqrt ((k : ℝ) + 1) := by
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, 1 / Real.sqrt ((s : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro s hs
      exact div_le_div_of_nonneg_right (sum_srwKernel_finite_le_one D (2 * s)) (Real.sqrt_nonneg _)
    _ ≤ ∑ s ∈ Finset.Icc 0 k, 1 / Real.sqrt ((s : ℝ) + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) hnk)
        (fun s hs hnot => by positivity)
    _ ≤ _ := sum_inv_sqrt_add_one_le k

private theorem wordLimit_gapPotential_late_mass_le (D : Finset Site) (n k : ℕ) (hkn : k < n) :
    (∑ s ∈ Finset.Icc (k + 1) n,
      (∑ z ∈ D, srwKernel (2 * s) z) / Real.sqrt ((s : ℝ) + 1)) ≤
        2 * (D.card : ℝ) / Real.sqrt ((k : ℝ) + 1) := by
  have hslice (s : ℕ) : (∑ z ∈ D, srwKernel (2 * s) z) ≤ (D.card : ℝ) / ((s : ℝ) + 1) := by
    calc
      _ ≤ ∑ _z ∈ D, 1 / ((s : ℝ) + 1) :=
        Finset.sum_le_sum (fun z hz => Smoothing.srwKernel_even_le_inv_succ s z)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
  calc
    _ ≤ ∑ s ∈ Finset.Icc (k + 1) n,
        (D.card : ℝ) * (1 / (((s : ℝ) + 1) * Real.sqrt ((s : ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro s hs
      exact (div_le_div_of_nonneg_right (hslice s) (Real.sqrt_nonneg _)).trans_eq (by rw [div_div]; ring)
    _ = (D.card : ℝ) * ∑ s ∈ Finset.Icc (k + 1) n,
        1 / (((s : ℝ) + 1) * Real.sqrt ((s : ℝ) + 1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D.card : ℝ) * (2 / Real.sqrt (((k + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_succ_le (k + 1) n (by omega) (by omega))
        (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

/-- A sparse gap set has small integrated potential after diffusive scaling.
The bound is uniform even when the remaining microscopic horizon is unbounded. -/
theorem sum_wordGapPotential_le_cutoff (D : Finset Site) (n k : ℕ) :
    (∑ z ∈ D, wordGapPotential n z) ≤
      2 * Real.sqrt ((k : ℝ) + 1) + 2 * (D.card : ℝ) / Real.sqrt ((k : ℝ) + 1) := by
  have hswap : (∑ z ∈ D, wordGapPotential n z) =
      ∑ s ∈ Finset.Icc 1 n, (∑ z ∈ D, srwKernel (2 * s) z) / Real.sqrt ((s : ℝ) + 1) := by
    simp only [wordGapPotential]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div]
  rw [hswap]
  by_cases hnk : n ≤ k
  · exact (wordLimit_gapPotential_early_mass_le D n k hnk).trans
      (le_add_of_nonneg_right (by positivity))
  · have hkn : k < n := by omega
    have hsplit := Finset.sum_Ico_consecutive
      (fun s : ℕ => (∑ z ∈ D, srwKernel (2 * s) z) / Real.sqrt ((s : ℝ) + 1))
      (m := 1) (n := k + 1) (k := n + 1) (by omega) (by omega)
    simp only [Finset.Ico_add_one_right_eq_Icc] at hsplit
    rw [← hsplit]
    exact add_le_add (wordLimit_gapPotential_early_mass_le D k k le_rfl)
      (wordLimit_gapPotential_late_mass_le D n k hkn)

end Critical2DKPZ.SHF.Moments
