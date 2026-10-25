/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.ReplicaOverlap
import Critical2DKPZ.RandomWalk.Estimates
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-!
# Logarithmic replica overlap

Summing the local central limit error at the origin gives a bounded difference
from the harmonic sum. The integral bounds on harmonic numbers then give
`R_N = π⁻¹ log N + O(1)`, as in KPZ equation (1.6).
-/

public section

namespace Critical2DKPZ

/-- The return probability at even times has a summable error. -/
theorem srwKernel_two_mul_zero_localCLT :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |srwKernel (2 * n) 0 - (1 / Real.pi) * (n : ℝ)⁻¹| ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := srwKernel_localCLT
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hz : Even ((0 : Site) 0 + (0 : Site) 1 + (2 * n : ℕ)) := by
    refine ⟨(n : ℤ), ?_⟩
    simp
    ring
  have he := h (2 * n) (by omega) 0 hz
  have hg : 2 * heatKernel (((2 * n : ℕ) : ℝ) / 2) (siteToPlane 0) =
      (1 / Real.pi) * (n : ℝ)⁻¹ := by
    have hp : siteToPlane 0 = 0 := by ext i; simp [siteToPlane]
    rw [hp, heatKernel]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      neg_zero, zero_div, Real.exp_zero, mul_one]
    push_cast
    field_simp
  rw [hg] at he
  refine he.trans ?_
  apply div_le_div_of_nonneg_left hC.le (by positivity)
  push_cast
  nlinarith only [sq_nonneg (n : ℝ)]

/-- The replica overlap differs from `π⁻¹ log N` by a uniformly bounded amount. -/
theorem replicaOverlap_log_bound :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |replicaOverlap N - (1 / Real.pi) * Real.log N| ≤ C := by
  obtain ⟨K, hK, h⟩ := srwKernel_two_mul_zero_localCLT
  have hs : Summable (fun n : ℕ => K / (n : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left K
  refine ⟨(∑' n : ℕ, K / (n : ℝ) ^ 2) + 1 / Real.pi, fun N hN => ?_⟩
  have hsum : replicaOverlap N - (1 / Real.pi) * (harmonic N : ℝ) =
      ∑ n ∈ Finset.Icc 1 N,
        (srwKernel (2 * n) 0 - (1 / Real.pi) * (n : ℝ)⁻¹) := by
    simp only [replicaOverlap, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, Finset.mul_sum, Finset.sum_sub_distrib]
  have herror : |replicaOverlap N - (1 / Real.pi) * (harmonic N : ℝ)| ≤
      ∑' n : ℕ, K / (n : ℝ) ^ 2 := by
    rw [hsum]
    calc
      |∑ n ∈ Finset.Icc 1 N,
          (srwKernel (2 * n) 0 - (1 / Real.pi) * (n : ℝ)⁻¹)|
        ≤ ∑ n ∈ Finset.Icc 1 N,
          |srwKernel (2 * n) 0 - (1 / Real.pi) * (n : ℝ)⁻¹| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, K / (n : ℝ) ^ 2 :=
        Finset.sum_le_sum fun n hn => h n (Finset.mem_Icc.mp hn).1
      _ ≤ ∑' n : ℕ, K / (n : ℝ) ^ 2 :=
        hs.sum_le_tsum _ (fun _ _ => by positivity)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlog : Real.log (N : ℝ) ≤ (harmonic N : ℝ) := by
    refine (Real.log_le_log hN0 ?_).trans (log_add_one_le_harmonic N)
    exact_mod_cast Nat.le_succ N
  have hharm : |(harmonic N : ℝ) - Real.log N| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    linarith only [harmonic_le_one_add_log N]
  calc
    |replicaOverlap N - (1 / Real.pi) * Real.log N|
      = |(replicaOverlap N - (1 / Real.pi) * (harmonic N : ℝ)) +
          (1 / Real.pi) * ((harmonic N : ℝ) - Real.log N)| := by congr 1; ring
    _ ≤ |replicaOverlap N - (1 / Real.pi) * (harmonic N : ℝ)| +
          |(1 / Real.pi) * ((harmonic N : ℝ) - Real.log N)| := abs_add_le _ _
    _ ≤ (∑' n : ℕ, K / (n : ℝ) ^ 2) + 1 / Real.pi := by
      apply add_le_add herror
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      exact (mul_le_mul_of_nonneg_left hharm (by positivity)).trans_eq (mul_one _)

end Critical2DKPZ
