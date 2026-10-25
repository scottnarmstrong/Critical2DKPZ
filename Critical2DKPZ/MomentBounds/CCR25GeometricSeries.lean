/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Finite run counting and geometric summation for CCR25 -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- A uniform bound on each partition weight and an alphabet-cardinality bound
control the sum of all length-`n + 1` word weights. -/
theorem ccr25_wordWeight_sum_le {α : Type*} [Fintype α] {n : ℕ}
    (words : Finset (Fin (n + 1) → α)) (mom : α → ℝ) (M N : ℝ)
    (hM : 0 ≤ M)
    (hmom : ∀ a, |mom a| ≤ M)
    (hcard : (words.card : ℝ) ≤ N ^ (n + 1)) :
    (∑ I ∈ words, ∏ j : Fin (n + 1), |mom (I j)|) ≤
      (M * N) ^ (n + 1) := by
  classical
  have hword (I : Fin (n + 1) → α) :
      (∏ j : Fin (n + 1), |mom (I j)|) ≤ M ^ (n + 1) := by
    calc
      (∏ j : Fin (n + 1), |mom (I j)|) ≤ ∏ _j : Fin (n + 1), M :=
        Finset.prod_le_prod₀
          (fun j _ => abs_nonneg (mom (I j)))
          (fun j _ => hmom (I j))
      _ = M ^ (n + 1) := by simp
  calc
    (∑ I ∈ words, ∏ j : Fin (n + 1), |mom (I j)|) ≤
        ∑ I ∈ words, M ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hword I
    _ = (words.card : ℝ) * M ^ (n + 1) := by simp
    _ ≤ N ^ (n + 1) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hM _)
    _ = (M * N) ^ (n + 1) := by rw [mul_pow]; ring

/-- The source run-count series after applying a uniform operator cost and
partition weight estimate. -/
theorem ccr25_geometric_run_sum (A c B : ℝ)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hsmall : A * c < 1) :
    (∑' n : ℕ, B * A ^ (n + 1) * c ^ n) = B * A / (1 - A * c) := by
  have hratio0 : 0 ≤ A * c := mul_nonneg hA hc
  have hpow (n : ℕ) : B * A ^ (n + 1) * c ^ n = B * A * (A * c) ^ n := by
    rw [pow_succ]
    ring
  calc
    (∑' n : ℕ, B * A ^ (n + 1) * c ^ n) =
        ∑' n : ℕ, B * A * (A * c) ^ n := by
      apply tsum_congr
      intro n
      exact hpow n
    _ = B * A * ∑' n : ℕ, (A * c) ^ n := tsum_mul_left
    _ = B * A * (1 - A * c)⁻¹ := by
      rw [tsum_geometric_of_lt_one hratio0 hsmall]
    _ = B * A / (1 - A * c) := by rw [div_eq_mul_inv]

/-- A nonnegative run series dominated termwise by the source geometric series
is summable and obeys its closed-form bound. -/
theorem ccr25_tsum_le_geometric_run_sum {F : ℕ → ℝ} (A c B : ℝ)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hsmall : A * c < 1)
    (hF0 : ∀ n, 0 ≤ F n)
    (hF : ∀ n, F n ≤ B * A ^ (n + 1) * c ^ n) :
    Summable F ∧ (∑' n, F n) ≤ B * A / (1 - A * c) := by
  have hratio0 : 0 ≤ A * c := mul_nonneg hA hc
  have hpow (n : ℕ) : B * A ^ (n + 1) * c ^ n = B * A * (A * c) ^ n := by
    rw [pow_succ]
    ring
  have hgeom : Summable (fun n : ℕ => B * A * (A * c) ^ n) :=
    (summable_geometric_of_lt_one hratio0 hsmall).mul_left (B * A)
  have hmajor : Summable (fun n : ℕ => B * A ^ (n + 1) * c ^ n) := by
    exact hgeom.congr fun n => (hpow n).symm
  have hFsum : Summable F := Summable.of_nonneg_of_le hF0 hF hmajor
  refine ⟨hFsum, ?_⟩
  calc
    (∑' n, F n) ≤ ∑' n, B * A ^ (n + 1) * c ^ n := hFsum.tsum_le_tsum hF hmajor
    _ = B * A / (1 - A * c) := ccr25_geometric_run_sum A c B hA hc hsmall


end

end Critical2DKPZ.MomentBounds
