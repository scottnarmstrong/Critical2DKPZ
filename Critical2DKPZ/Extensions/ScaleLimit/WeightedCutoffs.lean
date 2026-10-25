/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Finite cutoff weights for Cramér–Wold projections of partial sums -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The coefficient of summand `j` in a finite projection of nested partial sums. -/
def cutoffWeight {I : Type*} [Fintype I] (n : I → ℕ) (v : I → ℝ) (j : ℕ) : ℝ :=
  ∑ i, if j < n i then v i else 0

/-- Cutoff coefficients have a bound independent of the cutoff indices. -/
theorem abs_cutoffWeight_le {I : Type*} [Fintype I] (n : I → ℕ) (v : I → ℝ) (j : ℕ) :
    |cutoffWeight n v j| ≤ ∑ i, |v i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> simp [abs_nonneg]

/-- A finite projection of partial sums is the sum with the cutoff coefficients. -/
theorem sum_cutoffWeight_eq {I : Type*} [Fintype I]
    (n : I → ℕ) (v : I → ℝ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Finset.univ.sup n), cutoffWeight n v j * f j) =
      ∑ i, (∑ j ∈ Finset.range (n i), f j) * v i := by
  classical
  simp only [cutoffWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hni : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  calc
    (∑ j ∈ Finset.range (Finset.univ.sup n), (if j < n i then v i else 0) * f j) =
        ∑ j ∈ Finset.range (Finset.univ.sup n), if j < n i then f j * v i else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp [mul_comm]
    _ = ∑ j ∈ Finset.range (n i), f j * v i := by
      rw [← Finset.sum_filter]
      have heq : (Finset.range (Finset.univ.sup n)).filter (fun j => j < n i) = Finset.range (n i) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [heq]

end Critical2DKPZ.Extensions.ScaleLimit
