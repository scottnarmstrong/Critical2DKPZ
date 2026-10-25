/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # The general-dimensional cell assertion in CSZ23

At x=(2/5,2/5,2/5), zero is the unique closest integer vector, hence also
the unique closest even integer vector, although its ℓ¹ distance exceeds one.
Source: arXiv:2109.03766v3, equation (3.5).
-/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata

private theorem integer_coordinate_square (k : ℤ) :
    (2 / 5 : ℝ) ^ 2 ≤ (2 / 5 - (k : ℝ)) ^ 2 ∧
      (k ≠ 0 → (2 / 5 : ℝ) ^ 2 < (2 / 5 - (k : ℝ)) ^ 2) := by
  rcases (show k ≤ -1 ∨ k = 0 ∨ 1 ≤ k by omega) with hk | hk | hk
  · have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    constructor
    · nlinarith only [hr, sq_nonneg ((k : ℝ) + 1)]
    · intro _
      nlinarith only [hr, sq_nonneg ((k : ℝ) + 1)]
  · subst k
    norm_num
  · have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    constructor
    · nlinarith only [hr, sq_nonneg ((k : ℝ) - 1)]
    · intro _
      nlinarith only [hr, sq_nonneg ((k : ℝ) - 1)]

/-- In dimension three, a point can have a unique nearest even-lattice point while lying outside its proposed open diamond. -/
theorem csz23_three_dimensional_cell_counterexample :
    1 < ∑ _i : Fin 3, |(2 / 5 : ℝ)| ∧
      ∀ v : Fin 3 → ℤ, v ≠ 0 →
        (∑ _i : Fin 3, (2 / 5 : ℝ) ^ 2) <
          ∑ i : Fin 3, (2 / 5 - (v i : ℝ)) ^ 2 := by
  constructor
  · norm_num
  · intro v hv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    apply Finset.sum_lt_sum
    · intro j _
      exact (integer_coordinate_square (v j)).1
    · exact ⟨i, Finset.mem_univ _, (integer_coordinate_square (v i)).2 hi⟩

end Critical2DKPZ.Errata
