/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.CSZ23

/-! # Nearest even-lattice points in three dimensions

For the cell construction in CSZ23, the origin is the unique nearest even-lattice point to `(2/5, 2/5, 2/5)`, which lies outside the stated open diamond. -/

@[expose] public section
namespace Critical2DKPZ.Errata

/-- In dimension three, the open diamond can omit a point uniquely closest to the even-lattice origin. -/
theorem csz23_even_cell_strict_counterexample :
    2 ≤ (3 : ℕ) ∧ Even (∑ i : Fin 3, (0 : Fin 3 → ℤ) i) ∧
    ¬ (∑ i : Fin 3, |(2 / 5 : ℝ) - ((0 : Fin 3 → ℤ) i : ℝ)|) < 1 ∧
    ∀ v : Fin 3 → ℤ, Even (∑ i, v i) → v ≠ 0 →
      (∑ i : Fin 3, ((2 / 5 : ℝ) - ((0 : Fin 3 → ℤ) i : ℝ)) ^ 2) <
        ∑ i : Fin 3, ((2 / 5 : ℝ) - (v i : ℝ)) ^ 2 := by
  obtain ⟨hout, hnear⟩ := csz23_three_dimensional_cell_counterexample
  refine ⟨by decide, by simp, ?_, ?_⟩
  · simpa using not_lt.mpr hout.le
  · intro v _ hv
    simpa using hnear v hv

end Critical2DKPZ.Errata
