/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitBounds
public import Critical2DKPZ.SHF.Moments.WordLimitWeightedEntrance
import Mathlib.Tactic

/-! # Potential domination away from the first collision diagonal -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The weighted entrance estimate bounds the potential away from zero
without iterating the inverse-fourth bound through successive collisions. -/
theorem exists_wordGapPotential_inverse_fourth_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : Site), 0 < ‖siteToPlane z‖ →
      wordGapPotential n z ≤ C * n * Real.sqrt ((n : ℝ) + 1) / ‖siteToPlane z‖ ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := sum_weighted_entrance_le_inverse_fourth
  refine ⟨C, hC, fun n z hz => ?_⟩
  have hslice (s : ℕ) (hs : s ∈ Finset.Icc 1 n) :
      srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1) ≤
        Real.sqrt ((n : ℝ) + 1) * (srwKernel (2 * s) z / ((s : ℝ) + 1)) := by
    have hfactor : srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1) =
        Real.sqrt ((s : ℝ) + 1) * (srwKernel (2 * s) z / ((s : ℝ) + 1)) := by
      calc
        _ = srwKernel (2 * s) z * (Real.sqrt ((s : ℝ) + 1))⁻¹ := div_eq_mul_inv _ _
        _ = srwKernel (2 * s) z * (Real.sqrt ((s : ℝ) + 1) / ((s : ℝ) + 1)) := by
          rw [Real.sqrt_div_self]
        _ = _ := by ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (add_le_add (Nat.cast_le.mpr (Finset.mem_Icc.mp hs).2) le_rfl))
      (div_nonneg (srwKernel_nonneg _ _) (by positivity))
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n,
        Real.sqrt ((n : ℝ) + 1) * (srwKernel (2 * s) z / ((s : ℝ) + 1)) :=
      Finset.sum_le_sum hslice
    _ = Real.sqrt ((n : ℝ) + 1) *
        ∑ s ∈ Finset.Icc 1 n, srwKernel (2 * s) z / ((s : ℝ) + 1) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt ((n : ℝ) + 1) * (C * n / ‖siteToPlane z‖ ^ 4) :=
      mul_le_mul_of_nonneg_left (hbound n z hz) (Real.sqrt_nonneg _)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments
