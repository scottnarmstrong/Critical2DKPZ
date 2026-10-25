/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitGapPotential
public import Critical2DKPZ.SHF.Moments.WordLimitGapSmoothing
public import Critical2DKPZ.SHF.Moments.WordLimitPotentialTimeBound

/-! # A free spectator smooths the weighted gap potential -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

/-- A free walk smooths the gap potential uniformly in both starting points and the remaining horizon, with the stated time envelope. -/
theorem exists_wordGapPotential_smoothing_bound_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ (m n : ℕ) (a b : Site),
      (∑' z : Site, srwKernel m (z - a) * wordGapPotential n (z - b)) ≤
        C * ((∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) +
          2 / Real.sqrt ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hsmooth⟩ := exists_srwKernel_gap_smoothing_bound
  have hkernel (l : ℕ) (z : Site) : srwKernel l z ≤ C / ((l : ℝ) + 1) := by
    let F : Site → ℝ := fun u => if u = z then 1 else 0
    have hF : Summable F := by
      apply summable_of_ne_finset_zero (s := {z})
      intro u hu
      simp only [Finset.mem_singleton] at hu
      exact ite_eq_right hu
    have hF0 (u : Site) : 0 ≤ F u := by dsimp only [F]; split_ifs <;> norm_num
    have hh := hsmooth l 0 F hF0 hF
    simpa [F] using hh
  refine ⟨C, hC, fun m n a b => ?_⟩
  rw [tsum_srwKernel_wordGapPotential]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n,
        C * (1 / (((m : ℝ) + 2 * k + 1) * Real.sqrt ((k : ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := div_le_div_of_nonneg_right (hkernel (m + 2 * k) (b - a))
        (Real.sqrt_nonneg ((k : ℝ) + 1))
      push_cast at hh
      exact hh.trans_eq (by rw [div_div, mul_one_div])
    _ = C * ∑ k ∈ Finset.Icc 1 n,
        1 / (((m : ℝ) + 2 * k + 1) * Real.sqrt ((k : ℝ) + 1)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_gapPotential_convolution_time_le m n) hC.le

end Critical2DKPZ.SHF.Moments
