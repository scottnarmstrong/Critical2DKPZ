/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.LocalLimit
import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Topology.Order.LiminfLimsup

/-! # Two-sided reciprocal bounds for collision return weights

These are the constants `aMinus, aPlus` used in CSZ25 Section 5. Positivity at every even time
and the period-correct local limit give uniform bounds without an asymptotic cutoff.
-/

@[expose] public noncomputable section

open Critical2DKPZ.Renewal

namespace Critical2DKPZ.MomentBounds

private theorem returnWeight_pos (n : ℕ) : 0 < returnWeight n := by
  have hex : ∃ z ∈ Polymer.endpoints 0 n, 0 < srwKernel n z := by
    have hsum := Polymer.sum_srwKernel_endpoints n 0
    simp only [sub_zero] at hsum
    apply (Finset.sum_pos_iff_of_nonneg (fun z _ => srwKernel_nonneg n z)).1
    rw [hsum]
    exact zero_lt_one
  obtain ⟨z, _, hz⟩ := hex
  have hs : Summable (fun y => srwKernel n y * srwKernel n y) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 n)
    intro y hy
    have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 y hy
    simp only [sub_zero] at h
    rw [h, zero_mul]
  have hcol : (∑' y, srwKernel n y * srwKernel n y) = returnWeight n := by
    simpa only [sub_zero, returnWeight] using Polymer.srwKernel_collision n 0 0
  rw [← hcol]
  exact (mul_pos hz hz).trans_le (hs.le_tsum z (fun y _ => mul_nonneg
    (srwKernel_nonneg n y) (srwKernel_nonneg n y)))

/-- The even-time return probability has positive reciprocal bounds uniform over all positive time gaps. -/
theorem srwKernel_two_mul_zero_bounds :
    ∃ aLo aHi : ℝ, 0 < aLo ∧ aLo ≤ aHi ∧ ∀ n : ℕ, 1 ≤ n →
      aLo / n ≤ srwKernel (2 * n) 0 ∧ srwKernel (2 * n) 0 ≤ aHi / n := by
  obtain ⟨U, hU⟩ := tendsto_returnWeight_moment.bddAbove_range
  have hinv := tendsto_returnWeight_moment.inv₀ (one_div_pos.2 Real.pi_pos).ne'
  obtain ⟨V, hV⟩ := hinv.bddAbove_range
  refine ⟨1 / (|V| + 1), max (1 / (|V| + 1)) (|U| + 1), by positivity,
    le_max_left _ _, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < (n : ℝ) * returnWeight n := mul_pos hn0 (returnWeight_pos n)
  have hl : 1 / (|V| + 1) ≤ (n : ℝ) * returnWeight n := by
    apply (one_div_le (by positivity) hq).2
    simpa only [one_div] using (hV (Set.mem_range_self n)).trans
      ((le_abs_self V).trans (le_add_of_nonneg_right zero_le_one))
  change 1 / (|V| + 1) / n ≤ returnWeight n ∧
    returnWeight n ≤ max (1 / (|V| + 1)) (|U| + 1) / n
  constructor
  · exact (div_le_iff₀ hn0).2 (by simpa only [mul_comm] using hl)
  · apply (le_div_iff₀ hn0).2
    exact (mul_comm _ _).trans_le ((hU (Set.mem_range_self n)).trans
      ((le_abs_self U).trans ((le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _))))

end Critical2DKPZ.MomentBounds
