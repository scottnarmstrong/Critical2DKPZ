/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.Blocks
public import Critical2DKPZ.Definitions.BlockTime
import Critical2DKPZ.Blocks.GridAlignment
import Critical2DKPZ.SHF.Symmetries.LatticeReversalDiscrete
import Mathlib.Tactic

/-! # Exact dictionary between reversed lattice blocks and geometric times

We take even lattice sizes so that the terminal lattice time is also its
rounded continuum time. All other endpoints agree exactly once the block
count exceeds the fixed reversed index.
-/

@[expose] public noncomputable section

open Filter

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- At a fixed interior reversed index the lattice clock is exactly the rounded
geometric time, rather than merely asymptotic to it. -/
theorem blockTime_reverse_eq {ρ : ℝ} (hρ : 1 < ρ) (N j : ℕ)
    (hj : 0 < j) (hK : j < blockCount N ρ) :
    blockTime N ρ (blockCount N ρ - j) = evenCeil ((N : ℝ) * tau ρ j) := by
  have hi0 : blockCount N ρ - j ≠ 0 := by omega
  have hiK : blockCount N ρ - j < blockCount N ρ := by omega
  rw [blockTime, ite_eq_right hi0, ite_eq_left hiK]
  have hcast : ((blockCount N ρ - j : ℕ) : ℝ) - (blockCount N ρ : ℝ) = -(j : ℝ) := by
    rw [Nat.cast_sub hK.le]
    ring
  rw [hcast, Real.rpow_neg (le_of_lt (lt_trans zero_lt_one hρ)), Real.rpow_natCast]
  rw [tau, inv_pow]

/-- The same dictionary includes reversed index zero on even lattice sizes. -/
theorem blockTime_reverse_eq_of_even {ρ : ℝ} (hρ : 1 < ρ) (N j : ℕ)
    (hN : Even N) (hK : j < blockCount N ρ) :
    blockTime N ρ (blockCount N ρ - j) = evenCeil ((N : ℝ) * tau ρ j) := by
  by_cases hj : j = 0
  · subst j
    simp only [Nat.sub_zero, tau, pow_zero, mul_one]
    rw [blockTime, ite_eq_right (by omega), ite_eq_right (lt_irrefl _)]
    exact (SHF.Symmetries.evenCeil_natCast_of_even hN).symm
  · exact blockTime_reverse_eq hρ N j (Nat.pos_of_ne_zero hj) hK

/-- The exact reversed clock dictionary holds eventually at every fixed index. -/
theorem eventually_blockTime_reverse_eq {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) :
    ∀ᶠ N : ℕ in atTop, blockTime (2 * N) ρ (blockCount (2 * N) ρ - j) =
      evenCeil ((2 * N : ℕ) * tau ρ j) := by
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  filter_upwards [((Blocks.blockCount_tendsto_atTop hρ).comp h2).eventually_gt_atTop j] with N hN
  exact blockTime_reverse_eq_of_even hρ (2 * N) j (even_two_mul N) hN

end Critical2DKPZ.Extensions.ScaleLimit
