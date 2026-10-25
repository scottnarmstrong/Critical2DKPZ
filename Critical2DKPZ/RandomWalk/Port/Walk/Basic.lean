/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.RandomWalk.Port.Site

/-! # Signed coordinate directions

A direction consists of a coordinate and a sign; summing over these directions gives
the nearest-neighbour sum and the simple random walk averaging operator. -/

@[expose] public section

namespace LatticeProb

open Finset

/-- A direction: a coordinate together with a sign.  There are `2d` of them. -/
abbrev Dir (d : ℕ) := Fin d × Bool

/-- The unit vector `± e_i` named by a direction. -/
def dirVec {d : ℕ} (a : Dir d) : Site d :=
  fun j => if j = a.1 then (if a.2 then 1 else -1) else 0

/-- The positive directions are the unit vectors of `LatticeProb.Site`. -/
theorem dirVec_eq_unit {d : ℕ} (i : Fin d) : dirVec ((i, true) : Dir d) = unit i := by
  funext j
  by_cases h : j = i <;> simp [dirVec, unit, h]

/-- The negative directions are the negated unit vectors. -/
theorem dirVec_eq_neg_unit {d : ℕ} (i : Fin d) : dirVec ((i, false) : Dir d) = -unit i := by
  funext j
  by_cases h : j = i <;> simp [dirVec, unit, h]





/-- A sum over the neighbours of `x` in the sense of `LatticeProb.nbrSum` is a
sum over the `2d` directions. -/
theorem nbrSum_eq_sum_dir {d : ℕ} (u : Site d → ℝ) (x : Site d) :
    nbrSum u x = ∑ a : Dir d, u (x + dirVec a) := by
  rw [nbrSum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, dirVec_eq_unit, dirVec_eq_neg_unit, ← sub_eq_add_neg]

/-- The simple random walk operator averages over the `2d` directions. -/
theorem walkOp_eq_sum_dir {d : ℕ} (u : Site d → ℝ) (x : Site d) :
    walkOp u x = (∑ a : Dir d, u (x + dirVec a)) / (2 * d) := by
  rw [walkOp, nbrSum_eq_sum_dir]

end LatticeProb

end
