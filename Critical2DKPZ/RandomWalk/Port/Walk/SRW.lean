/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.Basic

/-! # The simple random walk kernel and its parity constraint

Iterating the nearest-neighbour averaging operator from the unit atom at the origin
gives a kernel supported inside the graph-distance ball and on the parity class of time. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The `ℓ¹` norm of a site -/

/-- The graph distance from the origin: the `ℓ¹` norm of a site. -/
def graphNorm {d : ℕ} (x : Site d) : ℕ := ∑ i, (x i).natAbs

/-- The graph norm of the lattice origin is zero. -/
@[simp] theorem graphNorm_zero : graphNorm (0 : Site d) = 0 := by simp [graphNorm]


/-- The lattice graph norm satisfies the triangle inequality. -/
theorem graphNorm_add_le (x y : Site d) :
    graphNorm (x + y) ≤ graphNorm x + graphNorm y := by
  rw [graphNorm, graphNorm, graphNorm, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

/-- Negating a lattice site preserves its graph norm. -/
theorem graphNorm_neg (x : Site d) : graphNorm (-x) = graphNorm x := by
  simp [graphNorm]

/-- Each nearest-neighbor direction has graph norm one. -/
@[simp] theorem graphNorm_dirVec (a : Dir d) : graphNorm (dirVec a) = 1 := by
  classical
  rw [graphNorm]
  rw [Finset.sum_eq_single a.1]
  · cases hb : a.2 <;> simp [dirVec, hb]
  · intro i _ hi; simp [dirVec, hi]
  · intro h; exact absurd (Finset.mem_univ a.1) h

/-- A site's graph norm is at most one plus the graph norm after a nearest-neighbor step. -/
theorem graphNorm_le_succ_of_add_dirVec (x : Site d) (a : Dir d) :
    graphNorm x ≤ graphNorm (x + dirVec a) + 1 := by
  have h := graphNorm_add_le (x + dirVec a) (-dirVec a)
  simpa [graphNorm_neg] using h

/-- An integer and its absolute value agree modulo two. -/
theorem natAbs_cast_zmod (n : ℤ) : ((n.natAbs : ℕ) : ZMod 2) = (n : ZMod 2) := by
  rcases Int.natAbs_eq n with h | h
  · conv_rhs => rw [h]
    rw [Int.cast_natCast]
  · conv_rhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, CharTwo.neg_eq]

/-- The `ℓ¹` norm and the sum of the coordinates agree in parity. -/
theorem graphNorm_cast_zmod (x : Site d) :
    ((graphNorm x : ℕ) : ZMod 2) = ((∑ i, x i : ℤ) : ZMod 2) := by
  rw [graphNorm]
  push_cast
  exact Finset.sum_congr rfl fun i _ => natAbs_cast_zmod (x i)

/-- A nearest-neighbor step changes graph-norm parity. -/
theorem graphNorm_add_dirVec_zmod (x : Site d) (a : Dir d) :
    ((graphNorm (x + dirVec a) : ℕ) : ZMod 2) = ((graphNorm x : ℕ) : ZMod 2) + 1 := by
  classical
  rw [graphNorm_cast_zmod, graphNorm_cast_zmod]
  have hsum : (∑ i, (x + dirVec a) i) = (∑ i, x i) + (∑ i, dirVec a i) := by
    simp [Finset.sum_add_distrib]
  have hd : (∑ i, dirVec a i) = if a.2 then (1 : ℤ) else -1 := by
    rw [Finset.sum_eq_single a.1]
    · cases hb : a.2 <;> simp [dirVec, hb]
    · intro i _ hi; simp [dirVec, hi]
    · intro h; exact absurd (Finset.mem_univ a.1) h
  rw [hsum, hd]
  cases hb : a.2
  · rw [ite_eq_right (by simp)]
    push_cast
    rw [CharTwo.neg_eq]
  · rw [ite_eq_left (by simp)]
    push_cast
    ring

/-! ### The kernel -/

/-- `P^j(0, x)`, the `j`-step transition probability of the simple random walk
started at the origin. -/
noncomputable def srwHeat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => walkOp (srwHeat d j) x


/-- The simple-walk heat kernel at zero time is the point mass at the origin. -/
@[simp] theorem srwHeat_zero (x : Site d) :
    srwHeat d 0 x = if x = 0 then 1 else 0 := rfl

/-- The next simple-walk heat kernel is obtained by applying the walk averaging operator. -/
@[simp] theorem srwHeat_succ (j : ℕ) (x : Site d) :
    srwHeat d (j + 1) x = walkOp (srwHeat d j) x := rfl

/-- The simple-walk heat kernel at the next time is the average over nearest-neighbor directions. -/
theorem srwHeat_succ_eq_sum_dir (j : ℕ) (x : Site d) :
    srwHeat d (j + 1) x = (∑ a : Dir d, srwHeat d j (x + dirVec a)) / (2 * d) := by
  rw [srwHeat_succ, walkOp_eq_sum_dir]



/-- The simple-walk heat kernel is nonnegative. -/
theorem srwHeat_nonneg (j : ℕ) (x : Site d) : 0 ≤ srwHeat d j x := by
  induction j generalizing x with
  | zero => by_cases h : x = 0 <;> simp [h]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      exact div_nonneg (Finset.sum_nonneg fun a _ => ih _) (by positivity)


/-- The kernel vanishes outside the ball of radius `j`. -/
theorem srwHeat_eq_zero_of_lt {j : ℕ} {x : Site d} (h : j < graphNorm x) :
    srwHeat d j x = 0 := by
  induction j generalizing x with
  | zero =>
      have hx : x ≠ 0 := fun hx => by simp [hx] at h
      simp [hx]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      have : ∀ a : Dir d, srwHeat d j (x + dirVec a) = 0 := by
        intro a
        refine ih ?_
        have := graphNorm_le_succ_of_add_dirVec x a
        omega
      simp [this]

/-- Inside the ball the kernel still vanishes unless the parity of the `ℓ¹`
norm agrees with the parity of the time. -/
theorem srwHeat_eq_zero_of_parity {j : ℕ} {x : Site d}
    (h : ((graphNorm x : ℕ) : ZMod 2) ≠ ((j : ℕ) : ZMod 2)) : srwHeat d j x = 0 := by
  induction j generalizing x with
  | zero =>
      have hx : x ≠ 0 := by
        rintro rfl
        exact h (by simp)
      simp [hx]
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      have : ∀ a : Dir d, srwHeat d j (x + dirVec a) = 0 := by
        intro a
        refine ih ?_
        rw [graphNorm_add_dirVec_zmod]
        intro hcon
        apply h
        push_cast
        rw [← hcon, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      simp [this]

end LatticeProb

namespace LatticeProb

open Finset

/-! ### The one-dimensional nearest-neighbour recursion -/

/-- In dimension one the kernel satisfies the nearest-neighbour recursion. -/
theorem srwHeat_one_succ (m : ℕ) (a : ℤ) :
    srwHeat 1 (m + 1) ![a] = (srwHeat 1 m ![a - 1] + srwHeat 1 m ![a + 1]) / 2 := by
  rw [srwHeat_succ_eq_sum_dir]
  have hplus : (![a] : Site 1) + dirVec ((0, true) : Dir 1) = ![a + 1] := by
    funext i
    fin_cases i
    simp [dirVec]
  have hminus : (![a] : Site 1) + dirVec ((0, false) : Dir 1) = ![a - 1] := by
    funext i
    fin_cases i
    simp [dirVec, sub_eq_add_neg]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one, Fintype.sum_bool]
  rw [hplus, hminus, Nat.cast_one, mul_one, add_comm]





end LatticeProb

end
