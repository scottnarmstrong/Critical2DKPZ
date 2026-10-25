/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim

/-! # One-dimensional simple and lazy walk kernels

Two simple walk steps give a lazy step after dividing space by two; consequently
the simple walk kernel is bounded by `√2 / √(n+1)` at every site. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

/-- The `ℓ¹` norm of a one-dimensional site is the absolute value. -/
theorem graphNorm_one (a : ℤ) : graphNorm (![a] : Site 1) = a.natAbs := by
  simp [graphNorm]

/-- The simple walk at an even time and an even site is the lazy walk. -/
theorem srwHeat_one_two_mul (m : ℕ) (k : ℤ) :
    srwHeat 1 (2 * m) ![2 * k] = P1 m k := by
  induction m generalizing k with
  | zero =>
      rw [P1_zero_step]
      simp only [Nat.mul_zero]
      by_cases hk : k = 0
      · subst hk
        norm_num
        funext i
        exact i.elim0
      · rw [ite_eq_right hk, srwHeat_zero, ite_eq_right]
        intro hc
        apply hk
        have : (![2 * k] : Site 1) 0 = (0 : Site 1) 0 := by rw [hc]
        simp at this
        omega
  | succ m ih =>
      have hstep : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [hstep, srwHeat_one_succ, srwHeat_one_succ, srwHeat_one_succ]
      have e1 : 2 * k - 1 - 1 = 2 * (k - 1) := by ring
      have e2 : 2 * k - 1 + 1 = 2 * k := by ring
      have e3 : 2 * k + 1 - 1 = 2 * k := by ring
      have e4 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [e1, e2, e3, e4, ih, ih, ih]
      rw [P1_succ]
      ring

/-- At an even time the kernel is bounded by the peak of the lazy kernel. -/
theorem srwHeat_one_even_le (m : ℕ) (j : ℤ) :
    srwHeat 1 (2 * m) ![j] ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
  rcases Int.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hj : j = 2 * k := by omega
    subst hj
    calc srwHeat 1 (2 * m) ![2 * k] = P1 m k := srwHeat_one_two_mul m k
      _ ≤ P1 m 0 := P1_le_max m k
      _ ≤ 1 / Real.sqrt ((m : ℝ) + 1) := P1_zero_le_inv_sqrt m
  · have hzero : srwHeat 1 (2 * m) ![j] = 0 := by
      refine srwHeat_eq_zero_of_parity ?_
      rw [graphNorm_one]
      have hpar : ((j.natAbs : ℕ) : ZMod 2) = 1 := by
        rw [natAbs_cast_zmod, hk]
        push_cast
        ring_nf
        rw [show ((2 : ZMod 2)) = 0 by decide]
        ring
      have hpar2 : (((2 * m : ℕ)) : ZMod 2) = 0 := by
        push_cast
        rw [show ((2 : ZMod 2)) = 0 by decide]
        ring
      rw [hpar, hpar2]
      decide
    rw [hzero]
    positivity

/-- The sup bound on the one-dimensional simple kernel. -/
theorem srwHeat_one_le (n : ℕ) (j : ℤ) :
    srwHeat 1 n ![j] ≤ Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn : n = 2 * m := by omega
    subst hn
    refine le_trans (srwHeat_one_even_le m j) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.sqrt (((2 * m : ℕ) : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      push_cast
      ring_nf
      linarith
    linarith
  · have hn : n = 2 * m + 1 := by omega
    subst hn
    rw [srwHeat_one_succ]
    have hb1 := srwHeat_one_even_le m (j - 1)
    have hb2 := srwHeat_one_even_le m (j + 1)
    have hval : Real.sqrt 2 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ) + 1)
        = 1 / Real.sqrt ((m : ℝ) + 1) := by
      have h2 : (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * ((m : ℝ) + 1) := by push_cast; ring
      rw [h2, Real.sqrt_mul (by norm_num)]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [hval]
    linarith


/-! ### The binomial form of the one-dimensional kernel -/

/-- **The one-dimensional kernel is the binomial law.**  A path of `a + b` steps
ending at `a - b` takes `a` steps to the right and `b` to the left, and there are
`C(a+b, a)` such paths out of `2^{a+b}`. -/
theorem srwHeat_one_binom : ∀ (n a b : ℕ), a + b = n →
    srwHeat 1 n ![(a : ℤ) - (b : ℤ)] = (Nat.choose n a : ℝ) / 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro a b hab
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      have hz : (![(0 : ℤ)] : Site 1) = 0 := by funext i; fin_cases i; rfl
      simp only [Nat.cast_zero, sub_zero]
      rw [hz, srwHeat_zero, ite_eq_left rfl]
      norm_num
  | succ n ih =>
      intro a b hab
      rcases a with _ | a
      · have hb : b = n + 1 := by omega
        subst hb
        rw [show ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) by push_cast; ring,
          srwHeat_one_succ]
        rw [show -((n : ℤ) + 1) - 1 = -((n : ℤ) + 2) by ring,
          show -((n : ℤ) + 1) + 1 = ((0 : ℕ) : ℤ) - ((n : ℕ) : ℤ) by push_cast; ring]
        rw [srwHeat_eq_zero_of_lt (d := 1) (j := n) (x := (![-((n : ℤ) + 2)] : Site 1)) (by
          rw [graphNorm_one]; omega), ih 0 n (by omega)]
        rw [Nat.choose_zero_right, Nat.choose_zero_right, pow_succ]
        push_cast
        ring
      · rcases b with _ | b
        · have ha : a = n := by omega
          subst ha
          rw [show ((a + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (a : ℤ) + 1 by push_cast; ring,
            srwHeat_one_succ]
          rw [show (a : ℤ) + 1 - 1 = ((a : ℕ) : ℤ) - ((0 : ℕ) : ℤ) by push_cast; ring,
            show (a : ℤ) + 1 + 1 = (a : ℤ) + 2 by ring]
          rw [srwHeat_eq_zero_of_lt (d := 1) (j := a) (x := (![(a : ℤ) + 2] : Site 1)) (by
            rw [graphNorm_one]; omega), ih a 0 (by omega)]
          rw [Nat.choose_self, Nat.choose_self, pow_succ]
          push_cast
          ring
        · rw [srwHeat_one_succ]
          rw [show ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) - 1
                = ((a : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) by push_cast; ring,
            show ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) + 1
                = ((a + 1 : ℕ) : ℤ) - ((b : ℕ) : ℤ) by push_cast; ring]
          rw [ih a (b + 1) (by omega), ih (a + 1) b (by omega), Nat.choose_succ_succ' n a]
          push_cast
          rw [pow_succ]
          ring

end LatticeProb

end
