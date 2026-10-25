/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.Decomp

/-! # Exponential moments of coordinate counts

A coordinate count under the uniform law on schedules is binomial with success
probability `1/d`; its exponential moment yields a Chernoff lower-tail bound. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}


/-- `∑_c u^{N_i(c)} = (u + d - 1)^r`: each of the `r` steps contributes `u` if it
selects coordinate `i` and `1` otherwise. -/
theorem sum_pow_cnt (r : ℕ) (i : Fin d) (u : ℝ) :
    ∑ c : Fin r → Fin d, u ^ (cnt c i) = (u + ((d : ℝ) - 1)) ^ r := by
  -- Each schedule contributes a product over the `r` steps, with `u` at the steps
  -- that select `i`; the number of such steps is `cnt c i`.
  have hA : ∀ c : Fin r → Fin d, ∏ t : Fin r, (if c t = i then u else 1) = u ^ (cnt c i) := by
    intro c
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Finset.card_filter]
    rfl
  -- One step contributes `u` from the coordinate `i` and `1` from each of the other `d - 1`.
  have hC : ∑ j : Fin d, (if j = i then u else 1) = u + ((d : ℝ) - 1) := by
    have h : ∀ j : Fin d, (if j = i then u else 1) = 1 + (if j = i then u - 1 else 0) := by
      intro j; split <;> ring
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    ring
  -- Expanding the `r`-th power of the one-step sum enumerates the schedules.
  rw [← hC, Fintype.sum_pow (fun j : Fin d => (if j = i then u else 1)) r]
  exact Finset.sum_congr rfl fun c _ => (hA c).symm


/-- A Chernoff bound for the number of updates of one coordinate:
`#{c : N_i(c) ≤ r/(4d)} ≤ d^r e^{-r/(4d)}`, in the form of a sum of indicators. -/
theorem sum_indicator_cnt_le (hd : 0 < d) (r : ℕ) (i : Fin d) :
    ∑ c : Fin r → Fin d, (if cnt c i ≤ r / (4 * d) then (1 : ℝ) else 0)
      ≤ (d : ℝ) ^ r * Real.exp (-(r : ℝ) / (4 * (d : ℝ))) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set a : ℕ := r / (4 * d) with ha
  have hrw : ∀ n : ℕ, Real.exp (a : ℝ) * Real.exp (-1) ^ n = Real.exp ((a : ℝ) - (n : ℝ)) := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  -- Markov's inequality for the exponential moment: the indicator of `N_i ≤ a` is at most
  -- `e^{a - N_i}`, since that exponent is nonnegative exactly on the indicated event.
  have hpt : ∀ c : Fin r → Fin d,
      (if cnt c i ≤ a then (1 : ℝ) else 0) ≤ Real.exp (a : ℝ) * Real.exp (-1) ^ (cnt c i) := by
    intro c
    rw [hrw (cnt c i)]
    split
    · rename_i hle
      refine Real.one_le_exp ?_
      have : ((cnt c i : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    · exact le_of_lt (Real.exp_pos _)
  have hstep1 : ∑ c : Fin r → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
      ≤ Real.exp (a : ℝ) * (Real.exp (-1) + ((d : ℝ) - 1)) ^ r := by
    calc ∑ c : Fin r → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
        ≤ ∑ c : Fin r → Fin d, Real.exp (a : ℝ) * Real.exp (-1) ^ (cnt c i) :=
          Finset.sum_le_sum fun c _ => hpt c
      _ = Real.exp (a : ℝ) * ∑ c : Fin r → Fin d, Real.exp (-1) ^ (cnt c i) := by
          rw [Finset.mul_sum]
      _ = Real.exp (a : ℝ) * (Real.exp (-1) + ((d : ℝ) - 1)) ^ r := by
          rw [sum_pow_cnt r i (Real.exp (-1))]
  -- `e^{-1} ≤ 1/2`, so the one-step factor loses `1/2` out of `d`.
  have hem1 : Real.exp (-1) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1)]
  have hbase_le : Real.exp (-1) + ((d : ℝ) - 1) ≤ (d : ℝ) * Real.exp (-(1 / (2 * (d : ℝ)))) := by
    have h2 : -(1 / (2 * (d : ℝ))) + 1 ≤ Real.exp (-(1 / (2 * (d : ℝ)))) :=
      Real.add_one_le_exp _
    have h3 : (d : ℝ) * (-(1 / (2 * (d : ℝ))) + 1) ≤ (d : ℝ) * Real.exp (-(1 / (2 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hdR)
    have h4 : (d : ℝ) * (-(1 / (2 * (d : ℝ))) + 1) = (d : ℝ) - 1 / 2 := by
      field_simp
      ring
    linarith
  have hbase_nonneg : (0 : ℝ) ≤ Real.exp (-1) + ((d : ℝ) - 1) := by
    have := Real.exp_pos (-1)
    linarith
  have hpow : (Real.exp (-1) + ((d : ℝ) - 1)) ^ r
      ≤ ((d : ℝ) * Real.exp (-(1 / (2 * (d : ℝ))))) ^ r :=
    pow_le_pow_left₀ hbase_nonneg hbase_le r
  have hRHS : ((d : ℝ) * Real.exp (-(1 / (2 * (d : ℝ))))) ^ r
      = (d : ℝ) ^ r * Real.exp (-(r : ℝ) / (2 * (d : ℝ))) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    field_simp
  -- Natural division only shrinks: `a ≤ r/(4d)` over the reals.
  have haR : (a : ℝ) ≤ (r : ℝ) / (4 * (d : ℝ)) := by
    have h := Nat.cast_div_le (α := ℝ) (m := r) (n := 4 * d)
    rw [ha]
    push_cast at h ⊢
    exact h
  calc ∑ c : Fin r → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
      ≤ Real.exp (a : ℝ) * (Real.exp (-1) + ((d : ℝ) - 1)) ^ r := hstep1
    _ ≤ Real.exp (a : ℝ) * ((d : ℝ) ^ r * Real.exp (-(r : ℝ) / (2 * (d : ℝ)))) := by
        rw [← hRHS]
        exact mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
    _ = (d : ℝ) ^ r * Real.exp ((a : ℝ) + -(r : ℝ) / (2 * (d : ℝ))) := by
        rw [Real.exp_add]; ring
    _ ≤ (d : ℝ) ^ r * Real.exp (-(r : ℝ) / (4 * (d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have hq : -(r : ℝ) / (2 * (d : ℝ)) = -(2 * ((r : ℝ) / (4 * (d : ℝ)))) := by
          field_simp
          ring
        rw [hq, neg_div]
        linarith

end LatticeProb

end
