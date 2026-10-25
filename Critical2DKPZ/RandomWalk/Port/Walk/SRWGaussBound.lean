/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.SRWGauss
public import Critical2DKPZ.RandomWalk.Port.Walk.SRWDecomp
import Critical2DKPZ.RandomWalk.Port.Walk.S1Gauss

/-!
The Gaussian upper bound on the simple random walk kernel.

Each coordinate of the walk, run for `N_i` of the `r` steps, contributes a
one-dimensional factor bounded by `3 (N_i+1)^{-1/2} exp(-x_i^2 / (8(N_i+2)))`.
The exponents add, and Sedrakyan's inequality turns the sum
`∑_i x_i^2/(N_i+2)` into `|x|_1^2 / ∑_i (N_i+2) = |x|_1^2 / (r + 2d)`, which no
longer depends on the schedule.  The Gaussian factor therefore comes out of the
schedule average, and what is left is the average of `∏_i (N_i+1)^{-1/2}`, which
is of order `r^{-d/2}`.  The bound is in the `ℓ¹` norm, hence stronger than the
usual Euclidean form.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The product kernel against a Gaussian factor, given the one-dimensional bound. -/
theorem KS_gaussian_of
    (hS : ∀ (n : ℕ) (k : ℤ), S1 n k
        ≤ 3 / Real.sqrt ((n : ℝ) + 1) * Real.exp (-((k : ℝ) ^ 2) / (8 * ((n : ℝ) + 2))))
    (n : Fin d → ℕ) (x : Site d) :
    KS n x ≤ 3 ^ d * (∏ i, (1 : ℝ) / Real.sqrt ((n i : ℝ) + 1))
      * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, ((n i : ℝ) + 2)))) := by
  have hstep : KS n x
      ≤ ∏ i, (3 / Real.sqrt ((n i : ℝ) + 1)
          * Real.exp (-((x i : ℝ)) ^ 2 / (8 * ((n i : ℝ) + 2)))) := by
    unfold KS
    refine Finset.prod_le_prod₀ (fun i _ => S1_nonneg _ _) (fun i _ => hS (n i) (x i))
  have hsplit : ∀ i : Fin d, (3 : ℝ) / Real.sqrt ((n i : ℝ) + 1)
      = 3 * ((1 : ℝ) / Real.sqrt ((n i : ℝ) + 1)) := fun i => by ring
  have hfac : ∏ i, (3 : ℝ) / Real.sqrt ((n i : ℝ) + 1)
      = 3 ^ d * ∏ i, (1 : ℝ) / Real.sqrt ((n i : ℝ) + 1) := by
    rw [Finset.prod_congr rfl fun i _ => hsplit i, Finset.prod_mul_distrib]
    simp
  have hEq : ∏ i, (3 / Real.sqrt ((n i : ℝ) + 1)
          * Real.exp (-((x i : ℝ)) ^ 2 / (8 * ((n i : ℝ) + 2))))
      = (3 ^ d * ∏ i, (1 : ℝ) / Real.sqrt ((n i : ℝ) + 1))
        * ∏ i, Real.exp (-((x i : ℝ)) ^ 2 / (8 * ((n i : ℝ) + 2))) := by
    rw [Finset.prod_mul_distrib, hfac]
  refine hstep.trans ?_
  rw [hEq]
  have hnn : (0 : ℝ) ≤ 3 ^ d * ∏ i, (1 : ℝ) / Real.sqrt ((n i : ℝ) + 1) :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => by positivity)
  exact mul_le_mul_of_nonneg_left (prod_exp_le x n) hnn

/-- The Gaussian upper bound on the simple walk kernel, given the one-dimensional bound. -/
theorem srwHeat_gaussian_of
    (hS : ∀ (n : ℕ) (k : ℤ), S1 n k
        ≤ 3 / Real.sqrt ((n : ℝ) + 1) * Real.exp (-((k : ℝ) ^ 2) / (8 * ((n : ℝ) + 2))))
    (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (x : Site d) :
    srwHeat d R x ≤ 3 ^ d * greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2)
      * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((R : ℝ) + 2 * d))) := by
  have hdRpow : (0 : ℝ) < (d : ℝ) ^ R := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  set E : ℝ := Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((R : ℝ) + 2 * d))) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hterm : ∀ c : Fin R → Fin d,
      KS (cnt c) x ≤ 3 ^ d * (∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) * E := by
    intro c
    have := KS_gaussian_of hS (cnt c) x
    rwa [sum_cnt_add_two c] at this
  have hsum : (∑ c : Fin R → Fin d, KS (cnt c) x)
      ≤ 3 ^ d * E * (∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have := hterm c
    calc KS (cnt c) x ≤ 3 ^ d * (∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) * E := this
      _ = 3 ^ d * E * ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) := by ring
  rw [srwHeat_eq_sched hd R x]
  rw [div_le_iff₀ hdRpow]
  have havg := sched_avg_le (d := d) hd hR
  rw [div_le_iff₀ hdRpow] at havg
  calc (∑ c : Fin R → Fin d, KS (cnt c) x)
      ≤ 3 ^ d * E * (∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) := hsum
    _ ≤ 3 ^ d * E * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) * (d : ℝ) ^ R) := by
        refine mul_le_mul_of_nonneg_left havg ?_
        positivity
    _ = 3 ^ d * greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) * E * (d : ℝ) ^ R := by ring


/-- **The Gaussian upper bound on the simple random walk kernel**:
`P^R(0, x) ≤ 3^d C_d R^{-d/2} exp(-|x|_1^2 / (8(R + 2d)))`. -/
theorem srwHeat_gaussian (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (x : Site d) :
    srwHeat d R x ≤ 3 ^ d * greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2)
      * Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * ((R : ℝ) + 2 * d))) :=
  srwHeat_gaussian_of S1_gaussian hd hR x

end LatticeProb

end
