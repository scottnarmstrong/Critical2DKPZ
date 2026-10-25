/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.SRWDecomp
import Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
import Critical2DKPZ.RandomWalk.Port.Walk.OneDimGauss

/-! # Gaussian bounds for the one-dimensional simple random walk

At even times and even sites the simple walk kernel equals the lazy walk kernel;
a single nearest-neighbour step extends its Gaussian upper bound to odd times. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

/-- Shifting a real number by a unit costs at most one against half its square:
`(t + s)^2 ≥ t^2/2 - 1` whenever `s^2 = 1`, with equality at `t = -2s`.  This is
what lets the even-time Gaussian bound be transported to the two neighbours of a
site without losing more than a bounded factor. -/
lemma half_sq_sub_one_le_sq_add (t s : ℝ) (hs : s ^ 2 = 1) :
    t ^ 2 / 2 - 1 ≤ (t + s) ^ 2 := by
  nlinarith [sq_nonneg (t + 2 * s)]

/-- The Gaussian factor at a unit-shifted site, in terms of the factor at the
site itself: halving the rate absorbs the shift at the price of `exp(1/D)`. -/
lemma exp_shift_bound (D t s : ℝ) (hD : 0 < D) (hs : s ^ 2 = 1) :
    Real.exp (-((t + s) ^ 2) / D)
      ≤ Real.exp (1 / D) * Real.exp (-(t ^ 2) / (2 * D)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hDne : D ≠ 0 := ne_of_gt hD
  have heq : 1 / D + -(t ^ 2) / (2 * D) = (1 - t ^ 2 / 2) / D := by
    field_simp
    ring
  rw [heq, div_le_div_iff₀ hD hD]
  have hkey : (0 : ℝ) ≤ (1 - t ^ 2 / 2 + (t + s) ^ 2) * D :=
    mul_nonneg (by nlinarith [half_sq_sub_one_le_sq_add t s hs]) (le_of_lt hD)
  nlinarith [hkey]

/-- **The Gaussian bound at even times.**  The kernel vanishes at the odd sites,
and at an even site it is the lazy kernel, where the bound of
`LatticeProb.P1_gaussian` applies with the rate `2(m+1)` in the lazy variable,
that is `8(m+1)` in the simple one. -/
lemma S1_gaussian_even (m : ℕ) (k : ℤ) :
    S1 (2 * m) k ≤ 1 / Real.sqrt ((m : ℝ) + 1)
      * Real.exp (-((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hk : k = 2 * j := by omega
    subst hk
    have hval : S1 (2 * m) (2 * j) = P1 m j := srwHeat_one_two_mul m j
    have hexp : Real.exp (-((((2 * j : ℤ)) : ℝ) ^ 2) / (8 * ((m : ℝ) + 1)))
        = Real.exp (-((j : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := by
      congr 1
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [hval, hexp]
    calc P1 m j ≤ P1 m 0 * Real.exp (-((j : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) :=
          P1_gaussian m j
      _ ≤ 1 / Real.sqrt ((m : ℝ) + 1) * Real.exp (-((j : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right (P1_zero_le_inv_sqrt m) (Real.exp_nonneg _)
  · have hzero : S1 (2 * m) k = 0 := by
      show srwHeat 1 (2 * m) ![k] = 0
      refine srwHeat_eq_zero_of_parity ?_
      rw [graphNorm_one]
      have hpar : ((k.natAbs : ℕ) : ZMod 2) = 1 := by
        rw [natAbs_cast_zmod, hj]
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

/-- **The Gaussian off-diagonal bound for the one-dimensional simple random
walk.**  The even times are `LatticeProb.S1_gaussian_even`, and an odd time is
one step away from an even one. -/
theorem S1_gaussian (n : ℕ) (k : ℤ) :
    S1 n k ≤ 3 / Real.sqrt ((n : ℝ) + 1)
      * Real.exp (-((k : ℝ) ^ 2) / (8 * ((n : ℝ) + 2))) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn : n = 2 * m := by omega
    subst hn
    have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpre : 1 / Real.sqrt ((m : ℝ) + 1) ≤ 3 / Real.sqrt (((2 * m : ℕ) : ℝ) + 1) := by
      have h1 : Real.sqrt (((2 * m : ℕ) : ℝ) + 1) ≤ Real.sqrt (9 * ((m : ℝ) + 1)) := by
        refine Real.sqrt_le_sqrt ?_
        push_cast
        linarith
      have h3 : Real.sqrt 9 = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), h3] at h1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hden : -((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))
        ≤ -((k : ℝ) ^ 2) / (8 * (((2 * m : ℕ) : ℝ) + 2)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith [sq_nonneg ((k : ℝ)), mul_nonneg (sq_nonneg ((k : ℝ))) hmm]
    refine le_trans (S1_gaussian_even m k) ?_
    exact mul_le_mul hpre (Real.exp_le_exp.mpr hden) (Real.exp_nonneg _) (by positivity)
  · have hn : n = 2 * m + 1 := by omega
    subst hn
    have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hDpos : (0 : ℝ) < 8 * ((m : ℝ) + 1) := by positivity
    have hsq : (0 : ℝ) ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by positivity
    rw [S1_succ]
    have hA : S1 (2 * m) (k - 1)
        ≤ 1 / Real.sqrt ((m : ℝ) + 1)
          * Real.exp (-(((k : ℝ) + (-1)) ^ 2) / (8 * ((m : ℝ) + 1))) := by
      have h := S1_gaussian_even m (k - 1)
      have hc : (((k - 1 : ℤ)) : ℝ) = (k : ℝ) + (-1) := by push_cast; ring
      rwa [hc] at h
    have hB : S1 (2 * m) (k + 1)
        ≤ 1 / Real.sqrt ((m : ℝ) + 1)
          * Real.exp (-(((k : ℝ) + 1) ^ 2) / (8 * ((m : ℝ) + 1))) := by
      have h := S1_gaussian_even m (k + 1)
      have hc : (((k + 1 : ℤ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rwa [hc] at h
    have hEA := exp_shift_bound (8 * ((m : ℝ) + 1)) (k : ℝ) (-1) hDpos (by norm_num)
    have hEB := exp_shift_bound (8 * ((m : ℝ) + 1)) (k : ℝ) 1 hDpos (by norm_num)
    have hstep : (S1 (2 * m) (k - 1) + S1 (2 * m) (k + 1)) / 2
        ≤ 1 / Real.sqrt ((m : ℝ) + 1)
          * (Real.exp (1 / (8 * ((m : ℝ) + 1)))
              * Real.exp (-((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1))))) := by
      have h1 := le_trans hA (mul_le_mul_of_nonneg_left hEA hsq)
      have h2 := le_trans hB (mul_le_mul_of_nonneg_left hEB hsq)
      linarith
    refine le_trans hstep ?_
    have hexp2 : Real.exp (1 / (8 * ((m : ℝ) + 1))) ≤ 2 := by
      have hlog := Real.log_two_gt_d9
      have h1 : 1 / (8 * ((m : ℝ) + 1)) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hle : 1 / (8 * ((m : ℝ) + 1)) ≤ Real.log 2 := by
        norm_num at hlog
        linarith
      calc Real.exp (1 / (8 * ((m : ℝ) + 1))) ≤ Real.exp (Real.log 2) :=
            Real.exp_le_exp.mpr hle
        _ = 2 := Real.exp_log (by norm_num)
    have e1 : Real.exp (1 / (8 * ((m : ℝ) + 1)))
          * Real.exp (-((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1))))
        ≤ 2 * Real.exp (-((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1)))) :=
      mul_le_mul_of_nonneg_right hexp2 (Real.exp_nonneg _)
    have hpre : 2 * (1 / Real.sqrt ((m : ℝ) + 1))
        ≤ 3 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ) + 1) := by
      have hcast : (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * ((m : ℝ) + 1) := by push_cast; ring
      have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from
          (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hnn : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
      rw [hcast, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hs2 hnn]
    have hden : -((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1)))
        ≤ -((k : ℝ) ^ 2) / (8 * (((2 * m + 1 : ℕ) : ℝ) + 2)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith [sq_nonneg ((k : ℝ)), mul_nonneg (sq_nonneg ((k : ℝ))) hmm]
    calc 1 / Real.sqrt ((m : ℝ) + 1)
            * (Real.exp (1 / (8 * ((m : ℝ) + 1)))
                * Real.exp (-((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1)))))
        ≤ 1 / Real.sqrt ((m : ℝ) + 1)
            * (2 * Real.exp (-((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1))))) :=
          mul_le_mul_of_nonneg_left e1 hsq
      _ = 2 * (1 / Real.sqrt ((m : ℝ) + 1))
            * Real.exp (-((k : ℝ) ^ 2) / (2 * (8 * ((m : ℝ) + 1)))) := by ring
      _ ≤ 3 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ) + 1)
            * Real.exp (-((k : ℝ) ^ 2) / (8 * (((2 * m + 1 : ℕ) : ℝ) + 2))) :=
          mul_le_mul hpre (Real.exp_le_exp.mpr hden) (Real.exp_nonneg _) (by positivity)

end LatticeProb

end
