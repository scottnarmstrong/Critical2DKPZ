/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim

/-!
A Gaussian off-diagonal bound for the one-dimensional lazy walk kernel `P1`.

Writing `p_m(k) = 4^{-m} binom(2m, m+k)`, the Pascal recurrence gives the exact
ratio of consecutive weights on the right half of the range,

  `p_m(k+1) / p_m(k) = (m - k) / (m + k + 1)`,

valid for `0 ≤ k ≤ m`.  Since `m + k + 1 ≤ 2(m + 1)` in that range, the ratio is
at most `1 - (2k+1) / (2(m+1))`, hence at most `exp(-(2k+1) / (2(m+1)))`.  The
increments `2k + 1` telescope to a square, `∑_{j<k} (2j+1) = k^2`, so multiplying
the bounds along `0, 1, …, k` yields

  `p_m(k) ≤ p_m(0) exp(-k^2 / (2(m+1)))`.

Outside the range the left-hand side vanishes, and the estimate is symmetric in
`k`, so it holds for every integer `k`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

/-- The Pascal recurrence in the form of an exact relation between consecutive
weights of the one-dimensional lazy walk kernel on the right half of its range. -/
lemma P1_pascal_ratio (m k : ℕ) (h : k ≤ m) :
    P1 m ((k : ℤ) + 1) * ((m : ℝ) + k + 1) = P1 m (k : ℤ) * ((m : ℝ) - k) := by
  have e1 : (m : ℤ) + ((k : ℤ) + 1) = ((m + k + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : (m : ℤ) + (k : ℤ) = ((m + k : ℕ) : ℤ) := by push_cast; ring
  have key := Nat.choose_succ_right_eq (2 * m) (m + k)
  have hsub : 2 * m - (m + k) = m - k := by omega
  rw [hsub] at key
  have keyR : (((2 * m).choose (m + k + 1) : ℕ) : ℝ) * ((m : ℝ) + (k : ℝ) + 1)
      = (((2 * m).choose (m + k) : ℕ) : ℝ) * ((m : ℝ) - (k : ℝ)) := by
    have h1 : (((2 * m).choose (m + k + 1) * (m + k + 1) : ℕ) : ℝ)
        = (((2 * m).choose (m + k) * (m - k) : ℕ) : ℝ) := by exact_mod_cast key
    push_cast [Nat.cast_sub h] at h1
    linear_combination h1
  unfold P1
  rw [e1, e2, binomZ_natCast, binomZ_natCast]
  linear_combination keyR / (4 : ℝ) ^ m

/-- The one-step decay factor of the kernel is dominated by an exponential whose
rate is uniform over the right half of the range. -/
lemma P1_ratio_le_exp (m k : ℕ) (h : k ≤ m) :
    ((m : ℝ) - k) / ((m : ℝ) + k + 1)
      ≤ Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) := by
  have hmk : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  have hden : (0 : ℝ) < (m : ℝ) + k + 1 := by positivity
  have hden2 : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
  have hs0 : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1)) := by positivity
  have hs : ((2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * (2 * ((m : ℝ) + 1))
      = 2 * (k : ℝ) + 1 := div_mul_cancel₀ _ (ne_of_gt hden2)
  have h1 : ((m : ℝ) - k) / ((m : ℝ) + k + 1)
      ≤ 1 + -(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1)) := by
    rw [div_le_iff₀ hden, neg_div]
    nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1 - (k : ℝ)), hs]
  have h2 := Real.add_one_le_exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1)))
  linarith

/-- The Gaussian bound on the initial segment of the range, obtained by
multiplying the one-step decay estimates. -/
lemma P1_gaussian_of_le (m : ℕ) :
    ∀ k : ℕ, k ≤ m + 1 →
      P1 m (k : ℤ) ≤ P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkm : k ≤ m := by omega
    have ih' := ih (by omega)
    have hden : (0 : ℝ) < (m : ℝ) + k + 1 := by positivity
    have hE2 : (m : ℝ) - k
        ≤ Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + k + 1) :=
      (div_le_iff₀ hden).mp (P1_ratio_le_exp m k hkm)
    have hchain : P1 m ((k : ℤ) + 1) * ((m : ℝ) + k + 1)
        ≤ (P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))))
            * (Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + k + 1)) := by
      calc P1 m ((k : ℤ) + 1) * ((m : ℝ) + k + 1)
          = P1 m (k : ℤ) * ((m : ℝ) - k) := P1_pascal_ratio m k hkm
        _ ≤ P1 m (k : ℤ)
              * (Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + k + 1)) :=
            mul_le_mul_of_nonneg_left hE2 (P1_nonneg m _)
        _ ≤ (P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))))
              * (Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + k + 1)) :=
            mul_le_mul_of_nonneg_right ih' (by positivity)
    have hfinal : P1 m ((k : ℤ) + 1)
        ≤ P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))
            * Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) := by
      refine le_of_mul_le_mul_right ?_ hden
      calc P1 m ((k : ℤ) + 1) * ((m : ℝ) + k + 1)
          ≤ (P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))))
              * (Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + k + 1)) :=
            hchain
        _ = P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))
              * Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + k + 1) := by
            ring
    have hexp : Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))
          * Real.exp (-(2 * (k : ℝ) + 1) / (2 * ((m : ℝ) + 1)))
        = Real.exp (-(((k : ℝ) + 1) ^ 2) / (2 * ((m : ℝ) + 1))) := by
      rw [← Real.exp_add]
      congr 1
      have hD : (2 * ((m : ℝ) + 1)) ≠ 0 := by positivity
      field_simp
      ring
    have hc1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    have hc2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc1, hc2, ← hexp, ← mul_assoc]
    exact hfinal

/-- The Gaussian bound at every nonnegative site, the sites beyond the range
being handled by the vanishing of the kernel there. -/
lemma P1_gaussian_natCast (m k : ℕ) :
    P1 m (k : ℤ) ≤ P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := by
  by_cases h : k ≤ m + 1
  · exact P1_gaussian_of_le m k h
  · have hz : P1 m (k : ℤ) = 0 := by
      refine P1_eq_zero ?_
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ))]
      omega
    rw [hz]
    exact mul_nonneg (P1_nonneg m 0) (Real.exp_nonneg _)

/-- The one-dimensional lazy walk kernel satisfies a Gaussian upper bound. -/
theorem P1_gaussian (m : ℕ) (k : ℤ) :
    P1 m k ≤ P1 m 0 * Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := by
  by_cases h : 0 ≤ k
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = (t : ℤ) := ⟨k.toNat, by omega⟩
    have hsq : (((t : ℤ) : ℝ)) ^ 2 = ((t : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [hsq]
    exact P1_gaussian_natCast m t
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = -(t : ℤ) := ⟨(-k).toNat, by omega⟩
    have hsq : ((-(t : ℤ) : ℤ) : ℝ) ^ 2 = ((t : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [P1_symm, hsq]
    exact P1_gaussian_natCast m t

end LatticeProb

end
