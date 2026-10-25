/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Estimates
public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim
import Critical2DKPZ.RandomWalk.Port.Walk.OneDimGauss
public import Critical2DKPZ.RandomWalk.Port.Walk.SRWDecomp
import Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
import Critical2DKPZ.RandomWalk.Port.Walk.S1Gauss
import Critical2DKPZ.Lattice.Basic
import Mathlib

/-!
# Same-parity gradient bound for the planar simple random walk

The rotated coordinates of the planar walk are independent one-dimensional
simple walks.  We first bound their two-step differences, then telescope along
the even sublattice and use the Gaussian kernel estimate for long displacements.
-/

@[expose] public section

namespace Critical2DKPZ.WalkTails

open LatticeProb

private lemma p1_poly_exp_absorb (m k : ℕ) :
    ((2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)) *
        Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))
      ≤ 4 * Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
  set M : ℝ := (m : ℝ) + 1
  have hM : 1 ≤ M := by change 1 ≤ (m : ℝ) + 1; linarith
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have hsM1 : 1 ≤ Real.sqrt M := by
    have := Real.sqrt_le_sqrt hM
    simpa using this
  have hsMsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt (by linarith)
  have hx : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hpoly : (2 * (k : ℝ) + 1) / Real.sqrt M ≤ 2 + (k : ℝ) ^ 2 / M := by
    have hyoung : 2 * (k : ℝ) * Real.sqrt M ≤ (k : ℝ) ^ 2 + M := by
      nlinarith [sq_nonneg ((k : ℝ) - Real.sqrt M), hsMsq]
    have hsqrt_le : Real.sqrt M ≤ M := by
      nlinarith [sq_nonneg (Real.sqrt M - 1), hsMsq, hsM1]
    have hnum : (2 * (k : ℝ) + 1) * Real.sqrt M ≤ 2 * M + (k : ℝ) ^ 2 := by
      nlinarith
    have heq : (2 + (k : ℝ) ^ 2 / M) * Real.sqrt M =
        (2 * M + (k : ℝ) ^ 2) / Real.sqrt M := by
      field_simp [ne_of_gt hsM, ne_of_gt (show 0 < M by linarith)]
      nlinarith [hsMsq]
    rw [div_le_iff₀ hsM, heq]
    exact (le_div_iff₀ hsM).2 hnum
  have hexp := Real.add_one_le_exp ((k : ℝ) ^ 2 / (4 * M))
  have hpoly' : 2 + (k : ℝ) ^ 2 / M ≤ 4 * Real.exp ((k : ℝ) ^ 2 / (4 * M)) := by
    calc
      2 + (k : ℝ) ^ 2 / M ≤ 4 + (k : ℝ) ^ 2 / M := by linarith
      _ = 4 * (1 + (k : ℝ) ^ 2 / (4 * M)) := by
        field_simp [ne_of_gt (show 0 < M by linarith)]
      _ ≤ 4 * Real.exp ((k : ℝ) ^ 2 / (4 * M)) := by nlinarith [hexp]
  calc
    ((2 * (k : ℝ) + 1) / Real.sqrt M) *
        Real.exp (-((k : ℝ) ^ 2) / (2 * M))
      ≤ (2 + (k : ℝ) ^ 2 / M) *
          Real.exp (-((k : ℝ) ^ 2) / (2 * M)) :=
            mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
    _ ≤ (4 * Real.exp ((k : ℝ) ^ 2 / (4 * M))) *
          Real.exp (-((k : ℝ) ^ 2) / (2 * M)) :=
            mul_le_mul_of_nonneg_right hpoly' (Real.exp_nonneg _)
    _ = 4 * (Real.exp ((k : ℝ) ^ 2 / (4 * M)) *
        Real.exp (-((k : ℝ) ^ 2) / (2 * M))) := by ring
    _ = 4 * Real.exp (-((k : ℝ) ^ 2) / (4 * M)) := by
      rw [← Real.exp_add]
      congr 1
      apply congrArg Real.exp
      field_simp [ne_of_gt (show 0 < M by linarith)]
      ring

/-- On the right half of its support, adjacent lazy-walk weights have a
Gaussian difference bound with the derivative scale `1 / (m+1)`. -/
private lemma P1_adjacent_abs_diff_bound_nat (m k : ℕ) :
    |P1 m ((k : ℤ) + 1) - P1 m (k : ℤ)| ≤
      4 / ((m : ℝ) + 1) *
        Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by
  by_cases hkm : k ≤ m
  · have hratio := P1_pascal_ratio m k hkm
    have hden : 0 < (m : ℝ) + (k : ℝ) + 1 := by positivity
    have hM : 0 < (m : ℝ) + 1 := by positivity
    have hdiff : P1 m (k : ℤ) - P1 m ((k : ℤ) + 1) =
        P1 m (k : ℤ) * ((2 * (k : ℝ) + 1) / ((m : ℝ) + (k : ℝ) + 1)) := by
      have hmul : P1 m ((k : ℤ) + 1) * ((m : ℝ) + (k : ℝ) + 1) =
          P1 m (k : ℤ) * ((m : ℝ) - (k : ℝ)) := hratio
      field_simp [ne_of_gt hden]
      nlinarith [hmul]
    have hanti : P1 m ((k : ℤ) + 1) ≤ P1 m (k : ℤ) := by
      exact P1_antitone m (by positivity)
    have habs : |P1 m ((k : ℤ) + 1) - P1 m (k : ℤ)| =
        P1 m (k : ℤ) - P1 m ((k : ℤ) + 1) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hanti)]
      ring
    rw [habs, hdiff]
    have hratio_nn : 0 ≤ (2 * (k : ℝ) + 1) /
        ((m : ℝ) + (k : ℝ) + 1) := by positivity
    have hratio_le : (2 * (k : ℝ) + 1) /
          ((m : ℝ) + (k : ℝ) + 1) ≤ (2 * (k : ℝ) + 1) / ((m : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by positivity) hM
      nlinarith
    have hP : P1 m (k : ℤ) ≤
        1 / Real.sqrt ((m : ℝ) + 1) *
          Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := by
      calc
        P1 m (k : ℤ) ≤ P1 m 0 *
            Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1))) := P1_gaussian m _
        _ ≤ _ := mul_le_mul_of_nonneg_right (P1_zero_le_inv_sqrt m)
          (Real.exp_nonneg _)
    have hfinal : (1 / Real.sqrt ((m : ℝ) + 1) *
          Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))) *
          ((2 * (k : ℝ) + 1) / ((m : ℝ) + 1)) =
        (1 / ((m : ℝ) + 1)) *
          (((2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)) *
            Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))) := by
      field_simp [ne_of_gt hM, ne_of_gt (Real.sqrt_pos.mpr hM)]
    calc
      P1 m (k : ℤ) *
          ((2 * (k : ℝ) + 1) / ((m : ℝ) + (k : ℝ) + 1))
        ≤ P1 m (k : ℤ) * ((2 * (k : ℝ) + 1) / ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hratio_le (P1_nonneg _ _)
      _ ≤ (1 / Real.sqrt ((m : ℝ) + 1) *
          Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))) *
          ((2 * (k : ℝ) + 1) / ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ = (1 / ((m : ℝ) + 1)) *
        (((2 * (k : ℝ) + 1) / Real.sqrt ((m : ℝ) + 1)) *
            Real.exp (-((k : ℝ) ^ 2) / (2 * ((m : ℝ) + 1)))) := hfinal
      _ ≤ 1 / ((m : ℝ) + 1) *
          (4 * Real.exp (-((k : ℝ) ^ 2) /
            (4 * ((m : ℝ) + 1)))) := by
          exact mul_le_mul_of_nonneg_left (p1_poly_exp_absorb m k) (by positivity)
      _ = 4 / ((m : ℝ) + 1) *
          Real.exp (-((k : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := by ring
  · have hzero : P1 m (k : ℤ) = 0 := by
      refine P1_eq_zero ?_
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ))]
      exact_mod_cast (show m < k by omega)
    have hzero' : P1 m ((k : ℤ) + 1) = 0 := by
      refine P1_eq_zero ?_
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ) + 1)]
      exact_mod_cast (show m < k + 1 by omega)
    rw [hzero, hzero']
    simp
    positivity

/-- Adjacent values of the lazy one-dimensional walk have a Gaussian gradient
bound on both sides of the symmetry centre. -/
lemma P1_adjacent_abs_diff_bound (m : ℕ) (k : ℤ) :
    |P1 m (k + 1) - P1 m k| ≤
      8 / ((m : ℝ) + 1) *
        Real.exp (-((k : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) := ⟨k.toNat, by omega⟩
    have hnat := P1_adjacent_abs_diff_bound_nat m j
    have hexp : Real.exp (-((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) ≤
        Real.exp (-((j : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (j : ℝ)]
    have hcoeff : 4 / ((m : ℝ) + 1) ≤ 8 / ((m : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact hnat.trans (mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by positivity))
  · let j : ℕ := (-k - 1).toNat
    have hk' : k = -((j : ℤ) + 1) := by
      dsimp [j]
      omega
    rw [hk']
    have hsymm₁ : P1 m ((-((j : ℤ) + 1)) + 1) = P1 m (j : ℤ) := by
      rw [show -((j : ℤ) + 1) + 1 = -(j : ℤ) by ring, P1_symm]
    have hsymm₂ : P1 m (-((j : ℤ) + 1)) = P1 m ((j : ℤ) + 1) := by
      rw [P1_symm]
    have hnat := P1_adjacent_abs_diff_bound_nat m j
    have hM : 1 ≤ (m : ℝ) + 1 := by
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    have hsquare : (j : ℝ) ^ 2 ≥ ((-((j : ℤ) + 1) : ℤ) : ℝ) ^ 2 / 2 - 1 := by
      push_cast
      nlinarith [sq_nonneg ((j : ℝ) - 1)]
    have hextra : 1 / (4 * ((m : ℝ) + 1)) ≤ Real.log 2 := by
      have hlog := Real.log_two_gt_d9
      have hquarter : (1 / 4 : ℝ) < Real.log 2 := by norm_num at hlog ⊢; linarith
      have hfrac : 1 / (4 * ((m : ℝ) + 1)) ≤ (1 / 4 : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      exact hfrac.trans hquarter.le
    have hMpos : 0 < (m : ℝ) + 1 := by positivity
    have hprod : 2 ≤ 8 * ((m : ℝ) + 1) * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left hextra
        (by positivity : 0 ≤ 8 * ((m : ℝ) + 1))
      have heq : (8 * ((m : ℝ) + 1)) *
          (1 / (4 * ((m : ℝ) + 1))) = 2 := by
        field_simp [ne_of_gt hMpos]
        norm_num
      nlinarith [hmul, heq]
    have hexp : Real.exp (-((j : ℝ) ^ 2) /
        (4 * ((m : ℝ) + 1))) ≤ 2 * Real.exp (-(((-((j : ℤ) + 1) : ℤ) : ℝ) ^ 2) /
          (8 * ((m : ℝ) + 1))) := by
      calc
        _ ≤ Real.exp (-(((-((j : ℤ) + 1) : ℤ) : ℝ) ^ 2) /
              (8 * ((m : ℝ) + 1)) + Real.log 2) := by
                apply Real.exp_le_exp.mpr
                apply (div_le_iff₀ (by positivity)).2
                field_simp [ne_of_gt hMpos]
                nlinarith [hsquare, hprod]
        _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring
    calc
      |P1 m ((-((j : ℤ) + 1)) + 1) - P1 m (-((j : ℤ) + 1))|
        = |P1 m ((j : ℤ) + 1) - P1 m (j : ℤ)| := by rw [hsymm₁, hsymm₂, abs_sub_comm]
      _ ≤ 4 / ((m : ℝ) + 1) *
          Real.exp (-((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1))) := hnat
      _ ≤ 8 / ((m : ℝ) + 1) *
          Real.exp (-(((-((j : ℤ) + 1) : ℤ) : ℝ) ^ 2) /
            (8 * ((m : ℝ) + 1))) := by
          calc
            4 / ((m : ℝ) + 1) *
                Real.exp (-((j : ℝ) ^ 2) / (4 * ((m : ℝ) + 1)))
              ≤ 4 / ((m : ℝ) + 1) *
                  (2 * Real.exp (-(((-((j : ℤ) + 1) : ℤ) : ℝ) ^ 2) /
                    (8 * ((m : ℝ) + 1)))) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = 8 / ((m : ℝ) + 1) *
                  Real.exp (-(((-((j : ℤ) + 1) : ℤ) : ℝ) ^ 2) /
                    (8 * ((m : ℝ) + 1))) := by ring

private lemma p1_exp_shift (m : ℕ) (j a : ℤ) (ha : a = j ∨ a = j + 1) :
    Real.exp (-((a : ℝ) ^ 2) / (8 * ((m : ℝ) + 1))) ≤
      2 * Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
        (512 * ((m : ℝ) + 1))) := by
  have hquad : ((2 * j + 1 : ℤ) : ℝ) ^ 2 ≤ 8 * (a : ℝ) ^ 2 + 2 := by
    rcases ha with h | h
    · subst a
      push_cast
      nlinarith [sq_nonneg (2 * (j : ℝ) - 1)]
    · subst a
      push_cast
      nlinarith [sq_nonneg (2 * (j : ℝ) + 3)]
  have hlog : (1 / 32 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hM : 1 ≤ (m : ℝ) + 1 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  have hMpos : 0 < (m : ℝ) + 1 := by linarith
  have hlog' : 1 / (32 * ((m : ℝ) + 1)) ≤ Real.log 2 := by
    have hfrac : 1 / (32 * ((m : ℝ) + 1)) ≤ (1 / 32 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact hfrac.trans hlog.le
  have hprod : 2 ≤ 512 * ((m : ℝ) + 1) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlog'
      (by positivity : 0 ≤ 512 * ((m : ℝ) + 1))
    have heq : (512 * ((m : ℝ) + 1)) *
        (1 / (32 * ((m : ℝ) + 1))) = 16 := by
      field_simp [ne_of_gt hMpos]
      norm_num
    nlinarith [hmul, heq]
  have harg : -((a : ℝ) ^ 2) / (8 * ((m : ℝ) + 1)) ≤
      -((2 * j + 1 : ℤ) : ℝ) ^ 2 /
        (512 * ((m : ℝ) + 1)) + Real.log 2 := by
    apply (div_le_iff₀ (by positivity)).2
    field_simp [ne_of_gt hMpos]
    nlinarith [hquad, hprod]
  calc
    _ ≤ Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
        (512 * ((m : ℝ) + 1)) + Real.log 2) := Real.exp_le_exp.mpr harg
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring

/-- The simple one-dimensional walk has a Gaussian bound on its differences
between sites two units apart, on the parity class accessible at time `n`. -/
lemma S1_two_step_abs_diff_bound (n : ℕ) (k : ℤ)
    (hk : Even (k + (n : ℤ))) :
    |S1 n (k + 2) - S1 n k| ≤
      32 / ((n : ℝ) + 1) *
        Real.exp (-((k : ℝ) ^ 2) / (256 * ((n : ℝ) + 1))) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn : n = 2 * m := by omega
    subst n
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hk' : k = 2 * j := by omega
      subst k
      have htime : m + m = 2 * m := by omega
      have hEven : S1 (m + m) (j + j) = P1 m j := by
        rw [htime]
        have heq : (j + j : ℤ) = 2 * j := by ring
        rw [heq]
        exact srwHeat_one_two_mul m j
      have hNext : S1 (m + m) (j + j + 2) = P1 m (j + 1) := by
        rw [htime]
        have heq : (j + j + 2 : ℤ) = 2 * (j + 1) := by ring
        rw [heq]
        exact srwHeat_one_two_mul m (j + 1)
      rw [hNext, hEven]
      have hP := P1_adjacent_abs_diff_bound m j
      have hM : 0 < (m : ℝ) + 1 := by positivity
      have hcoef : 8 / ((m : ℝ) + 1) ≤ 32 / (((m + m : ℕ) : ℝ) + 1) := by
        rw [div_le_div_iff₀ hM (by positivity)]
        push_cast
        nlinarith
      have hexp : Real.exp (-((j : ℝ) ^ 2) /
          (8 * ((m : ℝ) + 1))) ≤
          Real.exp (-((2 * j : ℤ) : ℝ) ^ 2 /
            (256 * (((m + m : ℕ) : ℝ) + 1))) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith [sq_nonneg (j : ℝ)]
      have hmul := mul_le_mul hcoef hexp (Real.exp_nonneg _) (by positivity)
      have hidx : (j + j : ℤ) = 2 * j := by ring
      simpa only [hidx] using hP.trans hmul
    · have hk' : k = 2 * j + 1 := by omega
      obtain ⟨q, hq⟩ := hk
      omega
  · have hn : n = 2 * m + 1 := by omega
    subst n
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hk' : k = 2 * j := by omega
      obtain ⟨q, hq⟩ := hk
      omega
    · have hk' : k = 2 * j + 1 := by omega
      subst k
      have hformula : ∀ l : ℤ, S1 (2 * m + 1) (2 * l + 1) =
          (P1 m l + P1 m (l + 1)) / 2 := by
        intro l
        rw [S1_succ]
        have h0 : S1 (2 * m) ((2 * l + 1) - 1) = P1 m l := by
          have heq : (2 * l + 1 - 1 : ℤ) = 2 * l := by ring
          rw [heq]
          exact srwHeat_one_two_mul m l
        have h1 : S1 (2 * m) ((2 * l + 1) + 1) = P1 m (l + 1) := by
          have heq : (2 * l + 1 + 1 : ℤ) = 2 * (l + 1) := by ring
          rw [heq]
          exact srwHeat_one_two_mul m (l + 1)
        rw [h0, h1]
      have hleft := hformula j
      have hright : S1 (2 * m + 1) (2 * j + 1 + 2) =
          (P1 m (j + 1) + P1 m (j + 2)) / 2 := by
        have h := hformula (j + 1)
        convert h using 1 <;> ring_nf
      rw [hleft, hright]
      have htri : |(P1 m (j + 1) + P1 m (j + 2)) / 2 -
          (P1 m j + P1 m (j + 1)) / 2| ≤
          (|P1 m (j + 2) - P1 m (j + 1)| +
            |P1 m (j + 1) - P1 m j|) / 2 := by
        have heq : (P1 m (j + 1) + P1 m (j + 2)) / 2 -
            (P1 m j + P1 m (j + 1)) / 2 =
            ((P1 m (j + 2) - P1 m (j + 1)) +
              (P1 m (j + 1) - P1 m j)) / 2 := by ring
        rw [heq]
        calc
          |((P1 m (j + 2) - P1 m (j + 1)) +
              (P1 m (j + 1) - P1 m j)) / 2|
            = |(P1 m (j + 2) - P1 m (j + 1)) +
                (P1 m (j + 1) - P1 m j)| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          _ ≤ (|P1 m (j + 2) - P1 m (j + 1)| +
                |P1 m (j + 1) - P1 m j|) / 2 := by
                  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num))
      have hM : 0 < (m : ℝ) + 1 := by positivity
      have hshift₀ := p1_exp_shift m j j (Or.inl rfl)
      have hshift₁ := p1_exp_shift m j (j + 1) (Or.inr rfl)
      have hP₀ := P1_adjacent_abs_diff_bound m j
      have hP₁ := P1_adjacent_abs_diff_bound m (j + 1)
      have hP₁' : |P1 m (j + 2) - P1 m (j + 1)| ≤
          8 / ((m : ℝ) + 1) *
            Real.exp (-(((j + 1 : ℤ) : ℝ) ^ 2) /
              (8 * ((m : ℝ) + 1))) := by
        have hidx : (j + 1 : ℤ) + 1 = j + 2 := by omega
        simpa only [hidx] using hP₁
      have hboth : (|P1 m (j + 2) - P1 m (j + 1)| +
          |P1 m (j + 1) - P1 m j|) / 2 ≤
          16 / ((m : ℝ) + 1) *
            Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
              (512 * ((m : ℝ) + 1))) := by
        have h0 : |P1 m (j + 1) - P1 m j| ≤
            16 / ((m : ℝ) + 1) *
              Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                (512 * ((m : ℝ) + 1))) := by
          calc
            _ ≤ 8 / ((m : ℝ) + 1) *
                Real.exp (-((j : ℝ) ^ 2) /
                  (8 * ((m : ℝ) + 1))) := hP₀
            _ ≤ 16 / ((m : ℝ) + 1) *
                Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                  (512 * ((m : ℝ) + 1))) := by
                  calc
                    8 / ((m : ℝ) + 1) *
                        Real.exp (-((j : ℝ) ^ 2) /
                          (8 * ((m : ℝ) + 1)))
                      ≤ 8 / ((m : ℝ) + 1) *
                          (2 * Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                            (512 * ((m : ℝ) + 1)))) :=
                        mul_le_mul_of_nonneg_left hshift₀ (by positivity)
                    _ = 16 / ((m : ℝ) + 1) *
                          Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                            (512 * ((m : ℝ) + 1))) := by ring
        have h1 : |P1 m (j + 2) - P1 m (j + 1)| ≤
            16 / ((m : ℝ) + 1) *
              Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                (512 * ((m : ℝ) + 1))) := by
          calc
            _ ≤ 8 / ((m : ℝ) + 1) *
                Real.exp (-(((j + 1 : ℤ) : ℝ) ^ 2) /
                  (8 * ((m : ℝ) + 1))) := hP₁'
            _ ≤ 16 / ((m : ℝ) + 1) *
                Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                  (512 * ((m : ℝ) + 1))) := by
                  calc
                    8 / ((m : ℝ) + 1) *
                        Real.exp (-(((j + 1 : ℤ) : ℝ) ^ 2) /
                          (8 * ((m : ℝ) + 1)))
                      ≤ 8 / ((m : ℝ) + 1) *
                          (2 * Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                            (512 * ((m : ℝ) + 1)))) :=
                        mul_le_mul_of_nonneg_left hshift₁ (by positivity)
                    _ = 16 / ((m : ℝ) + 1) *
                          Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                            (512 * ((m : ℝ) + 1))) := by ring
        rw [add_div]
        calc
          |P1 m (j + 2) - P1 m (j + 1)| / 2 +
              |P1 m (j + 1) - P1 m j| / 2
            ≤ (16 / ((m : ℝ) + 1) *
                Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                  (512 * ((m : ℝ) + 1)))) / 2 +
              (16 / ((m : ℝ) + 1) *
                Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                  (512 * ((m : ℝ) + 1)))) / 2 := by
                exact add_le_add
                  (div_le_div_of_nonneg_right h1 (by norm_num))
                  (div_le_div_of_nonneg_right h0 (by norm_num))
          _ = 16 / ((m : ℝ) + 1) *
                Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
                  (512 * ((m : ℝ) + 1))) := by ring
      have htime : (((2 * m + 1 : ℕ) : ℝ) + 1) =
          2 * ((m : ℝ) + 1) := by push_cast; ring
      have hfinal : 16 / ((m : ℝ) + 1) *
          Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
            (512 * ((m : ℝ) + 1))) =
        32 / ((((2 * m + 1 : ℕ) : ℝ) + 1)) *
          Real.exp (-(((2 * j + 1 : ℤ) : ℝ) ^ 2) /
            (256 * (((2 * m + 1 : ℕ) : ℝ) + 1))) := by
        rw [htime]
        field_simp [ne_of_gt hM]
        ring
      calc
        |(P1 m (j + 1) + P1 m (j + 2)) / 2 -
          (P1 m j + P1 m (j + 1)) / 2| ≤ _ := htri
        _ ≤ 16 / ((m : ℝ) + 1) *
            Real.exp (-((2 * j + 1 : ℤ) : ℝ) ^ 2 /
              (512 * ((m : ℝ) + 1))) := hboth
        _ = 32 / ((((2 * m + 1 : ℕ) : ℝ) + 1)) *
            Real.exp (-(((2 * j + 1 : ℤ) : ℝ) ^ 2) /
              (256 * (((2 * m + 1 : ℕ) : ℝ) + 1))) := hfinal

end Critical2DKPZ.WalkTails

namespace Critical2DKPZ.WalkTails

open LatticeProb

private lemma S1_eq_zero_of_not_even_add (n : ℕ) (k : ℤ)
    (h : ¬ Even (k + (n : ℤ))) : S1 n k = 0 := by
  change srwHeat 1 n (![k] : LatticeProb.Site 1) = 0
  apply srwHeat_eq_zero_of_parity
  rw [graphNorm_one, natAbs_cast_zmod]
  intro heq
  rcases Int.even_or_odd (k + (n : ℤ)) with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact (h ⟨q, hq⟩).elim
  · have hcast : (k : ZMod 2) + (n : ZMod 2) = 1 := by
      have hc := congrArg (fun x : ℤ => (x : ZMod 2)) hq
      push_cast at hc
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add] at hc
      exact hc
    have hzero : (k : ZMod 2) + (n : ZMod 2) = 0 := by
      rw [heq]
      exact CharTwo.add_self_eq_zero _
    rw [hzero] at hcast
    norm_num at hcast

/-- The one-dimensional two-step gradient estimate also holds off the
accessible parity class, where both kernel values vanish. -/
private lemma S1_two_step_abs_diff_bound_all (n : ℕ) (k : ℤ) :
    |S1 n (k + 2) - S1 n k| ≤
      32 / ((n : ℝ) + 1) *
        Real.exp (-((k : ℝ) ^ 2) / (256 * ((n : ℝ) + 1))) := by
  by_cases hk : Even (k + (n : ℤ))
  · exact S1_two_step_abs_diff_bound n k hk
  · have hk2 : ¬ Even (k + 2 + (n : ℤ)) := by
      rintro ⟨q, hq⟩
      apply hk
      refine ⟨q - 1, ?_⟩
      omega
    rw [S1_eq_zero_of_not_even_add n k hk,
      S1_eq_zero_of_not_even_add n (k + 2) hk2]
    norm_num
    positivity

end Critical2DKPZ.WalkTails

namespace Critical2DKPZ.WalkTails

open LatticeProb

private def rotU (z : Site) : ℤ := z 0 + z 1

private def rotV (z : Site) : ℤ := z 0 - z 1

/-- The planar simple walk factors into independent simple walks in the two
rotated coordinates `u = x+y` and `v = x-y`. -/
private theorem srwHeat_two_rotated_product (n : ℕ) (z : Site) :
    LatticeProb.srwHeat 2 n z =
      LatticeProb.S1 n (rotU z) * LatticeProb.S1 n (rotV z) := by
  induction n generalizing z with
  | zero =>
      rw [LatticeProb.srwHeat_zero, LatticeProb.S1_zero, LatticeProb.S1_zero]
      by_cases hz : z = 0
      · subst z
        simp [rotU, rotV]
      · have hUV : rotU z ≠ 0 ∨ rotV z ≠ 0 := by
          by_cases hU : rotU z = 0
          · by_cases hV : rotV z = 0
            · change z 0 + z 1 = 0 at hU
              change z 0 - z 1 = 0 at hV
              have hz0 : z = 0 := by
                ext i
                fin_cases i <;> simp_all <;> omega
              exact (hz hz0).elim
            · exact Or.inr hV
          · exact Or.inl hU
        rcases hUV with hU | hV
        · simp [hU, hz]
        · simp [hV, hz]
  | succ n ih =>
      rw [LatticeProb.srwHeat_succ_eq_sum_dir]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
      simp_rw [ih]
      simp [rotU, rotV, LatticeProb.dirVec]
      rw [LatticeProb.S1_succ, LatticeProb.S1_succ]
      ring

private theorem srwKernel_rotated_product (n : ℕ) (z : Site) :
    srwKernel n z = S1 n (rotU z) * S1 n (rotV z) := by
  rw [srwKernel_eq_srwHeat, srwHeat_two_rotated_product]

end Critical2DKPZ.WalkTails

namespace Critical2DKPZ.WalkTails

open LatticeProb

private lemma rotated_u_edge_gaussian (n : ℕ) (u v : ℤ) :
    |S1 n (u + 2) * S1 n v - S1 n u * S1 n v| ≤
      96 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) *
        Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
          (512 * ((n : ℝ) + 1))) := by
  have hgrad := S1_two_step_abs_diff_bound_all n u
  have hgauss := S1_gaussian n v
  have hnonneg : 0 ≤ S1 n v := S1_nonneg n v
  have hfactor : |S1 n (u + 2) * S1 n v - S1 n u * S1 n v| =
      |S1 n (u + 2) - S1 n u| * S1 n v := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hnonneg]
  rw [hfactor]
  let N : ℝ := (n : ℝ) + 1
  have hN : 1 ≤ N := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    dsimp [N]
    linarith
  have hNpos : 0 < N := by linarith
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsqU : 0 ≤ (u : ℝ) ^ 2 := sq_nonneg _
  have hsqV : 0 ≤ (v : ℝ) ^ 2 := sq_nonneg _
  have hden : 8 * ((n : ℝ) + 2) ≤ 512 * N := by
    dsimp [N]
    nlinarith
  have hrateU : -((u : ℝ) ^ 2) / (256 * N) ≤
      -((u : ℝ) ^ 2) / (512 * N) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hrateV : -((v : ℝ) ^ 2) / (8 * ((n : ℝ) + 2)) ≤
      -((v : ℝ) ^ 2) / (512 * N) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hrate : (-((u : ℝ) ^ 2) / (256 * N)) +
        (-((v : ℝ) ^ 2) / (8 * ((n : ℝ) + 2))) ≤
      -((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (512 * N) := by
    calc
      _ ≤ -((u : ℝ) ^ 2) / (512 * N) +
          (-((v : ℝ) ^ 2) / (512 * N)) := add_le_add hrateU hrateV
      _ = -((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (512 * N) := by ring
  have hexp : Real.exp (-((u : ℝ) ^ 2) / (256 * N)) *
        Real.exp (-(v : ℝ) ^ 2 / (8 * ((n : ℝ) + 2))) ≤
      Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (512 * N)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hrate
  have hmul := mul_le_mul hgrad hgauss hnonneg (by positivity)
  have hcoef : (32 / N) * (3 / Real.sqrt N) =
      96 / (N * Real.sqrt N) := by
    field_simp [ne_of_gt hNpos, ne_of_gt hsqrt]
    ring
  calc
    |S1 n (u + 2) - S1 n u| * S1 n v
      ≤ (32 / N * Real.exp (-((u : ℝ) ^ 2) / (256 * N))) *
          (3 / Real.sqrt N * Real.exp (-(v : ℝ) ^ 2 /
            (8 * ((n : ℝ) + 2)))) := by
              simpa [N] using hmul
    _ = (32 / N) * (3 / Real.sqrt N) *
          (Real.exp (-((u : ℝ) ^ 2) / (256 * N)) *
            Real.exp (-(v : ℝ) ^ 2 / (8 * ((n : ℝ) + 2)))) := by ring
    _ = 96 / (N * Real.sqrt N) *
          (Real.exp (-((u : ℝ) ^ 2) / (256 * N)) *
            Real.exp (-(v : ℝ) ^ 2 / (8 * ((n : ℝ) + 2)))) := by rw [hcoef]
    _ ≤ 96 / (N * Real.sqrt N) *
          Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (512 * N)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by dsimp [N]


private lemma abs_step_telescope (f : ℤ → ℝ) (k : ℤ) (m : ℕ) :
    |f (k + 2 * (m : ℤ)) - f k| ≤
      ∑ i ∈ Finset.range m, |f (k + 2 * (i : ℤ) + 2) - f (k + 2 * (i : ℤ))| := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hidx : k + 2 * ((m + 1 : ℕ) : ℤ) = k + 2 * (m : ℤ) + 2 := by
        push_cast
        ring
      rw [hidx]
      calc
        |f (k + 2 * (m : ℤ) + 2) - f k|
          = |(f (k + 2 * (m : ℤ) + 2) - f (k + 2 * (m : ℤ))) +
              (f (k + 2 * (m : ℤ)) - f k)| := by ring_nf
        _ ≤ |f (k + 2 * (m : ℤ) + 2) - f (k + 2 * (m : ℤ))| +
              |f (k + 2 * (m : ℤ)) - f k| := abs_add_le _ _
        _ ≤ |f (k + 2 * (m : ℤ) + 2) - f (k + 2 * (m : ℤ))| +
              ∑ i ∈ Finset.range m,
                |f (k + 2 * (i : ℤ) + 2) - f (k + 2 * (i : ℤ))| :=
          by
            have := add_le_add_left ih
              |f (k + 2 * (m : ℤ) + 2) - f (k + 2 * (m : ℤ))|
            simpa [add_comm] using this
        _ = _ := by ring

private lemma integer_segment_data {a b : ℤ} (h : Even (b - a)) :
    ∃ m : ℕ, (b = a + 2 * (m : ℤ) ∨ a = b + 2 * (m : ℤ)) := by
  obtain ⟨q, hq⟩ := h
  by_cases hab : a ≤ b
  · refine ⟨q.toNat, Or.inl ?_⟩
    have hq0 : 0 ≤ q := by omega
    rw [Int.toNat_of_nonneg hq0]
    omega
  · refine ⟨(-q).toNat, Or.inr ?_⟩
    have hqneg : q < 0 := by omega
    rw [Int.toNat_of_nonneg (by omega)]
    omega

private lemma rot_same_parity_differences (z z' : Site)
    (h : Even (z 0 + z 1 + z' 0 + z' 1)) :
    Even (rotU z' - rotU z) ∧ Even (rotV z' - rotV z) := by
  obtain ⟨q, hq⟩ := h
  constructor
  · refine ⟨q - rotU z, ?_⟩
    dsimp [rotU]
    omega
  · have hvs : Even (rotV z + rotV z') := by
      refine ⟨q - z 1 - z' 1, ?_⟩
      dsimp [rotV]
      omega
    obtain ⟨r, hr⟩ := hvs
    refine ⟨r - rotV z, ?_⟩
    dsimp [rotV] at hr ⊢
    omega

private lemma rotated_gaussian_shift (n : ℕ) (u v a b : ℤ)
    (hshift : ((u : ℝ) - a) ^ 2 + ((v : ℝ) - b) ^ 2 ≤ 2 * n) :
    Real.exp (-((a : ℝ) ^ 2 + (b : ℝ) ^ 2) /
        (512 * ((n : ℝ) + 1))) ≤
      2 * Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
        (1024 * ((n : ℝ) + 1))) := by
  let N : ℝ := (n : ℝ) + 1
  have hN : 1 ≤ N := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    dsimp [N]
    linarith
  have hNpos : 0 < N := by linarith
  have hlog : (1 / 256 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog' : 1 / 256 ≤ Real.log 2 := hlog.le
  have hprod : 2 * (n : ℝ) / (512 * N) ≤ Real.log 2 := by
    calc
      2 * (n : ℝ) / (512 * N) ≤ (1 / 256 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        dsimp [N]
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        norm_num
        linarith
      _ ≤ Real.log 2 := hlog'
  have hquad : (u : ℝ) ^ 2 + (v : ℝ) ^ 2 ≤
      2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) +
        2 * (((u : ℝ) - a) ^ 2 + ((v : ℝ) - b) ^ 2) := by
    nlinarith [sq_nonneg ((u : ℝ) - 2 * a),
      sq_nonneg ((v : ℝ) - 2 * b)]
  have hbase : ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / 2 -
      (((u : ℝ) - a) ^ 2 + ((v : ℝ) - b) ^ 2) ≤
      (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    nlinarith [hquad]
  have harg0 : -((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (512 * N) ≤
      -((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (1024 * N) +
        (((u : ℝ) - a) ^ 2 + ((v : ℝ) - b) ^ 2) / (512 * N) := by
    have hdiv := div_le_div_of_nonneg_right
      (neg_le_neg hbase) (by positivity : 0 ≤ (512 : ℝ) * N)
    convert hdiv using 1
    field_simp [ne_of_gt hNpos]
    ring
  have hshift' := div_le_div_of_nonneg_right hshift
    (by positivity : 0 ≤ (512 : ℝ) * N)
  have harg : -((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (512 * N) ≤
      -((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (1024 * N) + Real.log 2 := by
    calc
      _ ≤ -((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (1024 * N) +
          2 * (n : ℝ) / (512 * N) := by linarith [harg0, hshift']
      _ ≤ _ := by
        have := add_le_add_left hprod (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
          (1024 * N))
        simpa [add_comm] using this
  calc
    _ ≤ Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
        (1024 * N) + Real.log 2) := Real.exp_le_exp.mpr harg
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

private lemma abs_step_segment (f : ℤ → ℝ) (a b : ℤ)
    (h : Even (b - a)) :
    ∃ m : ℕ, ∃ k : ℤ,
      ((a = k ∧ b = k + 2 * (m : ℤ)) ∨
        (b = k ∧ a = k + 2 * (m : ℤ))) ∧
      |f b - f a| ≤
        ∑ i ∈ Finset.range m,
          |f (k + 2 * (i : ℤ) + 2) - f (k + 2 * (i : ℤ))| := by
  rcases integer_segment_data h with ⟨m, hforward | hbackward⟩
  · refine ⟨m, a, Or.inl ⟨rfl, hforward⟩, ?_⟩
    rw [hforward]
    exact abs_step_telescope f a m
  · refine ⟨m, b, Or.inr ⟨rfl, hbackward⟩, ?_⟩
    rw [hbackward]
    simpa only [abs_sub_comm] using abs_step_telescope f b m

private lemma segment_point_sq_le {a b k : ℤ} {m i : ℕ}
    (hi : i < m)
    (horient : (a = k ∧ b = k + 2 * (m : ℤ)) ∨
      (b = k ∧ a = k + 2 * (m : ℤ))) :
    (((k + 2 * (i : ℤ) : ℤ) : ℝ) - (a : ℝ)) ^ 2 ≤
      ((b - a : ℤ) : ℝ) ^ 2 := by
  have hiR : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.le_of_lt hi)
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  rcases horient with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
  · rw [hb]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hiR)
      (add_nonneg hi0 (by positivity : 0 ≤ (m : ℝ)))]
  · rw [ha]
    push_cast
    nlinarith [mul_nonneg hi0
      (sub_nonneg.mpr (show 0 ≤ 2 * (m : ℝ) - (i : ℝ) by linarith))]

private lemma rotated_u_segment_gaussian (n : ℕ) (u u' v v' : ℤ)
    (hparity : Even (u' - u))
    (hshort : ((u' : ℝ) - u) ^ 2 + ((v' : ℝ) - v) ^ 2 ≤ 2 * (n : ℝ)) :
    ∃ m : ℕ,
      (u' = u + 2 * (m : ℤ) ∨ u = u' + 2 * (m : ℤ)) ∧
      |S1 n u' * S1 n v' - S1 n u * S1 n v'| ≤
        (m : ℝ) * (192 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) *
          Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
            (1024 * ((n : ℝ) + 1))) := by
  obtain ⟨m, k, horient, htelescope⟩ :=
    abs_step_segment (fun x => S1 n x * S1 n v') u u' hparity
  have hrel : u' = u + 2 * (m : ℤ) ∨ u = u' + 2 * (m : ℤ) := by
    rcases horient with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · exact Or.inl hb
    · exact Or.inr ha
  refine ⟨m, hrel, ?_⟩
  let K : ℝ := 192 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) *
    Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
      (1024 * ((n : ℝ) + 1)))
  have hterm : ∀ i ∈ Finset.range m,
      |S1 n (k + 2 * (i : ℤ) + 2) * S1 n v' -
          S1 n (k + 2 * (i : ℤ)) * S1 n v'| ≤ K := by
    intro i hi
    have hpoint := segment_point_sq_le (Finset.mem_range.mp hi) horient
    have hshift : ((u : ℝ) - (k + 2 * (i : ℤ) : ℤ)) ^ 2 +
        ((v : ℝ) - v') ^ 2 ≤ 2 * (n : ℝ) := by
      have hend : ((u' : ℝ) - u) ^ 2 + ((v' : ℝ) - v) ^ 2 ≤
          2 * (n : ℝ) := hshort
      push_cast at hpoint hend ⊢
      nlinarith [hpoint]
    have hlocal := rotated_u_edge_gaussian n (k + 2 * (i : ℤ)) v'
    have hshiftExp := rotated_gaussian_shift n u v (k + 2 * (i : ℤ)) v' hshift
    calc
      |S1 n (k + 2 * (i : ℤ) + 2) * S1 n v' -
          S1 n (k + 2 * (i : ℤ)) * S1 n v'|
        ≤ 96 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) *
            Real.exp (-(((k + 2 * (i : ℤ) : ℤ) : ℝ) ^ 2 + (v' : ℝ) ^ 2) /
              (512 * ((n : ℝ) + 1))) := by
                simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hlocal
      _ ≤ 96 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) *
            (2 * Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
              (1024 * ((n : ℝ) + 1)))) := by
                exact mul_le_mul_of_nonneg_left hshiftExp (by positivity)
      _ = K := by dsimp [K]; ring
  have hsum :
      (∑ i ∈ Finset.range m,
        |S1 n (k + 2 * (i : ℤ) + 2) * S1 n v' -
          S1 n (k + 2 * (i : ℤ)) * S1 n v'|) ≤
        ∑ i ∈ Finset.range m, K :=
    Finset.sum_le_sum fun i hi => hterm i hi
  have hsumconst : (∑ i ∈ Finset.range m, K) = (m : ℝ) * K := by simp
  calc
    |S1 n u' * S1 n v' - S1 n u * S1 n v'|
      ≤ ∑ i ∈ Finset.range m,
          |S1 n (k + 2 * (i : ℤ) + 2) * S1 n v' -
            S1 n (k + 2 * (i : ℤ)) * S1 n v'| := by
              simpa only [sub_mul] using htelescope
    _ ≤ ∑ i ∈ Finset.range m, K := hsum
    _ = (m : ℝ) * K := hsumconst
    _ = _ := by dsimp [K]; ring

private lemma rotated_v_segment_gaussian (n : ℕ) (u u' v v' : ℤ)
    (hparity : Even (v' - v))
    (hshort : ((u' : ℝ) - u) ^ 2 + ((v' : ℝ) - v) ^ 2 ≤ 2 * (n : ℝ)) :
    ∃ m : ℕ,
      (v' = v + 2 * (m : ℤ) ∨ v = v' + 2 * (m : ℤ)) ∧
      |S1 n u * S1 n v' - S1 n u * S1 n v| ≤
        (m : ℝ) * (192 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) *
          Real.exp (-((u : ℝ) ^ 2 + (v : ℝ) ^ 2) /
            (1024 * ((n : ℝ) + 1))) := by
  obtain ⟨m, hrel, hm⟩ := rotated_u_segment_gaussian n v v' u u hparity (by
    have h := hshort
    nlinarith [h])
  refine ⟨m, hrel, ?_⟩
  simpa [mul_comm, add_comm, add_left_comm] using hm

private lemma segment_half_sq {a b : ℤ} {m : ℕ}
    (h : b = a + 2 * (m : ℤ) ∨ a = b + 2 * (m : ℤ)) :
    ((b - a : ℤ) : ℝ) ^ 2 / 4 = (m : ℝ) ^ 2 := by
  rcases h with h | h
  · rw [h]
    push_cast
    ring
  · rw [h]
    push_cast
    ring

private lemma segment_length_sq_le (m₁ m₂ : ℕ) :
    ((m₁ + m₂ : ℕ) : ℝ) ^ 2 ≤
      2 * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2) := by
  have h := sq_nonneg ((m₁ : ℝ) - (m₂ : ℝ))
  push_cast at h ⊢
  nlinarith

private lemma rotated_norm_sq (z : Site) :
    (rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2 =
      2 * ‖siteToPlane z‖ ^ 2 := by
  rw [norm_siteToPlane_sq]
  dsimp [rotU, rotV]
  push_cast
  ring

private lemma exp_rotated_le_plane (n : ℕ) (z : Site)
    (hn : 1 ≤ n) :
    Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
      (512 * ((n : ℝ) + 1))) ≤
      Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hR : 0 ≤ ‖siteToPlane z‖ ^ 2 := sq_nonneg _
  have hcoeff : (1 / 512 : ℝ) / n ≤
      (1 / 256 : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ hnR (by positivity)]
    norm_num
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [rotated_norm_sq]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hcoeff hR
  have hleft : -(2 * ‖siteToPlane z‖ ^ 2) /
      (512 * ((n : ℝ) + 1)) =
      -((1 / 256 : ℝ) / ((n : ℝ) + 1)) * ‖siteToPlane z‖ ^ 2 := by
    field_simp [ne_of_gt (show 0 < (n : ℝ) + 1 by positivity)]
    ring
  have hright : -(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n =
      -((1 / 512 : ℝ) / n) * ‖siteToPlane z‖ ^ 2 := by
    field_simp [ne_of_gt hnR]
  rw [hleft, hright]
  simpa only [neg_mul] using neg_le_neg hmul


private lemma rotated_edge_prefactor_sq (n : ℕ) :
    (192 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) ^ 2 =
      36864 / ((n : ℝ) + 1) ^ 3 := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt (by linarith)
  have hden : (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) ^ 2 =
      ((n : ℝ) + 1) ^ 3 := by rw [mul_pow, hsqrt]; ring
  rw [div_pow, hden]
  norm_num

private lemma srwKernel_sameParity_sq_diff_short (n : ℕ) (hn : 1 ≤ n)
    (z z' : Site) (hparity : Even (z 0 + z 1 + z' 0 + z' 1))
    (hshort : ‖siteToPlane (z - z')‖ ^ 2 ≤ n) :
    (srwKernel n z - srwKernel n z') ^ 2 ≤
      36864 * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
        Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
  have hrotParity := rot_same_parity_differences z z' hparity
  obtain ⟨hu, hv⟩ := hrotParity
  let du : ℝ := ((rotU z' - rotU z : ℤ) : ℝ)
  let dv : ℝ := ((rotV z' - rotV z : ℤ) : ℝ)
  let D : ℝ := ‖siteToPlane (z - z')‖ ^ 2
  have hD : du ^ 2 + dv ^ 2 = 2 * D := by
    dsimp [du, dv, D]
    rw [norm_siteToPlane_sq]
    simp only [Pi.sub_apply]
    dsimp [rotU, rotV]
    push_cast
    ring
  have hDnonneg : 0 ≤ D := sq_nonneg _
  have hcoordshort : du ^ 2 + dv ^ 2 ≤ 2 * (n : ℝ) := by
    rw [hD]
    change D ≤ (n : ℝ) at hshort
    nlinarith
  have heqU : ((rotU z' : ℝ) - rotU z) = du := by
    dsimp [du]
    push_cast
    ring
  have heqV : ((rotV z' : ℝ) - rotV z) = dv := by
    dsimp [dv]
    push_cast
    ring
  have hUshort : ((rotU z' : ℝ) - rotU z) ^ 2 +
      ((rotV z' : ℝ) - rotV z) ^ 2 ≤ 2 * (n : ℝ) := by
    rw [heqU, heqV]
    exact hcoordshort
  have hVshort : ((rotU z' : ℝ) - rotU z) ^ 2 +
      ((rotV z' : ℝ) - rotV z) ^ 2 ≤ 2 * (n : ℝ) := hUshort
  obtain ⟨mu, hUrel, hUbound⟩ :=
    rotated_u_segment_gaussian n (rotU z) (rotU z') (rotV z) (rotV z') hu hUshort
  obtain ⟨mv, hVrel, hVbound⟩ :=
    rotated_v_segment_gaussian n (rotU z) (rotU z') (rotV z) (rotV z') hv hVshort
  have hmu : (mu : ℝ) ^ 2 = du ^ 2 / 4 := by
    simpa [du] using (segment_half_sq hUrel).symm
  have hmv : (mv : ℝ) ^ 2 = dv ^ 2 / 4 := by
    simpa [dv] using (segment_half_sq hVrel).symm
  have hL : ((mu + mv : ℕ) : ℝ) ^ 2 ≤ D := by
    calc
      ((mu + mv : ℕ) : ℝ) ^ 2 ≤
          2 * ((mu : ℝ) ^ 2 + (mv : ℝ) ^ 2) := segment_length_sq_le mu mv
      _ = du ^ 2 / 2 + dv ^ 2 / 2 := by rw [hmu, hmv]; ring
      _ = D := by nlinarith [hD]
  have hkernelz := srwKernel_rotated_product n z
  have hkernelz' := srwKernel_rotated_product n z'
  have habs : |srwKernel n z - srwKernel n z'| ≤
      ((mu + mv : ℕ) : ℝ) *
        (192 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) *
          Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
            (1024 * ((n : ℝ) + 1))) := by
    rw [abs_sub_comm, hkernelz', hkernelz]
    have hsplit :
        S1 n (rotU z') * S1 n (rotV z') - S1 n (rotU z) * S1 n (rotV z) =
          (S1 n (rotU z') * S1 n (rotV z') -
              S1 n (rotU z) * S1 n (rotV z')) +
            (S1 n (rotU z) * S1 n (rotV z') -
              S1 n (rotU z) * S1 n (rotV z)) := by ring
    rw [hsplit]
    calc
      _ ≤ |S1 n (rotU z') * S1 n (rotV z') -
              S1 n (rotU z) * S1 n (rotV z')| +
            |S1 n (rotU z) * S1 n (rotV z') -
              S1 n (rotU z) * S1 n (rotV z)| := abs_add_le _ _
      _ ≤ _ := add_le_add hUbound hVbound
      _ = _ := by push_cast; ring
  let N : ℝ := (n : ℝ) + 1
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hExpSq :
      Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) / (1024 * N)) ^ 2 =
        Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) / (512 * N)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp [ne_of_gt hNpos]
    ring
  have hLden : ((mu + mv : ℕ) : ℝ) ^ 2 / N ^ 3 ≤ D / (n : ℝ) ^ 3 := by
    have hN : (n : ℝ) ^ 3 ≤ N ^ 3 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hfac : 0 ≤ (N - n) * (N ^ 2 + N * n + n ^ 2) :=
        mul_nonneg (by dsimp [N]; norm_num) (by positivity)
      dsimp [N] at hfac ⊢
      nlinarith
    calc
      ((mu + mv : ℕ) : ℝ) ^ 2 / N ^ 3 ≤ D / N ^ 3 :=
        div_le_div_of_nonneg_right hL (by positivity)
      _ ≤ D / (n : ℝ) ^ 3 := by
        have hInv : (N ^ 3)⁻¹ ≤ ((n : ℝ) ^ 3)⁻¹ := by
          simpa only [one_div] using
            one_div_le_one_div_of_le (by positivity) hN
        exact mul_le_mul_of_nonneg_left hInv hDnonneg
  have hrate : Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
      (512 * N)) ≤ Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
    simpa only [N] using exp_rotated_le_plane n z hn
  calc
    (srwKernel n z - srwKernel n z') ^ 2
      = |srwKernel n z - srwKernel n z'| ^ 2 := by rw [sq_abs]
    _ ≤ (((mu + mv : ℕ) : ℝ) *
          (192 / (N * Real.sqrt N)) *
            Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
              (1024 * N))) ^ 2 := by
            exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
    _ = 36864 * (((mu + mv : ℕ) : ℝ) ^ 2 / N ^ 3) *
          Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
            (512 * N)) := by
            have hpref := rotated_edge_prefactor_sq n
            have hprefN : (192 / (N * Real.sqrt N)) ^ 2 =
                36864 / N ^ 3 := by simpa [N] using hpref
            calc
              _ = ((mu + mv : ℕ) : ℝ) ^ 2 *
                    (192 / (N * Real.sqrt N)) ^ 2 *
                      Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
                        (1024 * N)) ^ 2 := by ring
              _ = ((mu + mv : ℕ) : ℝ) ^ 2 * (36864 / N ^ 3) *
                    Real.exp (-((rotU z : ℝ) ^ 2 + (rotV z : ℝ) ^ 2) /
                      (512 * N)) := by rw [hprefN, hExpSq]
              _ = _ := by ring
    _ ≤ 36864 * (D / (n : ℝ) ^ 3) *
          Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hLden (by norm_num)
            · exact hrate
            · positivity
            · positivity
    _ = _ := by ring

private lemma exp_rate_mono {a b R t : ℝ} (hab : b ≤ a)
    (hR : 0 ≤ R) (ht : 0 < t) :
    Real.exp (-a * R / t) ≤ Real.exp (-b * R / t) := by
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right (neg_le_neg hab) hR
  exact div_le_div_of_nonneg_right hmul (by positivity)

private lemma srwKernel_sq_gaussian {n : ℕ} {z : Site} {A c : ℝ}
    (hn : 1 ≤ n) (hA : 0 ≤ A)
    (hK : 0 ≤ srwKernel n z)
    (hbound : srwKernel n z ≤ A / n *
      Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n)) :
    (srwKernel n z) ^ 2 ≤ (A / n) ^ 2 *
      Real.exp (-(2 * c) * ‖siteToPlane z‖ ^ 2 / n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hB : 0 ≤ A / n *
      Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) := by positivity
  have hs := (sq_le_sq₀ hK hB).2 hbound
  have hExpSq :
      Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) ^ 2 =
        Real.exp (-(2 * c) * ‖siteToPlane z‖ ^ 2 / n) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (srwKernel n z) ^ 2 ≤
        (A / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n)) ^ 2 := hs
    _ = (A / n) ^ 2 * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) ^ 2 := by
          rw [mul_pow]
    _ = (A / n) ^ 2 *
        Real.exp (-(2 * c) * ‖siteToPlane z‖ ^ 2 / n) := by rw [hExpSq]

/-- Squared differences of the planar walk kernel at same-parity sites satisfy a Gaussian
gradient bound, as used in the proof of KPZ Lemma A.2. -/
theorem srwKernel_sameParity_sq_diff_le :
    ∃ C c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ z z' : Site,
      Even (z 0 + z 1 + z' 0 + z' 1) →
      (srwKernel n z - srwKernel n z') ^ 2 ≤
        C * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
          (Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-c * ‖siteToPlane z'‖ ^ 2 / n)) := by
  obtain ⟨CG, cG, hcG, hG⟩ := srwKernel_gaussianBound
  let C : ℝ := 36864 + 2 * CG ^ 2
  let c : ℝ := min (1 / 512) cG
  refine ⟨C, c, by positivity, ?_⟩
  intro n hn z z' hparity
  let D : ℝ := ‖siteToPlane (z - z')‖ ^ 2
  have hDnonneg : 0 ≤ D := sq_nonneg _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hCshort : 36864 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg CG]
  have hcoeffnonneg : 0 ≤ D / (n : ℝ) ^ 3 := by positivity
  have hcsmall : c ≤ (1 / 512 : ℝ) := by
    dsimp [c]
    exact min_le_left _ _
  have hrate_small :
      Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) ≤
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) :=
    exp_rate_mono hcsmall (sq_nonneg _) hnR
  by_cases hshort : D ≤ n
  · have hlocal := srwKernel_sameParity_sq_diff_short n hn z z' hparity (by
      change D ≤ (n : ℝ) at hshort
      exact hshort)
    have hsum :
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) ≤
          Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-c * ‖siteToPlane z'‖ ^ 2 / n) :=
      le_add_of_nonneg_right (Real.exp_nonneg _)
    have hCcoeff : 36864 * D / (n : ℝ) ^ 3 ≤ C * D / (n : ℝ) ^ 3 := by
      calc
        36864 * D / (n : ℝ) ^ 3 = 36864 * (D / (n : ℝ) ^ 3) := by ring
        _ ≤ C * (D / (n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hCshort hcoeffnonneg
        _ = C * D / (n : ℝ) ^ 3 := by ring
    have hlocal' :
        (srwKernel n z - srwKernel n z') ^ 2 ≤
          36864 * D / (n : ℝ) ^ 3 *
            Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := by
      simpa only [D] using hlocal
    calc
      (srwKernel n z - srwKernel n z') ^ 2
        ≤ 36864 * D / (n : ℝ) ^ 3 *
            Real.exp (-(1 / 512 : ℝ) * ‖siteToPlane z‖ ^ 2 / n) := hlocal'
      _ ≤ 36864 * D / (n : ℝ) ^ 3 *
            (Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) +
              Real.exp (-c * ‖siteToPlane z'‖ ^ 2 / n)) :=
          mul_le_mul_of_nonneg_left (hrate_small.trans hsum) (by positivity)
      _ ≤ C * D / (n : ℝ) ^ 3 *
            (Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) +
              Real.exp (-c * ‖siteToPlane z'‖ ^ 2 / n)) :=
          mul_le_mul_of_nonneg_right hCcoeff (by positivity)
  · have hDlarge : (n : ℝ) < D := lt_of_not_ge hshort
    have hscale : 1 / (n : ℝ) ^ 2 ≤ D / (n : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDlarge)
        (sq_nonneg (n : ℝ))
      nlinarith [hmul]
    let w : Site := ![(1 : ℤ), 0]
    have hw : 0 < srwKernel 1 w := by
      rw [srwKernel_rotated_product]
      norm_num [w, rotU, rotV, LatticeProb.S1_succ, LatticeProb.S1_zero]
    have hCGbound0 := hG 1 (by norm_num) w
    have hCGupper0 : srwKernel 1 w ≤ CG *
        Real.exp (-cG * ‖siteToPlane w‖ ^ 2 / 1) := by
      simpa using hCGbound0
    have hCGpos : 0 < CG := by
      by_contra hnot
      have hCGle : CG ≤ 0 := le_of_not_gt hnot
      have hRhs : CG * Real.exp (-cG * ‖siteToPlane w‖ ^ 2 / 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hCGle (Real.exp_nonneg _)
      exact (not_lt_of_ge (hCGupper0.trans hRhs) hw).elim
    have hCG : 0 ≤ CG := hCGpos.le
    have hCGbound := hG n hn z
    have hCGbound' := hG n hn z'
    have hsqz := srwKernel_sq_gaussian hn hCG (Critical2DKPZ.srwKernel_nonneg n z) hCGbound
    have hsqz' := srwKernel_sq_gaussian hn hCG (Critical2DKPZ.srwKernel_nonneg n z') hCGbound'
    have hsqdiff : (srwKernel n z - srwKernel n z') ^ 2 ≤
        2 * ((srwKernel n z) ^ 2 + (srwKernel n z') ^ 2) := by
      nlinarith [sq_nonneg (srwKernel n z + srwKernel n z')]
    have hsumrate :
        Real.exp (-(2 * cG) * ‖siteToPlane z‖ ^ 2 / n) +
          Real.exp (-(2 * cG) * ‖siteToPlane z'‖ ^ 2 / n) ≤
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) +
          Real.exp (-c * ‖siteToPlane z'‖ ^ 2 / n) := by
      have hc_le : c ≤ 2 * cG := by
        dsimp [c]
        calc
          min (1 / 512 : ℝ) cG ≤ cG := min_le_right _ _
          _ ≤ 2 * cG := by nlinarith [hcG]
      exact add_le_add
        (exp_rate_mono hc_le (sq_nonneg _) hnR)
        (exp_rate_mono hc_le (sq_nonneg _) hnR)
    have hCwide : 2 * CG ^ 2 ≤ C := by
      dsimp [C]
      nlinarith [sq_nonneg CG]
    have hcoef : 2 * ((CG : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
        C * D / (n : ℝ) ^ 3 := by
      calc
        2 * (CG ^ 2 / (n : ℝ) ^ 2) = 2 * CG ^ 2 / (n : ℝ) ^ 2 := by ring
        _ ≤ C / (n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hCwide (by positivity)
        _ = C * (1 / (n : ℝ) ^ 2) := by ring
        _ ≤ C * (D / (n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = C * D / (n : ℝ) ^ 3 := by ring
    have hsumG :
        (srwKernel n z) ^ 2 + (srwKernel n z') ^ 2 ≤
          (CG / n) ^ 2 *
              Real.exp (-(2 * cG) * ‖siteToPlane z‖ ^ 2 / n) +
            (CG / n) ^ 2 *
              Real.exp (-(2 * cG) * ‖siteToPlane z'‖ ^ 2 / n) :=
      add_le_add hsqz hsqz'
    have hCGsquare : (CG / (n : ℝ)) ^ 2 = CG ^ 2 / (n : ℝ) ^ 2 := by
      rw [div_pow]
    calc
      (srwKernel n z - srwKernel n z') ^ 2
        ≤ 2 * ((srwKernel n z) ^ 2 + (srwKernel n z') ^ 2) := hsqdiff
      _ ≤ 2 * ((CG / n) ^ 2 *
            Real.exp (-(2 * cG) * ‖siteToPlane z‖ ^ 2 / n) +
          (CG / n) ^ 2 *
            Real.exp (-(2 * cG) * ‖siteToPlane z'‖ ^ 2 / n)) :=
          mul_le_mul_of_nonneg_left hsumG (by norm_num)
      _ = 2 * (CG ^ 2 / (n : ℝ) ^ 2) *
            (Real.exp (-(2 * cG) * ‖siteToPlane z‖ ^ 2 / n) +
              Real.exp (-(2 * cG) * ‖siteToPlane z'‖ ^ 2 / n)) := by
          rw [hCGsquare]
          ring
      _ ≤ C * D / (n : ℝ) ^ 3 *
            (Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) +
              Real.exp (-c * ‖siteToPlane z'‖ ^ 2 / n)) := by
          calc
            _ ≤ C * D / (n : ℝ) ^ 3 *
                (Real.exp (-(2 * cG) * ‖siteToPlane z‖ ^ 2 / n) +
                  Real.exp (-(2 * cG) * ‖siteToPlane z'‖ ^ 2 / n)) :=
                    mul_le_mul_of_nonneg_right hcoef (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left hsumrate (by positivity)

end Critical2DKPZ.WalkTails
