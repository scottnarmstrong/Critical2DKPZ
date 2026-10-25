/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.Moment

/-! # Bounds for coordinate-schedule averages

A Chernoff bound on coordinate counts controls the schedule average of the product
of inverse square roots by a constant times `r^{-d/2}`. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The schedule average of `∏_i (N_i+1)^{-1/2}` -/

/-- Bound on the reciprocal of a coordinate count used in the multinomial Chernoff estimate behind the sup bound. -/
lemma one_div_sqrt_cnt_le_one {r : ℕ} (c : Fin r → Fin d) (i : Fin d) :
    (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ 1 := by
  have hge : (1 : ℝ) ≤ (cnt c i : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (cnt c i : ℝ) := Nat.cast_nonneg _
    linarith
  have h1 : (1 : ℝ) ≤ Real.sqrt ((cnt c i : ℝ) + 1) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt hge
  rw [div_le_one (by linarith)]
  exact h1

/-- The reciprocal square root of a coordinate count plus one is nonnegative. -/
lemma one_div_sqrt_cnt_nonneg {r : ℕ} (c : Fin r → Fin d) (i : Fin d) :
    (0 : ℝ) ≤ (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) := by positivity

/-- Either some coordinate is updated at most `a` times, or every factor of the
product is at most `(a+2)^{-1/2}`. -/
lemma sched_prod_bound {r : ℕ} (c : Fin r → Fin d) (a : ℕ) :
    ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
        + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
  by_cases hex : ∃ i : Fin d, cnt c i ≤ a
  · obtain ⟨i₀, hi₀⟩ := hex
    have hone : (1 : ℝ) ≤ ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
      calc (1 : ℝ) = (if cnt c i₀ ≤ a then (1 : ℝ) else 0) := by rw [ite_eq_left hi₀]
        _ ≤ _ := Finset.single_le_sum (f := fun i => (if cnt c i ≤ a then (1 : ℝ) else 0))
              (fun i _ => by split <;> norm_num) (Finset.mem_univ i₀)
    have hprod : ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ 1 := by
      calc ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ ∏ _i : Fin d, (1 : ℝ) :=
            Finset.prod_le_prod₀ (fun i _ => one_div_sqrt_cnt_nonneg c i)
              (fun i _ => one_div_sqrt_cnt_le_one c i)
        _ = 1 := by simp
    have : (0 : ℝ) ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by positivity
    linarith
  · push Not at hex
    have hfac : ∀ i : Fin d,
        (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ := by
      intro i
      have ha : (a : ℝ) + 2 ≤ (cnt c i : ℝ) + 1 := by
        have : a + 1 ≤ cnt c i := hex i
        have : ((a : ℝ) + 1) ≤ (cnt c i : ℝ) := by exact_mod_cast this
        linarith
      have hpos : (0 : ℝ) < Real.sqrt ((a : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
      rw [one_div, inv_le_inv₀ (by positivity) hpos]
      exact Real.sqrt_le_sqrt ha
    have hsum : (0 : ℝ) ≤ ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun i _ => by split <;> norm_num
    have hprod : ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by
      calc ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ ∏ _i : Fin d, (Real.sqrt ((a : ℝ) + 2))⁻¹ :=
            Finset.prod_le_prod₀ (fun i _ => one_div_sqrt_cnt_nonneg c i) (fun i _ => hfac i)
        _ = ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by simp
    linarith

/-! ### Real-power and square-root identities -/

/-- A negative half-integer power equals the reciprocal of the corresponding square-root power. -/
lemma rpow_neg_half_eq (d R : ℕ) :
    (R : ℝ) ^ (-(d : ℝ) / 2) = ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have h1 : (Real.sqrt (R : ℝ)) ^ d = (R : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((R : ℝ) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul hR0]
    congr 1
    ring
  rw [h1, ← Real.rpow_neg hR0]
  congr 1
  ring


/-! ### The constant -/

/-- An explicit dimension-dependent constant for the coordinate-schedule bound. -/
noncomputable def greenConst (d : ℕ) : ℝ :=
  (Real.sqrt (4 * (d : ℝ))) ^ d + (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d

/-- The coordinate-schedule bound constant is nonnegative. -/
lemma greenConst_nonneg (d : ℕ) : 0 ≤ greenConst d := by
  unfold greenConst
  have h1 : (0 : ℝ) ≤ (Real.sqrt (4 * (d : ℝ))) ^ d := by positivity
  have h2 : (0 : ℝ) ≤ (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d := by positivity
  linarith

/-! ### The sup bound -/

/-- There are `d^r` coordinate schedules of length `r`. -/
lemma card_sched (r : ℕ) :
    ((Finset.univ : Finset (Fin r → Fin d)).card : ℝ) = (d : ℝ) ^ r := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  ring

/-- The Chernoff step: the schedule average of `∏_i (N_i+1)^{-1/2}` splits into a
bulk term and `d` tail terms. -/
lemma sched_sum_bound (hd : 0 < d) (R : ℕ) :
    ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ (d : ℝ) ^ R * ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
        + (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
  classical
  set a : ℕ := R / (4 * d) with ha
  have step1 : ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ ∑ c : Fin R → Fin d, (((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
          + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum fun c _ => sched_prod_bound c a
  have step2 : ∑ c : Fin R → Fin d, (((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
        + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0))
      = (d : ℝ) ^ R * ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
        + ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_sched, Finset.sum_comm]
  have step3 : ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
      ≤ (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
    calc ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin d, ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) :=
          Finset.sum_le_sum fun i _ => sum_indicator_cnt_le hd R i
      _ = (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [step1, step2.le, step3]

/-- The bulk contribution is bounded by a dimension-dependent constant times `R^{-d/2}`. -/
lemma bulk_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) :
    ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
      ≤ (Real.sqrt (4 * (d : ℝ))) ^ d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
  have hmod : R < 4 * d * (R / (4 * d) + 1) := by
    have h2 : 0 < 4 * d := by omega
    calc R = 4 * d * (R / (4 * d)) + R % (4 * d) := (Nat.div_add_mod R (4 * d)).symm
      _ < 4 * d * (R / (4 * d)) + 4 * d := by have := Nat.mod_lt R h2; omega
      _ = 4 * d * (R / (4 * d) + 1) := by ring
  set a : ℕ := R / (4 * d) with ha
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hRle : (R : ℝ) / (4 * (d : ℝ)) ≤ (a : ℝ) + 2 := by
    have : (R : ℝ) ≤ 4 * (d : ℝ) * ((a : ℝ) + 2) := by
      have : (R : ℝ) < 4 * (d : ℝ) * ((a : ℝ) + 1) := by exact_mod_cast hmod
      nlinarith [hdR]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsq : Real.sqrt ((R : ℝ) / (4 * (d : ℝ))) ≤ Real.sqrt ((a : ℝ) + 2) :=
    Real.sqrt_le_sqrt hRle
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hsqpos : (0 : ℝ) < Real.sqrt ((R : ℝ) / (4 * (d : ℝ))) :=
    Real.sqrt_pos.mpr (by positivity)
  have hinv : (Real.sqrt ((a : ℝ) + 2))⁻¹
      ≤ Real.sqrt (4 * (d : ℝ)) / Real.sqrt (R : ℝ) := by
    have := inv_le_inv₀ (lt_of_lt_of_le hsqpos hsq) hsqpos |>.mpr hsq
    rw [Real.sqrt_div (le_of_lt hRpos)] at this
    rwa [inv_div] at this
  have hnn : (0 : ℝ) ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ := by positivity
  calc ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
      ≤ (Real.sqrt (4 * (d : ℝ)) / Real.sqrt (R : ℝ)) ^ d := pow_le_pow_left₀ hnn hinv d
    _ = (Real.sqrt (4 * (d : ℝ))) ^ d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
        rw [div_pow, div_eq_mul_inv]

/-- The exponential tail contribution is bounded by a dimension-dependent constant times `R^{-d/2}`. -/
lemma tail_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) :
    (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))
      ≤ (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  set s : ℝ := (R : ℝ) / (4 * (d : ℝ)) with hs
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hterm : s ^ d / (Nat.factorial d : ℝ) ≤ Real.exp s := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (le_of_lt hspos) (d + 1))
    refine Finset.single_le_sum (f := fun i => s ^ i / (Nat.factorial i : ℝ)) ?_ ?_
    · intro i _
      positivity
    · simp
  have hpos : (0 : ℝ) < s ^ d / (Nat.factorial d : ℝ) := by positivity
  have hexp : Real.exp (-s) ≤ (Nat.factorial d : ℝ) / s ^ d := by
    rw [Real.exp_neg]
    have h := (inv_le_inv₀ (lt_of_lt_of_le hpos hterm) hpos).mpr hterm
    rwa [inv_div] at h
  have hsd : s ^ d = (R : ℝ) ^ d / (4 * (d : ℝ)) ^ d := by rw [hs, div_pow]
  have hfac : (Nat.factorial d : ℝ) / s ^ d
      = (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d / (R : ℝ) ^ d := by
    rw [hsd]
    field_simp
  have hsr : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
    have h1 : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (R : ℝ) ≤ Real.sqrt ((R : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (R : ℝ) := Real.sqrt_sq (le_of_lt hRpos)
  have hge : (Real.sqrt (R : ℝ)) ^ d ≤ (R : ℝ) ^ d :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr d
  have hinvle : ((R : ℝ) ^ d)⁻¹ ≤ ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
    have h1 : (0 : ℝ) < (Real.sqrt (R : ℝ)) ^ d := by
      have : (0 : ℝ) < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr hRpos
      positivity
    exact inv_le_inv₀ (lt_of_lt_of_le h1 hge) h1 |>.mpr hge
  have hpos : (0 : ℝ) ≤ (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d := by positivity
  rw [show -(R : ℝ) / (4 * (d : ℝ)) = -s from by rw [hs]; ring]
  calc (d : ℝ) * Real.exp (-s)
      ≤ (d : ℝ) * ((Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d / (R : ℝ) ^ d) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hexp (le_of_lt hdR)
    _ = ((d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d) * ((R : ℝ) ^ d)⁻¹ := by
        field_simp
    _ ≤ ((d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d) * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvle hpos

end LatticeProb

end
