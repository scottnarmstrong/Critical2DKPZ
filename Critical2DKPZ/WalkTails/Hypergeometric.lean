/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde

/-! # The squared-binomial walk law

The normalized squared-binomial weights form a hypergeometric law.
Through the increment `2j-m`, they describe the common endpoint of two independent simple walks
conditioned to have the same endpoint after `m` steps.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.WalkTails

open Finset.Nat Finset.HasAntidiagonal

/-- The finite hypergeometric mass at `j`: the squared binomial law on
`{0, ..., m}`.  It is zero outside that interval. -/
def hypergeometricWeight (m j : ℕ) : ℝ :=
  ((Nat.choose m j : ℝ) ^ 2) / (Nat.choose (2 * m) m : ℝ)

/-- The denominator in the squared-binomial law is positive. -/
theorem hypergeometric_denominator_pos (m : ℕ) :
    0 < (Nat.choose (2 * m) m : ℝ) := by
  exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m))

/-- Hypergeometric weights are nonnegative. -/
theorem hypergeometricWeight_nonneg (m j : ℕ) :
    0 ≤ hypergeometricWeight m j := by
  unfold hypergeometricWeight
  positivity

/-- The squared-binomial weights sum to one on their finite support. -/
theorem sum_hypergeometricWeight (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), hypergeometricWeight m j = 1 := by
  unfold hypergeometricWeight
  have hsum :
      (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) ^ 2) =
        (Nat.choose (2 * m) m : ℝ) := by
    have hn := Nat.sum_range_choose_sq m
    exact_mod_cast hn
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [hsum]
  exact div_self (ne_of_gt (hypergeometric_denominator_pos m))

/-- The squared-binomial law is symmetric around `m / 2` (allowing a
half-integer center). -/
theorem hypergeometricWeight_symm (m j : ℕ) (hj : j ≤ m) :
    hypergeometricWeight m (m - j) = hypergeometricWeight m j := by
  unfold hypergeometricWeight
  congr 1
  rw [Nat.choose_symm hj]




/-- The centered value corresponding to atom `j`; this is the rotated
simple-walk increment `2j-m`. -/
def hypergeometricIncrement (m j : ℕ) : ℝ := 2 * (j : ℝ) - m

private theorem sum_choose_mul_choose (a b r : ℕ) :
    (∑ k ∈ Finset.range (r + 1), a.choose k * b.choose (r - k)) =
      (a + b).choose r := by
  calc
    _ = ∑ ij ∈ antidiagonal r, a.choose ij.1 * b.choose ij.2 := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = (a + b).choose r := (Nat.add_choose_eq a b r).symm

private theorem sum_range_mul_choose_sq (m : ℕ) :
    2 * (∑ j ∈ Finset.range (m + 1), j * m.choose j ^ 2) =
      m * (2 * m).choose m := by
  calc
    2 * (∑ j ∈ Finset.range (m + 1), j * m.choose j ^ 2) =
        (∑ j ∈ Finset.range (m + 1), (m - j) * m.choose (m - j) ^ 2) +
          ∑ j ∈ Finset.range (m + 1), j * m.choose j ^ 2 := by
      rw [two_mul, ← Finset.sum_flip]
    _ = (∑ j ∈ Finset.range (m + 1), (m - j) * m.choose j ^ 2) +
          ∑ j ∈ Finset.range (m + 1), j * m.choose j ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hj)]
    _ = ∑ j ∈ Finset.range (m + 1), m * m.choose j ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := Finset.mem_range_succ_iff.mp hj
      calc
        (m - j) * m.choose j ^ 2 + j * m.choose j ^ 2 =
            ((m - j) + j) * m.choose j ^ 2 := by ring
        _ = m * m.choose j ^ 2 := by rw [Nat.sub_add_cancel hjm]
    _ = m * (2 * m).choose m := by
      rw [← Finset.mul_sum, Nat.sum_range_choose_sq]

private theorem choose_mul_index {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    j * m.choose j = m * (m - 1).choose (j - 1) := by
  have h1 : m.choose j * j = m.choose (j - 1) * (m - (j - 1)) := by
    simpa [Nat.sub_add_cancel hj] using Nat.choose_succ_right_eq m (j - 1)
  have h2 : (m - 1).choose (j - 1) * m =
      m.choose (j - 1) * (m - (j - 1)) := by
    have h := Nat.choose_mul_succ_eq (m - 1) (j - 1)
    have hm : m - 1 + 1 = m := by omega
    rw [hm] at h
    exact h
  calc
    j * m.choose j = m.choose j * j := by ac_rfl
    _ = m.choose (j - 1) * (m - (j - 1)) := h1
    _ = (m - 1).choose (j - 1) * m := h2.symm
    _ = m * (m - 1).choose (j - 1) := by ac_rfl

private theorem choose_mul_index_twice {m j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m) :
    j * (j - 1) * m.choose j = m * (m - 1) * (m - 2).choose (j - 2) := by
  have hfirst := choose_mul_index (m := m) (j := j) (by omega) hjm
  have hsecond := choose_mul_index (m := m - 1) (j := j - 1) (by omega) (by omega)
  have hindex : m - 1 - 1 = m - 2 := by omega
  have hjindex : j - 1 - 1 = j - 2 := by omega
  rw [hindex, hjindex] at hsecond
  calc
    j * (j - 1) * m.choose j = (j - 1) * (j * m.choose j) := by ring
    _ = (j - 1) * (m * (m - 1).choose (j - 1)) := by rw [hfirst]
    _ = m * ((j - 1) * (m - 1).choose (j - 1)) := by ring
    _ = m * ((m - 1) * (m - 2).choose (j - 2)) := by rw [hsecond]
    _ = m * (m - 1) * (m - 2).choose (j - 2) := by ring

private theorem sum_range_mul_pred_choose_sq {m : ℕ} (hm : 2 ≤ m) :
    (∑ j ∈ Finset.range (m + 1), j * (j - 1) * m.choose j ^ 2) =
      m * (m - 1) * (2 * m - 2).choose (m - 2) := by
  have hmix := sum_choose_mul_choose (m - 2) m (m - 2)
  have htotal : (m - 2) + m = 2 * m - 2 := by omega
  rw [htotal] at hmix
  rw [Finset.sum_range_succ']
  simp only [zero_mul]
  rw [show m = (m - 1) + 1 by omega, Finset.sum_range_succ']
  simp [Nat.add_assoc]
  rw [show m - 1 + 1 = m by omega]
  have hsum :
      (∑ k ∈ Finset.range (m - 1),
        (m - 2).choose k * m.choose (m - 2 - k)) =
        (2 * m - 2).choose (m - 2) := by
    have hrange : m - 1 = m - 2 + 1 := by omega
    rw [hrange]
    exact hmix
  calc
    (∑ k ∈ Finset.range (m - 1),
        (k + 2) * (k + 1) * m.choose (k + 2) ^ 2) =
        m * (m - 1) *
          (∑ k ∈ Finset.range (m - 1),
            (m - 2).choose k * m.choose (m - 2 - k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < m - 1 := Finset.mem_range.mp hk
      have hjm : k + 2 ≤ m := by omega
      have hchoose := Nat.choose_symm (n := m) (k := k + 2) hjm
      have hindex : m - (k + 2) = m - 2 - k := by omega
      rw [hindex] at hchoose
      have hterm := choose_mul_index_twice (m := m) (j := k + 2) (by omega) hjm
      rw [show k + 2 - 2 = k by omega,
        show k + 2 - 1 = k + 1 by omega] at hterm
      calc
        (k + 2) * (k + 1) * m.choose (k + 2) ^ 2 =
            ((k + 2) * (k + 1) * m.choose (k + 2)) * m.choose (k + 2) := by ring
        _ = (m * (m - 1) * (m - 2).choose k) * m.choose (k + 2) := by rw [hterm]
        _ = m * (m - 1) *
            ((m - 2).choose k * m.choose (m - 2 - k)) := by rw [← hchoose]; ring
    _ = m * (m - 1) * (2 * m - 2).choose (m - 2) := by rw [hsum]

private theorem central_choose_factor {m : ℕ} (hm : 2 ≤ m) :
    (2 * m).choose m * (m - 1) =
      2 * (2 * m - 1) * (2 * m - 2).choose (m - 2) := by
  have hrec :
      (2 * m - 2).choose (m - 1) * (m - 1) =
        (2 * m - 2).choose (m - 2) * m := by
    have h := Nat.choose_succ_right_eq (2 * m - 2) (m - 2)
    have hindex : m - 2 + 1 = m - 1 := by omega
    have hfactor : 2 * m - 2 - (m - 2) = m := by omega
    simpa [hindex, hfactor] using h
  have hsplit :
      (2 * m - 1).choose (m - 1) =
        (2 * m - 2).choose (m - 2) + (2 * m - 2).choose (m - 1) := by
    have h := Nat.choose_succ_succ (2 * m - 2) (m - 2)
    have htop : 2 * m - 2 + 1 = 2 * m - 1 := by omega
    have hindex : m - 2 + 1 = m - 1 := by omega
    simpa [htop, hindex] using h
  have hsymm : (2 * m - 1).choose m = (2 * m - 1).choose (m - 1) := by
    have h := Nat.choose_symm (n := 2 * m - 1) (k := m) (by omega)
    have hindex : 2 * m - 1 - m = m - 1 := by omega
    simpa [hindex] using h.symm
  have hdouble : (2 * m).choose m = 2 * (2 * m - 1).choose (m - 1) := by
    have h := Nat.choose_succ_succ (2 * m - 1) (m - 1)
    have htop : 2 * m - 1 + 1 = 2 * m := by omega
    have hindex : m - 1 + 1 = m := by omega
    have h' : (2 * m).choose m =
        (2 * m - 1).choose (m - 1) + (2 * m - 1).choose m := by
      simpa only [Nat.succ_eq_add_one, htop, hindex] using h
    rw [hsymm] at h'
    simpa [two_mul] using h'
  rw [hdouble, hsplit]
  calc
    2 * ((2 * m - 2).choose (m - 2) + (2 * m - 2).choose (m - 1)) * (m - 1) =
        2 * ((2 * m - 2).choose (m - 2) * (m - 1) +
          (2 * m - 2).choose (m - 1) * (m - 1)) := by ring
    _ = 2 * ((2 * m - 2).choose (m - 2) * (m - 1) +
          (2 * m - 2).choose (m - 2) * m) := by rw [hrec]
    _ = 2 * (2 * m - 1) * (2 * m - 2).choose (m - 2) := by
      have hsum : m + (m - 1) = 2 * m - 1 := by omega
      rw [← hsum]
      ring

/-- For `m ≥ 2`, the squared-binomial increment `2j-m` has second moment `m²/(2m-1)`. -/
private theorem hypergeometricIncrement_secondMoment_of_two (m : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ Finset.range (m + 1),
      hypergeometricWeight m j * hypergeometricIncrement m j ^ 2) =
      (m : ℝ) ^ 2 / (2 * (m : ℝ) - 1) := by
  have hsum0Nat := Nat.sum_range_choose_sq m
  have hsum1Nat := sum_range_mul_choose_sq m
  have hsum2Nat := sum_range_mul_pred_choose_sq (by omega : 2 ≤ m)
  have hfactorNat := central_choose_factor (by omega : 2 ≤ m)
  have hsum0 :
      (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) ^ 2) =
        (Nat.choose (2 * m) m : ℝ) := by exact_mod_cast hsum0Nat
  have hsum1 :
      2 * (∑ j ∈ Finset.range (m + 1),
        (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) =
        (m : ℝ) * (Nat.choose (2 * m) m : ℝ) := by exact_mod_cast hsum1Nat
  have hsum2Cast :
      (∑ j ∈ Finset.range (m + 1),
        ((j * (j - 1) : ℕ) : ℝ) * (Nat.choose m j : ℝ) ^ 2) =
        ((m * (m - 1) : ℕ) : ℝ) * (Nat.choose (2 * m - 2) (m - 2) : ℝ) := by
    exact_mod_cast hsum2Nat
  have hsum2 :
      (∑ j ∈ Finset.range (m + 1),
        (j : ℝ) * ((j : ℝ) - 1) * (Nat.choose m j : ℝ) ^ 2) =
        (m : ℝ) * ((m : ℝ) - 1) *
          (Nat.choose (2 * m - 2) (m - 2) : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1),
          ((j * (j - 1) : ℕ) : ℝ) * (Nat.choose m j : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hj0 : j = 0
            · subst j
              simp
            · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
              rw [Nat.cast_mul, Nat.cast_sub hjpos]
              norm_num
      _ = (m : ℝ) * ((m : ℝ) - 1) *
          (Nat.choose (2 * m - 2) (m - 2) : ℝ) := by
            have hmcast : ((m * (m - 1) : ℕ) : ℝ) =
                (m : ℝ) * ((m : ℝ) - 1) := by
              rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]
              norm_num
            rw [hsum2Cast, hmcast]
  have hfactorCast := congrArg (fun k : ℕ => (k : ℝ)) hfactorNat
  push_cast [Nat.cast_sub (by omega : 1 ≤ m),
    Nat.cast_sub (by omega : 1 ≤ 2 * m)] at hfactorCast
  have hfactor :
      (Nat.choose (2 * m) m : ℝ) * ((m : ℝ) - 1) =
        2 * (2 * (m : ℝ) - 1) *
          (Nat.choose (2 * m - 2) (m - 2) : ℝ) := hfactorCast
  have hden : 0 < (Nat.choose (2 * m) m : ℝ) := hypergeometric_denominator_pos m
  have hmone : 1 ≤ m := by omega
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hmone
  have hscale : 0 < 2 * (m : ℝ) - 1 := by nlinarith
  have hfirstMoment :
      (∑ j ∈ Finset.range (m + 1),
        (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) =
        (m : ℝ) / 2 * (Nat.choose (2 * m) m : ℝ) := by linarith [hsum1]
  have hsecondFactor :
      (Nat.choose (2 * m - 2) (m - 2) : ℝ) =
        ((Nat.choose (2 * m) m : ℝ) * ((m : ℝ) - 1)) /
          (2 * (2 * (m : ℝ) - 1)) := by
    have hden2 : 2 * (2 * (m : ℝ) - 1) ≠ 0 := by positivity
    calc
      (Nat.choose (2 * m - 2) (m - 2) : ℝ) =
          (2 * (2 * (m : ℝ) - 1) *
            (Nat.choose (2 * m - 2) (m - 2) : ℝ)) /
            (2 * (2 * (m : ℝ) - 1)) := by field_simp [hden2]
      _ = ((Nat.choose (2 * m) m : ℝ) * ((m : ℝ) - 1)) /
            (2 * (2 * (m : ℝ) - 1)) := by rw [← hfactor]
  have hnum :
      (∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) ^ 2 * (2 * (j : ℝ) - m) ^ 2) =
        (m : ℝ) ^ 2 * (Nat.choose (2 * m) m : ℝ) /
          (2 * (m : ℝ) - 1) := by
    have hexpand :
        (∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) ^ 2 * (2 * (j : ℝ) - m) ^ 2) =
          4 * (∑ j ∈ Finset.range (m + 1),
            (j : ℝ) * ((j : ℝ) - 1) * (Nat.choose m j : ℝ) ^ 2) +
          4 * (∑ j ∈ Finset.range (m + 1),
            (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) * (1 - (m : ℝ)) +
          (m : ℝ) ^ 2 * (∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) ^ 2) := by
      calc
        _ = ∑ j ∈ Finset.range (m + 1),
            (4 * ((j : ℝ) * ((j : ℝ) - 1) * (Nat.choose m j : ℝ) ^ 2) +
              4 * ((j : ℝ) * (Nat.choose m j : ℝ) ^ 2) * (1 - (m : ℝ)) +
              (m : ℝ) ^ 2 * (Nat.choose m j : ℝ) ^ 2) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          have hmiddle :
              (∑ j ∈ Finset.range (m + 1),
                4 * ((j : ℝ) * (Nat.choose m j : ℝ) ^ 2) * (1 - (m : ℝ))) =
                (4 * (∑ j ∈ Finset.range (m + 1),
                  (j : ℝ) * (Nat.choose m j : ℝ) ^ 2)) * (1 - (m : ℝ)) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          rw [hmiddle, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hexpand, hsum2, hfirstMoment, hsum0, hsecondFactor]
    have hscaleNe : 2 * (m : ℝ) - 1 ≠ 0 := ne_of_gt hscale
    have hscaleNe2 : 2 * (2 * (m : ℝ) - 1) ≠ 0 := by positivity
    have hscaleNe' : -1 + (m : ℝ) * 2 ≠ 0 := by nlinarith [hscale]
    have hscaleNe3 : (m : ℝ) * 2 - 1 ≠ 0 := by nlinarith [hscale]
    field_simp [hscaleNe, hscaleNe2, hscaleNe', hscaleNe3]; ring
  have hnumDiv :
      ((∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) ^ 2 * (2 * (j : ℝ) - m) ^ 2) /
          (Nat.choose (2 * m) m : ℝ)) =
        (m : ℝ) ^ 2 / (2 * (m : ℝ) - 1) := by
    rw [hnum]
    field_simp [ne_of_gt hden, ne_of_gt hscale]
  unfold hypergeometricWeight hypergeometricIncrement
  calc
    _ = (∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) ^ 2 * (2 * (j : ℝ) - m) ^ 2) /
          (Nat.choose (2 * m) m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [ne_of_gt hden]
    _ = _ := hnumDiv

/-- The squared-binomial increment `2j-m` has mean zero. -/
theorem hypergeometricIncrement_firstMoment (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      hypergeometricWeight m j * hypergeometricIncrement m j) = 0 := by
  have hsum0 :
      (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) ^ 2) =
        (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast Nat.sum_range_choose_sq m
  have hsum1 :
      2 * (∑ j ∈ Finset.range (m + 1),
        (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) =
        (m : ℝ) * (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast sum_range_mul_choose_sq m
  have hnum :
      (∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) ^ 2 * (2 * (j : ℝ) - m)) = 0 := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1),
            (2 * (j : ℝ) * (Nat.choose m j : ℝ) ^ 2 -
              (m : ℝ) * (Nat.choose m j : ℝ) ^ 2) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
      _ = (∑ j ∈ Finset.range (m + 1),
            2 * (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) -
          (∑ j ∈ Finset.range (m + 1),
            (m : ℝ) * (Nat.choose m j : ℝ) ^ 2) := by
              rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ j ∈ Finset.range (m + 1),
            (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) -
          (m : ℝ) * (∑ j ∈ Finset.range (m + 1),
            (Nat.choose m j : ℝ) ^ 2) := by
              have hA :
                  (∑ j ∈ Finset.range (m + 1),
                    2 * (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) =
                    2 * (∑ j ∈ Finset.range (m + 1),
                      (j : ℝ) * (Nat.choose m j : ℝ) ^ 2) := by
                calc
                  _ = ∑ j ∈ Finset.range (m + 1),
                      2 * ((j : ℝ) * (Nat.choose m j : ℝ) ^ 2) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                  _ = _ := by rw [Finset.mul_sum]
              have hB :
                  (∑ j ∈ Finset.range (m + 1),
                    (m : ℝ) * (Nat.choose m j : ℝ) ^ 2) =
                    (m : ℝ) * (∑ j ∈ Finset.range (m + 1),
                      (Nat.choose m j : ℝ) ^ 2) := by
                rw [Finset.mul_sum]
              rw [hA, hB]
      _ = 0 := by rw [hsum1, hsum0]; ring
  unfold hypergeometricWeight hypergeometricIncrement
  simp only [div_eq_mul_inv]
  calc
    _ = ∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) ^ 2 *
            (2 * (j : ℝ) - (m : ℝ)) *
            (Nat.choose (2 * m) m : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
    _ = (∑ j ∈ Finset.range (m + 1),
          (Nat.choose m j : ℝ) ^ 2 * (2 * (j : ℝ) - (m : ℝ))) *
          (Nat.choose (2 * m) m : ℝ)⁻¹ := by rw [← Finset.sum_mul]
    _ = 0 := by rw [hnum]; simp

/-- The squared-binomial increment `2j-m` has second moment `m²/(2m-1)`, including at `m = 0`. -/
theorem hypergeometricIncrement_secondMoment (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      hypergeometricWeight m j * hypergeometricIncrement m j ^ 2) =
      (m : ℝ) ^ 2 / (2 * (m : ℝ) - 1) := by
  by_cases hm0 : m = 0
  · subst m
    norm_num [hypergeometricWeight, hypergeometricIncrement, Nat.choose]
  · by_cases hm1 : m = 1
    · subst m
      norm_num [hypergeometricWeight, hypergeometricIncrement, Nat.choose,
        Finset.sum_range_succ]
    · exact hypergeometricIncrement_secondMoment_of_two m (by omega)

end Critical2DKPZ.WalkTails

end
