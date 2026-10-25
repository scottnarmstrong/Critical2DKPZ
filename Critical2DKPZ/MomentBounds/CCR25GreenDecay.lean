/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FreeKernelGaussian
import Mathlib.Tactic

/-! # Spatial Green decay for the CCR25 summed free kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem exp_neg_le_inverse_nat_power {h : ℕ} (hh : 1 ≤ h) {x : ℝ}
    (hx : 0 ≤ x) :
    Real.exp (-x) ≤ ((1 + x / (h : ℝ)) ^ h)⁻¹ := by
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hh)
  have hbase : 0 ≤ 1 + x / (h : ℝ) := by positivity
  have hexp : (1 + x / (h : ℝ)) ^ h ≤ Real.exp x := by
    calc
      (1 + x / (h : ℝ)) ^ h ≤ Real.exp (x / (h : ℝ)) ^ h :=
        pow_le_pow_left₀ hbase (by simpa [add_comm] using Real.add_one_le_exp (x / (h : ℝ))) h
      _ = Real.exp ((h : ℝ) * (x / (h : ℝ))) := by rw [Real.exp_nat_mul]
      _ = Real.exp x := by
        congr 2
        field_simp
  have hbasepos : 0 < 1 + x / (h : ℝ) := by positivity
  have hinv := one_div_le_one_div_of_le (pow_pos hbasepos h) hexp
  simpa [Real.exp_neg] using hinv

private theorem shifted_inverse_square_sum_bound {L : ℕ} {a : ℝ} (ha : 0 < a) :
    (∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ 2)⁻¹) ≤ a⁻¹ := by
  have hstrong (L : ℕ) :
      (∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ 2)⁻¹) ≤
        a⁻¹ - (a + (L : ℝ))⁻¹ := by
    induction L with
    | zero => simp
    | succ L ih =>
        rw [Finset.sum_range_succ]
        have hx : 0 < a + (L : ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
        have hstep : ((a + (L : ℝ) + 1) ^ 2)⁻¹ ≤
            (a + (L : ℝ))⁻¹ - (a + (L : ℝ) + 1)⁻¹ := by
          have hp : 0 < a + (L : ℝ) + 1 := by positivity
          field_simp [ne_of_gt hx, ne_of_gt hp]
          nlinarith
        calc
          (∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ 2)⁻¹) +
                ((a + (L : ℝ) + 1) ^ 2)⁻¹ ≤
              (a⁻¹ - (a + (L : ℝ))⁻¹) +
                ((a + (L : ℝ))⁻¹ - (a + (L : ℝ) + 1)⁻¹) :=
            add_le_add ih hstep
          _ = a⁻¹ - (a + ((L + 1 : ℕ) : ℝ))⁻¹ := by
            rw [Nat.cast_succ]
            ring
  calc
    _ ≤ a⁻¹ - (a + (L : ℝ))⁻¹ := hstrong L
    _ ≤ a⁻¹ := by
      have hnonneg : 0 ≤ (a + (L : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt (by positivity))
      linarith

private theorem shifted_inverse_power_sum_bound {h L : ℕ} (hh : 2 ≤ h) {a : ℝ}
    (ha : 1 ≤ a) :
    (∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ h)⁻¹) ≤
      2 / (1 + a) ^ (h - 1) := by
  have hterm (n : ℕ) :
      ((a + (n : ℝ) + 1) ^ h)⁻¹ ≤
        ((1 + a) ^ (h - 2))⁻¹ * ((a + (n : ℝ) + 1) ^ 2)⁻¹ := by
    let y : ℝ := a + (n : ℝ) + 1
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hy : 1 + a ≤ y := by
      dsimp [y]
      nlinarith only [ha, hnnonneg]
    have hbase : 0 < 1 + a := by linarith
    have hypos : 0 < y := lt_of_lt_of_le hbase hy
    have hpow : (1 + a) ^ (h - 2) ≤ y ^ (h - 2) :=
      pow_le_pow_left₀ hbase.le hy (h - 2)
    have hdecomp : h = (h - 2) + 2 := by omega
    change (y ^ h)⁻¹ ≤ ((1 + a) ^ (h - 2))⁻¹ * (y ^ 2)⁻¹
    rw [hdecomp, pow_add, mul_inv_rev, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (inv_le_inv₀ (pow_pos hypos (h - 2)) (pow_pos hbase (h - 2)) |>.2 hpow)
      (inv_nonneg.mpr (pow_nonneg hypos.le 2))
  have hsum :
      (∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ h)⁻¹) ≤
        ((1 + a) ^ (h - 2))⁻¹ * a⁻¹ := by
    calc
      _ ≤ ∑ n ∈ Finset.range L,
          ((1 + a) ^ (h - 2))⁻¹ * ((a + (n : ℝ) + 1) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun n _ => hterm n
      _ = ((1 + a) ^ (h - 2))⁻¹ *
          ∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ 2)⁻¹ := by rw [← Finset.mul_sum]
      _ ≤ ((1 + a) ^ (h - 2))⁻¹ * a⁻¹ :=
        mul_le_mul_of_nonneg_left (shifted_inverse_square_sum_bound (by linarith)) (by positivity)
  have hscale : a⁻¹ ≤ 2 / (1 + a) := by
    have hineq : 1 + a ≤ 2 * a := by linarith
    have hdiv : (1 : ℝ) / a ≤ 2 / (1 + a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hineq]
    simpa [one_div] using hdiv
  have hpower :
      ((1 + a) ^ (h - 2))⁻¹ * (1 + a)⁻¹ = ((1 + a) ^ (h - 1))⁻¹ := by
    have he : h - 1 = (h - 2) + 1 := by omega
    rw [he, pow_succ]
    field_simp
  calc
    _ ≤ ((1 + a) ^ (h - 2))⁻¹ * a⁻¹ := hsum
    _ ≤ ((1 + a) ^ (h - 2))⁻¹ * (2 / (1 + a)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 2 / (1 + a) ^ (h - 1) := by
      calc
        _ = 2 * (((1 + a) ^ (h - 2))⁻¹ * (1 + a)⁻¹) := by ring
        _ = 2 * ((1 + a) ^ (h - 1))⁻¹ := by rw [hpower]
        _ = _ := by rw [div_eq_mul_inv]

/-- One Gaussian time term is controlled by a shifted inverse power. -/
private theorem gaussian_time_term_le_shifted_inverse {h : ℕ} (hh : 1 ≤ h)
    (n : ℕ) (hn : 1 ≤ n) {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E) :
    ((n : ℝ) ^ h)⁻¹ * Real.exp (-c * E / (n : ℝ)) ≤
      (((n : ℝ) + c * E / (h : ℝ)) ^ h)⁻¹ := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hh)
  let a : ℝ := c * E / (h : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have harg : c * E / (n : ℝ) / (h : ℝ) = a / (n : ℝ) := by
    dsimp [a]
    field_simp [ne_of_gt hnpos, ne_of_gt hhpos]
  have hbase :
      1 + c * E / (n : ℝ) / (h : ℝ) = ((n : ℝ) + a) / (n : ℝ) := by
    rw [harg]
    dsimp [a]
    field_simp [ne_of_gt hnpos, ne_of_gt hhpos]
  have hexp := exp_neg_le_inverse_nat_power hh
    (div_nonneg (mul_nonneg hc.le hE) hnpos.le)
  have hmult := mul_le_mul_of_nonneg_left hexp
    (inv_nonneg.mpr (pow_nonneg hnpos.le h))
  have hexpArg : Real.exp (-(c * E / (n : ℝ))) =
      Real.exp (-c * E / (n : ℝ)) := by
    congr 1
    ring
  have hEq :
      ((n : ℝ) ^ h)⁻¹ *
        ((1 + c * E / (n : ℝ) / (h : ℝ)) ^ h)⁻¹ =
          (((n : ℝ) + a) ^ h)⁻¹ := by
    rw [hbase, div_pow]
    field_simp [ne_of_gt hnpos, ne_of_gt (add_pos_of_pos_of_nonneg hnpos ha)]
  calc
    ((n : ℝ) ^ h)⁻¹ * Real.exp (-c * E / (n : ℝ)) ≤
        ((n : ℝ) ^ h)⁻¹ *
          ((1 + c * E / (n : ℝ) / (h : ℝ)) ^ h)⁻¹ := by
            simpa [hexpArg] using hmult
    _ = (((n : ℝ) + a) ^ h)⁻¹ := hEq
    _ = (((n : ℝ) + c * E / (h : ℝ)) ^ h)⁻¹ := by rfl

/-- The Gaussian time sum has the Green power decay uniformly in its cutoff. -/
private theorem gaussian_time_sum_green_bound {h L : ℕ} (hh : 2 ≤ h) {c E : ℝ}
    (hc : 0 < c) (hE : 0 ≤ E) :
    (∑ n ∈ Finset.range L,
      (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
        Real.exp (-c * E / ((n + 1 : ℕ) : ℝ))) ≤
      2 * (1 + (h : ℝ) / c) ^ (h - 1) / (1 + E) ^ (h - 1) := by
  let K : ℝ := (h : ℝ) / c
  have hKpos : 0 < K := by dsimp [K]; positivity
  by_cases hsmall : E < K
  · have hterm (n : ℕ) :
        (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-c * E / ((n + 1 : ℕ) : ℝ)) ≤
          (((n : ℝ) + 1) ^ 2)⁻¹ := by
      have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      have hexp : Real.exp (-c * E / ((n + 1 : ℕ) : ℝ)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hce : 0 ≤ c * E := mul_nonneg hc.le hE
        have hneg : -c * E ≤ 0 := by nlinarith only [hce]
        exact div_nonpos_of_nonpos_of_nonneg hneg hnpos.le
      have heq : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have hpow : (((n : ℝ) + 1) ^ 2) ≤ (((n + 1 : ℕ) : ℝ) ^ h) := by
        rw [heq]
        exact pow_le_pow_right₀
          (by exact_mod_cast (show 1 ≤ n + 1 by omega)) hh
      have hinv : (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ ≤ (((n : ℝ) + 1) ^ 2)⁻¹ :=
        inv_le_inv₀ (by positivity) (by positivity) |>.2 hpow
      calc
        _ ≤ (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ :=
          mul_le_of_le_one_right (by positivity) hexp
        _ = (((n : ℝ) + 1) ^ h)⁻¹ := by rw [heq]
        _ ≤ _ := by simpa only [heq] using hinv
    have hsum := Finset.sum_le_sum (s := Finset.range L) (fun n _ => hterm n)
    have hcoarse :
        (∑ n ∈ Finset.range L,
          (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-c * E / ((n + 1 : ℕ) : ℝ))) ≤ 2 := by
      calc
        _ ≤ ∑ n ∈ Finset.range L, (((n : ℝ) + 1) ^ 2)⁻¹ := hsum
        _ ≤ 2 := by
          simpa [one_div, inv_pow] using ccr25_time_inverse_square_sum_le_two L
    have hpowK : (1 + E) ^ (h - 1) ≤ (1 + K) ^ (h - 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) (h - 1)
    have hratio :
        1 ≤ (1 + K) ^ (h - 1) / (1 + E) ^ (h - 1) := by
      rw [one_le_div (by positivity)]
      exact hpowK
    calc
      _ ≤ 2 := hcoarse
      _ ≤ 2 * ((1 + K) ^ (h - 1) / (1 + E) ^ (h - 1)) := by nlinarith only [hratio]
      _ = _ := by dsimp [K]; ring

  · have hlarge : K ≤ E := le_of_not_gt hsmall
    let a : ℝ := c * E / (h : ℝ)
    have hhpos : 0 < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
    have hcE' : (h : ℝ) ≤ E * c := (div_le_iff₀ hc).mp (by simpa [K] using hlarge)
    have hcE : (h : ℝ) ≤ c * E := by nlinarith only [hcE']
    have ha : 1 ≤ a := by
      dsimp [a]
      exact (le_div_iff₀ hhpos).2 (by simpa using hcE)
    have hsumTerms :
        (∑ n ∈ Finset.range L,
          (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-c * E / ((n + 1 : ℕ) : ℝ))) ≤
          2 / (1 + a) ^ (h - 1) := by
      calc
        _ ≤ ∑ n ∈ Finset.range L,
            ((((n + 1 : ℕ) : ℝ) + c * E / (h : ℝ)) ^ h)⁻¹ := by
              apply Finset.sum_le_sum
              intro n hn
              exact gaussian_time_term_le_shifted_inverse
                (by omega) (n + 1) (by omega) hc hE
        _ = ∑ n ∈ Finset.range L, ((a + (n : ℝ) + 1) ^ h)⁻¹ := by
              apply Finset.sum_congr rfl
              intro n hn
              have heq :
                  ((n + 1 : ℕ) : ℝ) + c * E / (h : ℝ) =
                    a + (n : ℝ) + 1 := by
                dsimp [a]
                push_cast
                ring
              rw [heq]
        _ ≤ 2 / (1 + a) ^ (h - 1) := shifted_inverse_power_sum_bound hh ha
    have hKa : K * a = E := by
      dsimp [K, a]
      field_simp [ne_of_gt hc, ne_of_gt hhpos]
    have hscale : 1 + E ≤ (1 + K) * (1 + a) := by
      have hKn : 0 ≤ K := hKpos.le
      have han : 0 ≤ a := by positivity
      calc
        1 + E ≤ 1 + E + K + a := by linarith
        _ = (1 + K) * (1 + a) := by rw [← hKa]; ring
    have hpow :
        (1 + E) ^ (h - 1) ≤
          (1 + K) ^ (h - 1) * (1 + a) ^ (h - 1) := by
      calc
        _ ≤ ((1 + K) * (1 + a)) ^ (h - 1) :=
          pow_le_pow_left₀ (by positivity) hscale (h - 1)
        _ = _ := mul_pow _ _ _
    have hscaleInv :
        1 / (1 + a) ^ (h - 1) ≤ (1 + K) ^ (h - 1) / (1 + E) ^ (h - 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simpa only [one_mul, mul_one] using hpow
    calc
      _ ≤ 2 / (1 + a) ^ (h - 1) := hsumTerms
      _ ≤ 2 * ((1 + K) ^ (h - 1) / (1 + E) ^ (h - 1)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hscaleInv (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by dsimp [K]; ring

/-- Retain half of the Gaussian exponent at the macroscopic cutoff. -/
private theorem gaussian_time_sum_green_gaussian_bound {h L : ℕ} (hh : 2 ≤ h)
    {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E) :
    (∑ n ∈ Finset.range L,
      (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
        Real.exp (-c * E / ((n + 1 : ℕ) : ℝ))) ≤
      Real.exp (-c * E / (2 * (L : ℝ))) *
        (2 * (1 + 2 * (h : ℝ) / c) ^ (h - 1) / (1 + E) ^ (h - 1)) := by
  let d : ℝ := c / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdouble : 2 * d = c := by dsimp [d]; ring
  have hterm (n : ℕ) (hn : n ∈ Finset.range L) :
      (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
          Real.exp (-c * E / ((n + 1 : ℕ) : ℝ)) ≤
        Real.exp (-c * E / (2 * (L : ℝ))) *
          ((((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-d * E / ((n + 1 : ℕ) : ℝ))) := by
    let m : ℝ := ((n + 1 : ℕ) : ℝ)
    have hmpos : 0 < m := by dsimp [m]; positivity
    have hnLnat : n + 1 ≤ L := Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    have hmL : m ≤ (L : ℝ) := by dsimp [m]; exact_mod_cast hnLnat
    have hinvL : (L : ℝ)⁻¹ ≤ m⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hmpos hmL
    have hquot : d * E / (L : ℝ) ≤ d * E / m := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinvL (mul_nonneg hd.le hE)
    have hhalf :
        Real.exp (-d * E / m) ≤ Real.exp (-d * E / (L : ℝ)) :=
      Real.exp_le_exp.mpr (by
        have hneg := neg_le_neg hquot
        dsimp [m]
        convert hneg using 1 <;> ring)
    have hsplit :
        Real.exp (-c * E / m) =
          Real.exp (-d * E / m) * Real.exp (-d * E / m) := by
      rw [← Real.exp_add]
      congr 1
      rw [← hdouble]
      ring
    have hprod := mul_le_mul_of_nonneg_right hhalf (Real.exp_nonneg (-d * E / m))
    have hInv : 0 ≤ (m ^ h)⁻¹ := inv_nonneg.mpr (pow_nonneg hmpos.le h)
    calc
      _ = (m ^ h)⁻¹ *
            (Real.exp (-d * E / m) * Real.exp (-d * E / m)) := by rw [hsplit]
      _ ≤ (m ^ h)⁻¹ *
            (Real.exp (-d * E / (L : ℝ)) * Real.exp (-d * E / m)) :=
        mul_le_mul_of_nonneg_left hprod hInv
      _ = Real.exp (-c * E / (2 * (L : ℝ))) *
            ((m ^ h)⁻¹ * Real.exp (-d * E / m)) := by
        rw [← hdouble]
        ring
  have hsumTerm := Finset.sum_le_sum fun n hn => hterm n hn
  calc
    _ ≤ ∑ n ∈ Finset.range L,
        Real.exp (-c * E / (2 * (L : ℝ))) *
          ((((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-d * E / ((n + 1 : ℕ) : ℝ))) := hsumTerm
    _ = Real.exp (-c * E / (2 * (L : ℝ))) *
        ∑ n ∈ Finset.range L,
          (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-d * E / ((n + 1 : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-c * E / (2 * (L : ℝ))) *
        (2 * (1 + (h : ℝ) / d) ^ (h - 1) / (1 + E) ^ (h - 1)) :=
      mul_le_mul_of_nonneg_left (gaussian_time_sum_green_bound hh hd hE)
        (Real.exp_nonneg _)
    _ = _ := by dsimp [d]; ring


/-- The cutoff Gaussian bound for the free replica Green kernel, preserving
half of the walk heat-kernel exponent for the exponential weight conjugation in
CCR25 Proposition 4.23. -/
theorem hattedFreeReplicaKernel_gaussian_green_bound {h : ℕ} (hh : 2 ≤ h)
    :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ L : ℕ, ∀ I J : ReplicaPartition h, ∀ z x : LatticeConfiguration h,
        hattedFreeReplicaKernel L I J z x ≤
          2 * C ^ h * (1 + 2 * (h : ℝ) / c) ^ (h - 1) *
            Real.exp (-c * replicaDistanceEnergy z x / (2 * (L : ℝ))) *
            replicaGreenKernel z x := by
  obtain ⟨C, c, hC, hc, hfree⟩ := freeReplicaKernel_gaussian_bound
  refine ⟨C, c, hC, hc, ?_⟩
  intro L I J z x
  have hE : 0 ≤ replicaDistanceEnergy z x := replicaDistanceEnergy_nonneg z x
  have hsum :
      (∑ n ∈ Finset.range L,
        (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
          Real.exp (-c * replicaDistanceEnergy z x / ((n + 1 : ℕ) : ℝ))) ≤
        Real.exp (-c * replicaDistanceEnergy z x / (2 * (L : ℝ))) *
          (2 * (1 + 2 * (h : ℝ) / c) ^ (h - 1) /
            (1 + replicaDistanceEnergy z x) ^ (h - 1)) :=
    gaussian_time_sum_green_gaussian_bound hh hc hE
  have hterm (n : ℕ) (hn : n ∈ Finset.range L) :
      freeReplicaKernel (n + 1) I J z x ≤
        C ^ h * ((((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
          Real.exp (-c * replicaDistanceEnergy z x / ((n + 1 : ℕ) : ℝ))) := by
    have hbound := hfree (n + 1) (by omega) I J z x
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound
  have hkernel :
      (∑ n ∈ Finset.range L, freeReplicaKernel (n + 1) I J z x) ≤
        C ^ h * (∑ n ∈ Finset.range L,
          (((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-c * replicaDistanceEnergy z x / ((n + 1 : ℕ) : ℝ))) := by
    calc
      _ ≤ ∑ n ∈ Finset.range L,
          C ^ h * ((((n + 1 : ℕ) : ℝ) ^ h)⁻¹ *
            Real.exp (-c * replicaDistanceEnergy z x / ((n + 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun n hn => hterm n hn
      _ = _ := by rw [← Finset.mul_sum]
  have hgreen :
      (1 + replicaDistanceEnergy z x) ^ (-((h : ℝ) - 1)) =
        1 / (1 + replicaDistanceEnergy z x) ^ (h - 1) := by
    have hp : ((h : ℝ) - 1) = ((h - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ h)]
      norm_num
    rw [Real.rpow_neg (by positivity), hp, Real.rpow_natCast]
    simp only [one_div]
  unfold hattedFreeReplicaKernel
  calc
    _ ≤ C ^ h *
        (Real.exp (-c * replicaDistanceEnergy z x / (2 * (L : ℝ))) *
          (2 * (1 + 2 * (h : ℝ) / c) ^ (h - 1) /
            (1 + replicaDistanceEnergy z x) ^ (h - 1))) :=
      hkernel.trans (mul_le_mul_of_nonneg_left hsum (pow_nonneg hC h))
    _ = 2 * C ^ h * (1 + 2 * (h : ℝ) / c) ^ (h - 1) *
          Real.exp (-c * replicaDistanceEnergy z x / (2 * (L : ℝ))) *
          replicaGreenKernel z x := by
      rw [replicaGreenKernel, hgreen]
      ring

end Critical2DKPZ.MomentBounds

end
