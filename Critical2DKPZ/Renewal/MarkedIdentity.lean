/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.FormalSeries
public import Critical2DKPZ.Renewal.ParameterDerivative
import Mathlib.Tactic.LinearCombination

/-!
# Marked renewal factors and the squared resolvent

There are exactly `k+1` ways to split a word of `k` positive increments into two
renewal factors. The finite coefficient identity is proved from the renewal equation,
retaining the time-zero atom.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- Summing convolution powers weighted by one plus their order gives marked renewal mass. -/
theorem sum_markedPower_eq (w : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) * convolutionPower w k m =
      markedRenewalMass w m := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro k hk hnot
  rw [convolutionPower_eq_zero w (by simp only [Finset.mem_range] at hnot; omega), mul_zero]

/-- The marked renewal equation has the ordinary renewal mass as its forcing term. -/
theorem markedRenewalMass_succ (w : ℕ → ℝ) (n : ℕ) :
    markedRenewalMass w (n + 1) = renewalMass w (n + 1) +
      ∑ r ∈ Finset.Icc 1 (n + 1), w r * markedRenewalMass w (n + 1 - r) := by
  have hsplit : markedRenewalMass w (n + 1) = renewalMass w (n + 1) +
      ∑ k ∈ Finset.range (n + 1 + 1), (k : ℝ) * convolutionPower w k (n + 1) := by
    unfold markedRenewalMass renewalMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsplit, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one, convolutionPower_succ,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hmr : n + 1 - r ≤ n := by have := (Finset.mem_Icc.mp hr).1; omega
  rw [← sum_markedPower_eq w hmr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Marked renewal mass at time zero is one. -/
@[simp] theorem markedRenewalMass_zero (w : ℕ → ℝ) : markedRenewalMass w 0 = 1 := by
  simp only [markedRenewalMass, Finset.sum_range_one, Nat.cast_zero, zero_add,
    convolutionPower_zero, ↓reduceIte, mul_one]

/-- The formal series with one renewal factor marked. -/
def markedRenewalSeries (w : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk (markedRenewalMass w)

/-- The marked renewal series satisfies its renewal recursion with the ordinary renewal series as source. -/
theorem markedRenewalSeries_eq (w : ℕ → ℝ) :
    markedRenewalSeries w = renewalSeries w + stepSeries w * markedRenewalSeries w := by
  ext n
  rw [map_add, coeff_mul_range]
  simp only [markedRenewalSeries, renewalSeries, stepSeries, PowerSeries.coeff_mk]
  cases n with
  | zero => simp only [markedRenewalMass_zero, renewalMass_zero, Nat.zero_add,
      Finset.sum_range_one, ↓reduceIte, zero_mul, add_zero]
  | succ n =>
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 1 + 1)]
    simp only [↓reduceIte, zero_mul, zero_add, Finset.Ico_add_one_right_eq_Icc]
    rw [markedRenewalMass_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)]

/-- The marked renewal series equals the square of the renewal series. -/
theorem markedRenewalSeries_eq_square (w : ℕ → ℝ) :
    markedRenewalSeries w = renewalSeries w * renewalSeries w := by
  have h := markedRenewalSeries_eq w
  have hm : (1 - stepSeries w) * markedRenewalSeries w = renewalSeries w := by
    linear_combination h
  calc
    _ = ((1 - stepSeries w) * renewalSeries w) * markedRenewalSeries w := by
      rw [stepSeries_mul_renewalSeries, one_mul]
    _ = renewalSeries w * ((1 - stepSeries w) * markedRenewalSeries w) := by ring
    _ = _ := by rw [hm]

/-- The squared resolvent counts the `k+1` possible marked renewal factors. -/
theorem renewalSquare_eq_markedRenewalMass (w : ℕ → ℝ) (n : ℕ) :
    renewalSquare w n = markedRenewalMass w n := by
  rw [← coeff_renewalSeries_sq, ← markedRenewalSeries_eq_square, markedRenewalSeries,
    PowerSeries.coeff_mk]

/-- Summing marked renewal mass over a finite time range gives the marked cumulative renewal function. -/
theorem sum_markedRenewalMass_range (w : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), markedRenewalMass w m = markedRenewalFunction w n := by
  calc
    _ = ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((k : ℝ) + 1) * convolutionPower w k m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (sum_markedPower_eq w (by have := Finset.mem_range.mp hm; omega)).symm
    _ = ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) *
        ∑ m ∈ Finset.range (n + 1), convolutionPower w k m := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := rfl

end Critical2DKPZ.Renewal

end
