/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Renewal masses with strictly positive integer increments

Only finitely many convolution powers contribute at each fixed time; the zeroth power
is a unit atom at zero. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Renewal

/-- The `k`-fold convolution with strictly positive increments, ignoring the step kernel value at zero. -/
def convolutionPower (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ r ∈ Finset.Icc 1 n, w r * convolutionPower w k (n - r)

/-- The zeroth convolution power is the point mass at zero. -/
@[simp] theorem convolutionPower_zero (w : ℕ → ℝ) (n : ℕ) :
    convolutionPower w 0 n = if n = 0 then 1 else 0 := rfl

/-- The next convolution power is obtained by convolution with the positive-time step kernel. -/
@[simp] theorem convolutionPower_succ (w : ℕ → ℝ) (k n : ℕ) :
    convolutionPower w (k + 1) n =
      ∑ r ∈ Finset.Icc 1 n, w r * convolutionPower w k (n - r) := rfl

/-- A sum of `k` positive increments cannot equal a time smaller than `k`. -/
theorem convolutionPower_eq_zero (w : ℕ → ℝ) {k n : ℕ} (h : n < k) :
    convolutionPower w k n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [convolutionPower_succ]
    apply Finset.sum_eq_zero
    intro r hr
    rw [ih (by have := Finset.mem_Icc.mp hr; omega), mul_zero]

/-- A convolution power at time zero is one exactly at order zero. -/
@[simp] theorem convolutionPower_at_zero (w : ℕ → ℝ) (k : ℕ) :
    convolutionPower w k 0 = if k = 0 then 1 else 0 := by
  cases k <;> simp only [convolutionPower, ↓reduceIte, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
    Finset.sum_empty, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]

/-- Weighted renewal mass, including the unit mass at time zero. -/
def renewalMass (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), convolutionPower w k n

/-- Renewal mass at time zero equals one. -/
@[simp] theorem renewalMass_zero (w : ℕ → ℝ) : renewalMass w 0 = 1 := by
  simp only [renewalMass, Nat.zero_add, Finset.sum_range_one, convolutionPower_zero, ↓reduceIte]

/-- Extending the power sum adds only zero terms. -/
theorem sum_convolutionPower_eq_renewalMass (w : ℕ → ℝ) {m n : ℕ} (h : m ≤ n) :
    ∑ k ∈ Finset.range (n + 1), convolutionPower w k m = renewalMass w m := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
  intro k hk hnot
  exact convolutionPower_eq_zero w (by simp only [Finset.mem_range] at hnot; omega)

/-- The usual renewal equation. -/
theorem renewalMass_succ (w : ℕ → ℝ) (n : ℕ) :
    renewalMass w (n + 1) =
      ∑ r ∈ Finset.Icc 1 (n + 1), w r * renewalMass w (n + 1 - r) := by
  change (∑ k ∈ Finset.range (n + 1 + 1), convolutionPower w k (n + 1)) = _
  rw [Finset.sum_range_succ']
  simp only [convolutionPower_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    add_zero, convolutionPower_succ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum, sum_convolutionPower_eq_renewalMass w
    (by have := (Finset.mem_Icc.mp hr).1; omega)]

/-- The free renewal function, the deterministic expression for the free second moment. -/
def renewalFunction (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + ∑ m ∈ Finset.Icc 1 n, renewalMass w m

/-- The cumulative renewal function at time zero equals one. -/
@[simp] theorem renewalFunction_zero (w : ℕ → ℝ) : renewalFunction w 0 = 1 := by
  simp only [renewalFunction, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
    Finset.sum_empty, add_zero]

/-- The renewal convolution power is nonnegative. -/
theorem convolutionPower_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (k n : ℕ) :
    0 ≤ convolutionPower w k n := by
  induction k generalizing n with
  | zero => simp only [convolutionPower_zero]; split_ifs <;> positivity
  | succ k ih =>
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hw r) (ih (n - r))

/-- The renewal mass is nonnegative. -/
theorem renewalMass_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ) :
    0 ≤ renewalMass w n :=
  Finset.sum_nonneg fun k _ => convolutionPower_nonneg hw k n

/-- The cumulative renewal function is at least one. -/
theorem one_le_renewalFunction {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ) :
    1 ≤ renewalFunction w n :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => renewalMass_nonneg hw m)

/-- The cumulative renewal function increases with time for a nonnegative kernel. -/
theorem renewalFunction_mono_time {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) :
    Monotone (renewalFunction w) := by
  intro m n hmn
  apply add_le_add le_rfl
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hmn) (fun r _ _ => renewalMass_nonneg hw r)

/-- Convolution powers preserve pointwise order between nonnegative kernels. -/
theorem convolutionPower_mono {w v : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    (hwv : ∀ r, w r ≤ v r) (k n : ℕ) : convolutionPower w k n ≤ convolutionPower v k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul (hwv r) (ih (n - r)) (convolutionPower_nonneg hw k _) ((hw r).trans (hwv r))

/-- Renewal mass preserves pointwise order between nonnegative kernels. -/
theorem renewalMass_mono {w v : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (hwv : ∀ r, w r ≤ v r)
    (n : ℕ) : renewalMass w n ≤ renewalMass v n :=
  Finset.sum_le_sum fun k _ => convolutionPower_mono hw hwv k n

/-- The cumulative renewal function preserves pointwise order between nonnegative kernels. -/
theorem renewalFunction_mono {w v : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (hwv : ∀ r, w r ≤ v r)
    (n : ℕ) : renewalFunction w n ≤ renewalFunction v n :=
  add_le_add le_rfl (Finset.sum_le_sum fun m _ => renewalMass_mono hw hwv m)

/-- Scaling every step weight scales the `k`-fold convolution by the `k`-th power. -/
theorem convolutionPower_smul (w : ℕ → ℝ) (a : ℝ) (k n : ℕ) :
    convolutionPower (fun r => a * w r) k n = a ^ k * convolutionPower w k n := by
  induction k generalizing n with
  | zero => simp only [convolutionPower_zero, pow_zero, one_mul]
  | succ k ih =>
    simp only [convolutionPower_succ, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_succ]
    ring

/-- Values of a convolution power up to time `n` only use positive steps up to `n`. -/
theorem convolutionPower_congr {w v : ℕ → ℝ} (k n : ℕ)
    (h : ∀ r, 1 ≤ r → r ≤ n → w r = v r) :
    convolutionPower w k n = convolutionPower v k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨hr1, hrn⟩ := Finset.mem_Icc.mp hr
    rw [h r hr1 hrn, ih (n - r) (fun j hj1 hjn => h j hj1 (hjn.trans (Nat.sub_le _ _)))]



/-- The free renewal function is the cumulative mass including the time-zero atom. -/
theorem sum_renewalMass_range (w : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), renewalMass w m = renewalFunction w n := by
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 1), renewalMass_zero,
    Finset.Ico_add_one_right_eq_Icc]
  rfl

/-- The free renewal function satisfies the first-collision equation. -/
theorem renewalFunction_eq (w : ℕ → ℝ) (n : ℕ) :
    renewalFunction w n =
      1 + ∑ r ∈ Finset.Icc 1 n, w r * renewalFunction w (n - r) := by
  change 1 + (∑ m ∈ Finset.Icc 1 n, renewalMass w m) = _
  congr 1
  have hm (m : ℕ) (hm : m ∈ Finset.Icc 1 n) :
      renewalMass w m = ∑ r ∈ Finset.Icc 1 m, w r * renewalMass w (m - r) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := m) (by
      have := (Finset.mem_Icc.mp hm).1; omega)
    exact renewalMass_succ w j
  rw [Finset.sum_congr rfl hm]
  simp_rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.sum_Ico_Ico_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.add_sub_cancel_left]
  have hsub : n + 1 - r = n - r + 1 := by
    have := Finset.mem_Ico.mp hr; omega
  rw [hsub, sum_renewalMass_range]

/-- The renewal function is the unique solution of the first-collision recurrence. -/
theorem eq_renewalFunction_of_recurrence (w f : ℕ → ℝ)
    (hf : ∀ n, f n = 1 + ∑ r ∈ Finset.Icc 1 n, w r * f (n - r)) :
    f = renewalFunction w := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [hf n, renewalFunction_eq w n]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [ih (n - r) (by have := Finset.mem_Icc.mp hr; omega)]

end Critical2DKPZ.Renewal

end
