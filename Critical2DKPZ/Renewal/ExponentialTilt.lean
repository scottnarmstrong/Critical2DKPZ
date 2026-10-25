/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Subcritical
public import Critical2DKPZ.Renewal.Normalization
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Exponential tilting and renewal-clock bounds

Tilting the step weights by `exp (-a r)` tilts their convolution at time `n` by
`exp (-a n)`, yielding finite-horizon resolvent bounds and exponential renewal-clock estimates. -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- Exponentially damp the positive renewal steps. -/
def exponentialTilt (w : ℕ → ℝ) (a : ℝ) (r : ℕ) : ℝ := Real.exp (-a * r) * w r

/-- The exponentially tilted kernel is nonnegative. -/
theorem exponentialTilt_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (a : ℝ) (r : ℕ) :
    0 ≤ exponentialTilt w a r := mul_nonneg (Real.exp_nonneg _) (hw r)

/-- Exponential tilting commutes with convolution powers up to the terminal exponential factor. -/
theorem convolutionPower_exponentialTilt (w : ℕ → ℝ) (a : ℝ) (k n : ℕ) :
    convolutionPower (exponentialTilt w a) k n =
      Real.exp (-a * n) * convolutionPower w k n := by
  induction k generalizing n with
  | zero =>
    by_cases hn : n = 0
    · subst n; simp only [convolutionPower_zero, ↓reduceIte, Nat.cast_zero, mul_zero,
        Real.exp_zero, mul_one]
    · simp only [convolutionPower_zero, ite_eq_right hn, mul_zero]
  | succ k ih =>
    rw [convolutionPower_succ, convolutionPower_succ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [ih]
    have he : Real.exp (-a * r) * Real.exp (-a * ((n - r : ℕ) : ℝ)) = Real.exp (-a * n) := by
      rw [← Real.exp_add, Nat.cast_sub (Finset.mem_Icc.mp hr).2]
      congr 1
      ring
    change (Real.exp (-a * r) * w r) *
      (Real.exp (-a * ((n - r : ℕ) : ℝ)) * convolutionPower w k (n - r)) = _
    calc
      _ = (Real.exp (-a * r) * Real.exp (-a * ((n - r : ℕ) : ℝ))) *
          (w r * convolutionPower w k (n - r)) := by ring
      _ = _ := by rw [he]

/-- Exponential tilting multiplies renewal mass by its terminal exponential factor. -/
theorem renewalMass_exponentialTilt (w : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    renewalMass (exponentialTilt w a) n = Real.exp (-a * n) * renewalMass w n := by
  simp only [renewalMass, convolutionPower_exponentialTilt, Finset.mul_sum]

/-- Renewal mass is recovered from its exponential tilt by undoing the damping factor. -/
theorem renewalMass_eq_exp_mul_tilt (w : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    renewalMass w n = Real.exp (a * n) * renewalMass (exponentialTilt w a) n := by
  rw [renewalMass_exponentialTilt, ← mul_assoc, ← Real.exp_add]
  simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]

/-- Removing the tilt from a finite horizon costs at most `exp (a n)`. -/
theorem renewalFunction_le_exp_mul_tilt {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    renewalFunction w n ≤ Real.exp (a * n) * renewalFunction (exponentialTilt w a) n := by
  change 1 + (∑ m ∈ Finset.Icc 1 n, renewalMass w m) ≤ _
  rw [renewalFunction, mul_add, mul_one, Finset.mul_sum]
  apply add_le_add (Real.one_le_exp_iff.mpr (mul_nonneg ha (Nat.cast_nonneg n)))
  apply Finset.sum_le_sum
  intro m hm
  rw [renewalMass_eq_exp_mul_tilt w a m]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2) ha))
    (renewalMass_nonneg (exponentialTilt_nonneg hw a) m)

/-- A discounted subcritical kernel controls the original free renewal function. -/
theorem renewalFunction_le_exp_div {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (hsub : cutoffMass (exponentialTilt w a) n < 1) :
    renewalFunction w n ≤ Real.exp (a * n) / (1 - cutoffMass (exponentialTilt w a) n) := by
  calc
    renewalFunction w n ≤ Real.exp (a * n) * renewalFunction (exponentialTilt w a) n :=
      renewalFunction_le_exp_mul_tilt hw ha n
    _ ≤ Real.exp (a * n) * (1 / (1 - cutoffMass (exponentialTilt w a) n)) :=
      mul_le_mul_of_nonneg_left
        (renewalFunction_le_geometric (exponentialTilt_nonneg hw a) n hsub) (Real.exp_nonneg _)
    _ = _ := by rw [mul_one_div]

/-- The cumulative weight of exactly `k` renewals before time `n`. -/
def cumulativePower (w : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), convolutionPower w k m

/-- The cumulative zeroth convolution power equals one. -/
@[simp] theorem cumulativePower_zero (w : ℕ → ℝ) (n : ℕ) : cumulativePower w 0 n = 1 := by
  simp only [cumulativePower, convolutionPower_zero, Finset.sum_ite_eq',
    Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte]

/-- The cumulative convolution power is nonnegative. -/
theorem cumulativePower_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (k n : ℕ) :
    0 ≤ cumulativePower w k n := Finset.sum_nonneg fun m _ => convolutionPower_nonneg hw k m

/-- A convolution power vanishes cumulatively when too many positive steps are required. -/
theorem cumulativePower_eq_zero (w : ℕ → ℝ) {k n : ℕ} (h : n < k) :
    cumulativePower w k n = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  exact convolutionPower_eq_zero w (by have := Finset.mem_range.mp hm; omega)

/-- Summing cumulative convolution powers over the collision count gives the renewal function. -/
theorem sum_cumulativePower (w : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), cumulativePower w k n = renewalFunction w n := by
  simp_rw [cumulativePower]
  rw [Finset.sum_comm]
  calc
    _ = ∑ m ∈ Finset.range (n + 1), renewalMass w m :=
      Finset.sum_congr rfl fun m hm => sum_convolutionPower_eq_renewalMass w
        (by have := Finset.mem_range.mp hm; omega)
    _ = _ := sum_renewalMass_range w n

/-- The infinite collision-count series is in fact finitely supported at each finite horizon. -/
theorem hasSum_cumulativePower (w : ℕ → ℝ) (n : ℕ) :
    HasSum (fun k => cumulativePower w k n) (renewalFunction w n) := by
  rw [← sum_cumulativePower]
  exact hasSum_sum_of_ne_finset_zero (fun k hk => cumulativePower_eq_zero w
    (by simp only [Finset.mem_range] at hk; omega))

/-- The renewal mass agrees with its infinite convolution-power expansion. -/
theorem hasSum_convolutionPower (w : ℕ → ℝ) (n : ℕ) :
    HasSum (fun k => convolutionPower w k n) (renewalMass w n) :=
  hasSum_sum_of_ne_finset_zero (fun k hk => convolutionPower_eq_zero w
    (by simp only [Finset.mem_range] at hk; omega))

private theorem sum_convolution_range (w f : ℕ → ℝ) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), ∑ r ∈ Finset.Icc 1 m, w r * f (m - r)) =
      ∑ r ∈ Finset.Icc 1 n, w r * ∑ s ∈ Finset.range (n - r + 1), f s := by
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 1)]
  simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, zero_add]
  simp_rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.sum_Ico_Ico_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.add_sub_cancel_left]
  have hsub : n + 1 - r = n - r + 1 := by have := Finset.mem_Ico.mp hr; omega
  rw [hsub]

/-- The next cumulative convolution power is obtained by convolution with the step kernel. -/
theorem cumulativePower_succ (w : ℕ → ℝ) (k n : ℕ) :
    cumulativePower w (k + 1) n =
      ∑ r ∈ Finset.Icc 1 n, w r * cumulativePower w k (n - r) := by
  exact sum_convolution_range w (convolutionPower w k) n

/-- Forgetting the constraint on the total elapsed time gives a power of the cutoff mass. -/
theorem cumulativePower_le_pow {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (k n : ℕ) :
    cumulativePower w k n ≤ cutoffMass w n ^ k := by
  induction k generalizing n with
  | zero =>
    simp only [cumulativePower, convolutionPower_zero, Finset.sum_ite_eq',
      Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte, pow_zero, le_refl]
  | succ k ih =>
    rw [cumulativePower_succ, pow_succ, cutoffMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hmono : cutoffMass w (n - r) ≤ cutoffMass w n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.sub_le n r))
        (fun j _ _ => hw j)
    have hmass : 0 ≤ cutoffMass w (n - r) := Finset.sum_nonneg fun j _ => hw j
    calc
      w r * cumulativePower w k (n - r) ≤ w r * cutoffMass w (n - r) ^ k :=
        mul_le_mul_of_nonneg_left (ih (n - r)) (hw r)
      _ ≤ w r * cutoffMass w n ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmass hmono k) (hw r)
      _ = _ := mul_comm _ _

/-- Exponential Markov estimate for the renewal clock, in convolution form. -/
theorem cumulativePower_le_exp_mul_pow {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {a : ℝ} (ha : 0 ≤ a) (k n : ℕ) :
    cumulativePower w k n ≤ Real.exp (a * n) * cutoffMass (exponentialTilt w a) n ^ k := by
  have htilt : cumulativePower w k n ≤
      Real.exp (a * n) * cumulativePower (exponentialTilt w a) k n := by
    rw [cumulativePower, cumulativePower, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hid : convolutionPower w k m =
        Real.exp (a * m) * convolutionPower (exponentialTilt w a) k m := by
      rw [convolutionPower_exponentialTilt, ← mul_assoc, ← Real.exp_add]
      simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
    rw [hid]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by
        have := Finset.mem_range.mp hm; omega)) ha))
      (convolutionPower_nonneg (exponentialTilt_nonneg hw a) k m)
  exact htilt.trans (mul_le_mul_of_nonneg_left
    (cumulativePower_le_pow (exponentialTilt_nonneg hw a) k n) (Real.exp_nonneg _))

end Critical2DKPZ.Renewal

end
