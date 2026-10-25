/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Overshoot

/-! # A renewal lower bound with distinct time horizon and increment cutoff

CSZ25 Lemma 5.5 applies the first-moment clock estimate with increments truncated at `L`
and renewal horizon `L/2`. This form keeps those two cutoffs independent.
-/

@[expose] public noncomputable section

open Critical2DKPZ.Renewal

namespace Critical2DKPZ.MomentBounds

/-- The geometric comparison error for a renewal horizon below the increment cutoff. -/
theorem geometric_sub_renewalFunction_le_of_le {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {m n : ℕ} (hmn : m ≤ n) (hsub : cutoffMass w n < 1) :
    1 / (1 - cutoffMass w n) - renewalFunction w m ≤
      cutoffFirstMoment w n / ((m + 1 : ℝ) * (1 - cutoffMass w n) ^ 2) := by
  let W := cutoffMass w n
  let M := cutoffFirstMoment w n
  have hW : 0 ≤ W := Finset.sum_nonneg fun r _ => hw r
  have hnorm : ‖W‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hW]; exact hsub
  have hden : 1 - W ≠ 0 := (sub_pos.mpr hsub).ne'
  have hgeo : HasSum (fun k : ℕ => W ^ k) (1 / (1 - W)) := by
    simpa only [one_div] using hasSum_geometric_of_lt_one hW hsub
  have hdiff := hgeo.sub (hasSum_cumulativePower w m)
  have hshift : HasSum (fun k => W ^ (k + 1) - cumulativePower w (k + 1) m)
      (1 / (1 - W) - renewalFunction w m) := by
    have h := (hasSum_nat_add_iff' 1).mpr hdiff
    simpa only [Finset.sum_range_one, pow_zero, cumulativePower_zero, sub_self, sub_zero] using h
  have hseries : HasSum (fun k : ℕ => (k + 1 : ℝ) * W ^ k) (1 / (1 - W) ^ 2) := by
    simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
      hasSum_choose_mul_geometric_of_norm_lt_one 1 hnorm
  have hle : (m + 1 : ℝ) * (1 / (1 - W) - renewalFunction w m) ≤ M * (1 / (1 - W) ^ 2) := by
    apply hasSum_le _ (hshift.mul_left (m + 1 : ℝ)) (hseries.mul_left M)
    intro k
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_assoc, mul_left_comm] using
      cutoff_overshoot_le_firstMoment hw (k + 1) hmn
  apply (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < m + 1)
    (sq_pos_of_pos (sub_pos.mpr hsub)))).mpr
  calc
    (1 / (1 - W) - renewalFunction w m) * ((m + 1 : ℝ) * (1 - W) ^ 2) =
        ((m + 1 : ℝ) * (1 / (1 - W) - renewalFunction w m)) * (1 - W) ^ 2 := by ring
    _ ≤ (M * (1 / (1 - W) ^ 2)) * (1 - W) ^ 2 :=
      mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = M := by field_simp [hden]

/-- If the first-moment error is at most half the geometric sum, the renewal function
retains at least half that sum. -/
theorem half_geometric_le_renewalFunction {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {m n : ℕ} (hmn : m ≤ n) (hsub : cutoffMass w n < 1)
    (hsmall : 2 * cutoffFirstMoment w n ≤ (m + 1 : ℝ) * (1 - cutoffMass w n)) :
    1 / (2 * (1 - cutoffMass w n)) ≤ renewalFunction w m := by
  have herr := geometric_sub_renewalFunction_le_of_le hw hmn hsub
  have hd : 0 < 1 - cutoffMass w n := sub_pos.2 hsub
  have hm : (0 : ℝ) < m + 1 := by positivity
  have he : cutoffFirstMoment w n / ((m + 1 : ℝ) * (1 - cutoffMass w n) ^ 2) ≤
      1 / (2 * (1 - cutoffMass w n)) := by
    apply (div_le_div_iff₀ (mul_pos hm (sq_pos_of_pos hd)) (mul_pos (by norm_num) hd)).2
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hd.le]
  have hi : 1 / (1 - cutoffMass w n) = 2 * (1 / (2 * (1 - cutoffMass w n))) := by
    field_simp
  linarith only [herr, he, hi]

end Critical2DKPZ.MomentBounds
