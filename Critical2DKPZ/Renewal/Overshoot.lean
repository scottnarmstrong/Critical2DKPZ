/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ExponentialTilt
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# First-moment control of renewal overshoot

Markov's inequality bounds the discarded compositions in the proof of Claim B.1.
The finite convolution proof avoids any interchange of non-absolutely-convergent series.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- The first moment of the unnormalized, cutoff increment weights. -/
def cutoffFirstMoment (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, (r : ℝ) * w r


private theorem cumulativePower_succ_cutoff (w : ℕ → ℝ) (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    cumulativePower w (k + 1) m =
      ∑ r ∈ Finset.Icc 1 n, w r * if r ≤ m then cumulativePower w k (m - r) else 0 := by
  rw [cumulativePower_succ]
  calc
    _ = ∑ r ∈ Finset.Icc 1 m, w r * if r ≤ m then cumulativePower w k (m - r) else 0 :=
      Finset.sum_congr rfl fun r hr => by rw [ite_eq_left (Finset.mem_Icc.mp hr).2]
    _ = _ := Finset.sum_subset (Finset.Icc_subset_Icc_right hmn) (fun r hr hnot => by
      have hrm : ¬r ≤ m := by
        have hr1 := (Finset.mem_Icc.mp hr).1
        simp only [Finset.mem_Icc, not_and] at hnot
        exact hnot hr1
      rw [ite_eq_right hrm, mul_zero])

/-- Markov's inequality for the sum of the positive increments, with an unnormalized kernel. -/
theorem cutoff_overshoot_le_firstMoment {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    (k : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (m + 1 : ℝ) * (cutoffMass w n ^ k - cumulativePower w k m) ≤
      (k : ℝ) * cutoffFirstMoment w n * cutoffMass w n ^ (k - 1) := by
  let W := cutoffMass w n
  let M := cutoffFirstMoment w n
  have hW : 0 ≤ W := Finset.sum_nonneg fun r _ => hw r
  have hM : 0 ≤ M := Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg r) (hw r)
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    have hc : cumulativePower w 0 m = 1 := by
      simp only [cumulativePower, convolutionPower_zero, Finset.sum_ite_eq',
        Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte]
    rw [hc, sub_self, mul_zero]
  | succ k ih =>
    have hterm (r : ℕ) :
        (m + 1 : ℝ) * (W ^ k - if r ≤ m then cumulativePower w k (m - r) else 0) ≤
          (k : ℝ) * M * W ^ (k - 1) + (r : ℝ) * W ^ k := by
      by_cases hrm : r ≤ m
      · rw [ite_eq_left hrm]
        have hc := cumulativePower_nonneg hw k (m - r)
        have hi := ih (Nat.le_trans (Nat.sub_le m r) hmn)
        change (↑(m - r) + 1) * (W ^ k - cumulativePower w k (m - r)) ≤
          (k : ℝ) * M * W ^ (k - 1) at hi
        rw [Nat.cast_sub hrm] at hi
        have hrc := mul_nonneg (Nat.cast_nonneg r) hc
        nlinarith only [hi, hrc]
      · rw [ite_eq_right hrm, sub_zero]
        have hmr : (m + 1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show m + 1 ≤ r by omega)
        exact (mul_le_mul_of_nonneg_right hmr (pow_nonneg hW k)).trans
          (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hM)
            (pow_nonneg hW (k - 1))))
    calc
      (m + 1 : ℝ) * (cutoffMass w n ^ (k + 1) - cumulativePower w (k + 1) m) =
          ∑ r ∈ Finset.Icc 1 n, w r * ((m + 1 : ℝ) *
            (W ^ k - if r ≤ m then cumulativePower w k (m - r) else 0)) := by
        rw [cumulativePower_succ_cutoff w k hmn, pow_succ', cutoffMass, Finset.sum_mul,
          ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp only [W, cutoffMass]
        ring
      _ ≤ ∑ r ∈ Finset.Icc 1 n, w r *
          ((k : ℝ) * M * W ^ (k - 1) + (r : ℝ) * W ^ k) :=
        Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hterm r) (hw r)
      _ = W * ((k : ℝ) * M * W ^ (k - 1)) + M * W ^ k := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · exact (Finset.sum_mul ..).symm
        · change (∑ r ∈ Finset.Icc 1 n, w r * ((r : ℝ) * W ^ k)) =
            (∑ r ∈ Finset.Icc 1 n, (r : ℝ) * w r) * W ^ k
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          ring
      _ = (↑(k + 1) : ℝ) * cutoffFirstMoment w n * cutoffMass w n ^ (k + 1 - 1) := by
        change W * ((k : ℝ) * M * W ^ (k - 1)) + M * W ^ k =
          (↑(k + 1) : ℝ) * M * W ^ (k + 1 - 1)
        cases k <;> simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul,
          mul_zero, zero_add, pow_zero, one_mul, Nat.add_sub_cancel, Nat.zero_sub,
          pow_succ] <;> ring

/-- The geometric approximation error is controlled by the first moment of one increment. -/
theorem geometric_sub_renewalFunction_le {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ)
    (hsub : cutoffMass w n < 1) :
    1 / (1 - cutoffMass w n) - renewalFunction w n ≤
      cutoffFirstMoment w n / ((n + 1 : ℝ) * (1 - cutoffMass w n) ^ 2) := by
  let W := cutoffMass w n
  let M := cutoffFirstMoment w n
  have hW : 0 ≤ W := Finset.sum_nonneg fun r _ => hw r
  have hnorm : ‖W‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hW]; exact hsub
  have hden : 1 - W ≠ 0 := (sub_pos.mpr hsub).ne'
  have hgeo : HasSum (fun k : ℕ => W ^ k) (1 / (1 - W)) :=
    by simpa only [one_div] using hasSum_geometric_of_lt_one hW hsub
  have hdiff := hgeo.sub (hasSum_cumulativePower w n)
  have hshift : HasSum (fun k => W ^ (k + 1) - cumulativePower w (k + 1) n)
      (1 / (1 - W) - renewalFunction w n) := by
    have h := (hasSum_nat_add_iff' 1).mpr hdiff
    simpa only [Finset.sum_range_one, pow_zero, cumulativePower_zero, sub_self, sub_zero] using h
  have hseries : HasSum (fun k : ℕ => (k + 1 : ℝ) * W ^ k) (1 / (1 - W) ^ 2) := by
    simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
      (hasSum_choose_mul_geometric_of_norm_lt_one 1 hnorm)
  have hle : (n + 1 : ℝ) * (1 / (1 - W) - renewalFunction w n) ≤ M * (1 / (1 - W) ^ 2) := by
    apply hasSum_le _ (hshift.mul_left (n + 1 : ℝ)) (hseries.mul_left M)
    intro k
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_assoc, mul_left_comm] using
      (cutoff_overshoot_le_firstMoment hw (k + 1) (le_refl n))
  apply (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < n + 1)
    (sq_pos_of_pos (sub_pos.mpr hsub)))).mpr
  calc
    (1 / (1 - W) - renewalFunction w n) * ((n + 1 : ℝ) * (1 - W) ^ 2) =
        ((n + 1 : ℝ) * (1 / (1 - W) - renewalFunction w n)) * (1 - W) ^ 2 := by ring
    _ ≤ (M * (1 / (1 - W) ^ 2)) * (1 - W) ^ 2 :=
      mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = M := by field_simp [hden]

end Critical2DKPZ.Renewal

end
