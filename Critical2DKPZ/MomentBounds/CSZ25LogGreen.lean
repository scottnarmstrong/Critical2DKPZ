/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25UniformGreen
import Critical2DKPZ.MomentBounds.GreenLogRatio
import Critical2DKPZ.MomentBounds.LocalizedProfileMoments

/-! # The logarithmic Green lower bound of CSZ25 Lemma 5.1 -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Exponentially localized profiles satisfy the logarithmic lower Green-energy bound of CSZ25 Lemma 5.1. -/
theorem greenEnergy_half_ge_log (t c₁ : ℝ) (ht : 0 < t) (hc₁ : 0 < c₁) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℕ, ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) → HasSum φ 1 →
      ExpLocalized t c₁ L φ →
      c * Real.log (1 + ((L / 2 : ℕ) : ℝ) / (1 + 4 * profileSpread φ)) ≤ greenEnergy (L / 2) φ := by
  obtain ⟨d, A, hd, hA, hlog⟩ := exists_greenEnergy_ge_log_ratio
  obtain ⟨η, hη, hunif⟩ := greenEnergy_half_ge t c₁ ht hc₁
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let b := Real.log (2 * A)
  have hb : 0 < b := Real.log_pos (by linarith only [hA])
  let c := min (d / 2) (η / (2 * b))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc, fun L φ hφ hmass hlocal => ?_⟩
  by_cases hL : 2 ≤ L
  · let M := L / 2
    let D := profileSpread φ
    let X := (M : ℝ) / (D + 1)
    let Y := Real.log (1 + (M : ℝ) / (1 + 4 * D))
    have hD : 0 ≤ D := profileSpread_nonneg φ hφ
    have hM : 1 ≤ M := by dsimp [M]; omega
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hX : 0 < X := div_pos hM0 (by positivity)
    have hY0 : 0 ≤ Y := Real.log_nonneg (le_add_of_nonneg_right
      (div_nonneg (Nat.cast_nonneg M) (show 0 ≤ 1 + 4 * D by positivity)))
    have hE0 := greenEnergy_nonneg M φ hφ
    have hquad := summable_quadratic_of_expLocalized t c₁ ht L (by omega) φ hφ hmass hlocal (profileMean φ)
    have hlo := hlog M hM φ hφ hmass hquad
    have heq : (M : ℝ) / (A * (D + 1)) = X / A := by
      dsimp [X]
      rw [div_div, mul_comm A]
    rw [heq, Real.log_div hX.ne' hA0.ne'] at hlo
    have hY : Y ≤ Real.log (1 + X) := by
      apply Real.log_le_log (by positivity)
      have hdiv : (M : ℝ) / (1 + 4 * D) ≤ X :=
        div_le_div_of_nonneg_left hM0.le (by positivity) (by linarith only [hD])
      linarith only [hdiv]
    have hbEq : b = Real.log 2 + Real.log A := Real.log_mul (by norm_num) hA0.ne'
    have hrough : d * Y ≤ greenEnergy M φ + d * b := by
      by_cases hX1 : 1 ≤ X
      · have hy : Y ≤ Real.log 2 + Real.log X := by
          calc
            _ ≤ Real.log (1 + X) := hY
            _ ≤ Real.log (2 * X) := Real.log_le_log (by positivity) (by linarith only [hX1])
            _ = _ := Real.log_mul (by norm_num) hX.ne'
        have hdy := mul_le_mul_of_nonneg_left hy hd.le
        rw [hbEq]
        nlinarith only [hdy, hlo]
      · have hy : Y ≤ Real.log 2 := hY.trans
          (Real.log_le_log (by positivity) (by linarith only [hX1]))
        have hb2 : Real.log 2 ≤ b := Real.log_le_log (by norm_num) (by linarith only [hA])
        exact (mul_le_mul_of_nonneg_left (hy.trans hb2) hd.le).trans (le_add_of_nonneg_left hE0)
    change c * Y ≤ greenEnergy M φ
    by_cases hy : Y ≤ 2 * b
    · calc
        _ ≤ (η / (2 * b)) * Y := mul_le_mul_of_nonneg_right (min_le_right _ _) hY0
        _ ≤ η := by
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ (mul_pos (by norm_num) hb)).2
          exact mul_le_mul_of_nonneg_left hy hη.le
        _ ≤ _ := hunif L hL φ hφ hmass hlocal
    · have hsmall : d * b ≤ (d / 2) * Y := by
        nlinarith only [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hy)) hd.le]
      have hhalf : (d / 2) * Y ≤ greenEnergy M φ := by nlinarith only [hrough, hsmall]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hY0).trans hhalf
  · have hzero : L / 2 = 0 := by omega
    simp only [hzero, Nat.cast_zero, zero_div, add_zero, Real.log_one, mul_zero,
      greenEnergy, truncatedGreen, Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      Finset.sum_empty, zero_mul, mul_zero, tsum_zero, le_refl]

end Critical2DKPZ.MomentBounds
