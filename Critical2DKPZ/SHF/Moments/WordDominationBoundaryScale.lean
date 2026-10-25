/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationScaledBall
import Mathlib.Tactic

/-! # Cancellation of the compact-test boundary scale -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- Cell averaging and terminal endpoint averaging cancel the macroscopic
growth of the two CCR boundary norms. The final factor `X` is the contracted
interaction cost. -/
theorem compactTestBoundaryScale_le {h N : ℕ} (hh : 1 ≤ h) (hN : 0 < N)
    (R M Cb Cball cardA X : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hBall : 0 ≤ Cball)
    (hCard : 0 ≤ cardA) (hCardBound : cardA ≤ Cball * (R + 2) ^ 2 * N)
    (hXle : X ≤ 1) :
    ((4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
      (2 * Cb * cardA * (Real.sqrt cardA) ^ (h - 1)) ^ 2 * X) ≤
      4 * Cb ^ 2 * (8 * M) ^ h * (Cball * (R + 2) ^ 2) ^ (h + 1) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNnonneg : 0 ≤ (N : ℝ) := hNreal.le
  let D : ℝ := Cball * (R + 2) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : cardA ≤ D * N := by simpa [D, mul_assoc] using hCardBound
  have hApow : cardA ^ (h + 1) ≤ (D * N) ^ (h + 1) :=
    pow_le_pow_left₀ hCard hA (h + 1)
  have hboundary :
      (2 * Cb * cardA * (Real.sqrt cardA) ^ (h - 1)) ^ 2 =
        4 * Cb ^ 2 * cardA ^ (h + 1) := by
    calc
      _ = (2 * Cb) ^ 2 * cardA ^ 2 *
          ((Real.sqrt cardA) ^ (h - 1)) ^ 2 := by ring
      _ = 4 * Cb ^ 2 * cardA ^ 2 * (Real.sqrt cardA) ^ (2 * (h - 1)) := by
            rw [pow_mul]
            ring
      _ = 4 * Cb ^ 2 * cardA ^ 2 * cardA ^ (h - 1) := by
            have hsqrt : (Real.sqrt cardA) ^ (2 * (h - 1)) =
                ((Real.sqrt cardA) ^ 2) ^ (h - 1) := by
              rw [pow_mul]
            rw [hsqrt, Real.sq_sqrt hCard]
      _ = 4 * Cb ^ 2 * cardA ^ (h + 1) := by
            calc
              _ = 4 * Cb ^ 2 * (cardA ^ 2 * cardA ^ (h - 1)) := by ring
              _ = 4 * Cb ^ 2 * cardA ^ (2 + (h - 1)) := by
                    rw [← pow_add]
              _ = 4 * Cb ^ 2 * cardA ^ (h + 1) := by
                    rw [show 2 + (h - 1) = h + 1 by omega]
  have hbaseNonneg : 0 ≤ (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) := by
    positivity
  have hstep :
      (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
          (2 * Cb * cardA * (Real.sqrt cardA) ^ (h - 1)) ^ 2 * X ≤
        (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
          (4 * Cb ^ 2 * (D * N) ^ (h + 1)) := by
    calc
      _ ≤ (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
          (4 * Cb ^ 2 * cardA ^ (h + 1)) := by
            rw [hboundary]
            have hfac : 0 ≤ (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
                (4 * Cb ^ 2 * cardA ^ (h + 1)) := by positivity
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hXle hfac
      _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hApow (by positivity)
            · exact hbaseNonneg
  have halgebra :
      (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
          (4 * Cb ^ 2 * (D * N) ^ (h + 1)) =
        4 * Cb ^ 2 * (8 * M) ^ h * D ^ (h + 1) := by
    simp only [div_pow, mul_pow]
    rw [pow_succ]
    have hNh : (N : ℝ) ^ h ≠ 0 := pow_ne_zero _ (ne_of_gt hNreal)
    field_simp [ne_of_gt hNreal, hNh]
    have hprod : (4 : ℝ) ^ h * M ^ h * 2 ^ h = (8 * M) ^ h := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring
    rw [hprod]
    ring
  calc
    _ ≤ (4 * M / N) ^ h * ((2 : ℝ) ^ h / N) *
        (4 * Cb ^ 2 * (D * N) ^ (h + 1)) := hstep
    _ = 4 * Cb ^ 2 * (8 * M) ^ h * D ^ (h + 1) := halgebra
    _ = 4 * Cb ^ 2 * (8 * M) ^ h * (Cball * (R + 2) ^ 2) ^ (h + 1) := by
      simp [D]

end Critical2DKPZ.SHF.Moments

end
