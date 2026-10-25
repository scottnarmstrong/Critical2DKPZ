/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25LogGreen
import Critical2DKPZ.MomentBounds.GreenDiagonal

/-! # The local-uniformity implication in CSZ25 Lemma 5.1 -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- The inverse-spread squared-mass hypothesis implies the logarithmic Green-energy bound in CSZ25 Lemma 5.1. -/
theorem log_mul_sq_le_greenEnergy (t c₁ c₂ : ℝ) (ht : 0 < t) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ c₂' : ℝ, 0 < c₂' ∧ ∀ L : ℕ, 2 ≤ L → ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) → HasSum φ 1 →
      ExpLocalized t c₁ L φ → ∑' z, φ z ^ 2 ≤ c₂ / profileSpread φ →
      Real.log (L * ∑' z, φ z ^ 2) ≤ c₂' * greenEnergy L φ := by
  obtain ⟨c, hc, hlogGreen⟩ := greenEnergy_half_ge_log t c₁ ht hc₁
  obtain ⟨η, hη, hGreen⟩ := greenEnergy_half_ge t c₁ ht hc₁
  let B := Real.log (12 * (c₂ + 1))
  have hB : 0 < B := Real.log_pos (by nlinarith only [hc₂])
  refine ⟨1 / c + B / η, by positivity, fun L hL φ hφ hmass hlocal hS => ?_⟩
  let D := profileSpread φ
  let S := ∑' z, φ z ^ 2
  let M := L / 2
  let W := 1 + 4 * D
  let Y := Real.log (1 + (M : ℝ) / W)
  have hD : 0 ≤ D := profileSpread_nonneg φ hφ
  have hS0 : 0 ≤ S := tsum_nonneg (fun z => sq_nonneg _)
  have hS1 : S ≤ 1 := by
    have hpoint : ∀ z, φ z ^ 2 ≤ φ z := by
      intro z
      have hz : φ z ≤ 1 := hmass.tsum_eq ▸ hmass.summable.le_tsum z (fun w _ => hφ w)
      nlinarith only [mul_le_mul_of_nonneg_left hz (hφ z)]
    exact ((summable_sq_probability_profile φ hφ hmass).tsum_le_tsum hpoint hmass.summable).trans_eq hmass.tsum_eq
  have hE : 0 ≤ greenEnergy L φ := greenEnergy_nonneg L φ hφ
  by_cases hSz : S = 0
  · simpa only [show (∑' z, φ z ^ 2) = 0 from hSz, mul_zero, Real.log_zero] using
      mul_nonneg (show 0 ≤ 1 / c + B / η by positivity) hE
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSz)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hW : 0 < W := by dsimp [W]; positivity
  have hDS : S * D ≤ c₂ := by
    by_cases hDz : D = 0
    · simp only [hDz, mul_zero]
      exact hc₂.le
    · exact (le_div_iff₀ (lt_of_le_of_ne hD (Ne.symm hDz))).1 hS
  have hSD : S * (D + 1) ≤ c₂ + 1 := by nlinarith only [hDS, hS1]
  have hLM : (L : ℝ) ≤ 3 * M := by
    exact_mod_cast (show L ≤ 3 * M by dsimp [M]; omega)
  have hbound : (L : ℝ) * S * W ≤ 12 * (c₂ + 1) * (W + M) := by
    calc
      _ ≤ (L : ℝ) * S * (4 * (D + 1)) :=
        mul_le_mul_of_nonneg_left (by dsimp [W]; linarith) (mul_nonneg hL0.le hS0)
      _ = 4 * L * (S * (D + 1)) := by ring
      _ ≤ 4 * L * (c₂ + 1) := mul_le_mul_of_nonneg_left hSD (by positivity)
      _ ≤ 12 * M * (c₂ + 1) := by
        have h := mul_le_mul_of_nonneg_right hLM (show 0 ≤ 4 * (c₂ + 1) by positivity)
        nlinarith only [h]
      _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ c₂ + 1 by positivity) hW.le]
  have hbound' : (L : ℝ) * S ≤ (12 * (c₂ + 1)) * (1 + (M : ℝ) / W) := by
    have h := (le_div_iff₀ hW).2 hbound
    convert h using 1
    field_simp
  have hlog : Real.log ((L : ℝ) * S) ≤ B + Y := by
    have h := Real.log_le_log (mul_pos hL0 hSp) hbound'
    rwa [Real.log_mul (show 12 * (c₂ + 1) ≠ 0 by positivity)
      (show 1 + (M : ℝ) / W ≠ 0 by positivity)] at h
  have hmono := greenEnergy_mono (Nat.div_le_self L 2) φ hφ hmass.summable
  have hY : Y ≤ greenEnergy L φ / c := by
    apply (le_div_iff₀ hc).2
    have h := (hlogGreen L φ hφ hmass hlocal).trans hmono
    simpa only [mul_comm] using h
  have hηE : η ≤ greenEnergy L φ := (hGreen L hL φ hφ hmass hlocal).trans hmono
  have hBE : B ≤ (B / η) * greenEnergy L φ := by
    have h := mul_le_mul_of_nonneg_left hηE (div_nonneg hB.le hη.le)
    calc
      _ = (B / η) * η := by field_simp
      _ ≤ _ := h
  calc
    _ ≤ B + Y := hlog
    _ ≤ (B / η) * greenEnergy L φ + greenEnergy L φ / c := add_le_add hBE hY
    _ = _ := by ring

end Critical2DKPZ.MomentBounds
