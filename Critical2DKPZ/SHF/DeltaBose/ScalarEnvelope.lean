/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarBounds
import Mathlib.Tactic

/-! The logarithmic collision envelope used by Tsai and Surendranath–Tsai bounds the scalar density uniformly when the parameter is bounded above. -/

@[expose] public section

namespace Critical2DKPZ.DeltaBose

/-- The small-time logarithmic collision envelope is held constant above time `1/2`. -/
noncomputable def collisionTimeEnvelope (t : ℝ) : ℝ :=
  (min t (1 / 2) * (Real.log (min t (1 / 2))) ^ 2)⁻¹

/-- The collision envelope stays uniformly away from zero. -/
theorem half_le_collisionTimeEnvelope {t : ℝ} (ht : 0 < t) :
    (1 / 2 : ℝ) ≤ collisionTimeEnvelope t := by
  let x := min t (1 / 2)
  have hx : 0 < x := lt_min ht (by norm_num)
  have hx1 : x < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hL : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hx hx1)
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by rw [Real.exp_neg, Real.exp_log hx]
  have hp := Real.pow_div_factorial_le_exp (-Real.log x) hL.le 2
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    mul_one, Nat.cast_ofNat, neg_sq] at hp
  rw [hexp] at hp
  have hbound : x * (Real.log x) ^ 2 ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left hp hx.le
    rw [mul_inv_cancel₀ hx.ne'] at hh
    linarith only [hh]
  have hden : 0 < x * (Real.log x) ^ 2 := by
    exact mul_pos hx (sq_pos_of_ne_zero (Real.log_neg hx hx1).ne)
  change 1 / 2 ≤ (x * (Real.log x) ^ 2)⁻¹
  rw [← one_div, le_div_iff₀ hden]
  linarith only [hbound]

/-- The scalar collision density is bounded by a constant times its logarithmic envelope and an exponential time factor, uniformly when its parameter is bounded above. -/
theorem exists_scalarDensity_le_envelope (B : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ θ t : ℝ, θ ≤ B → 0 < t →
      scalarDensity θ t ≤ C * collisionTimeEnvelope t * Real.exp (c * t) := by
  obtain ⟨K, hK, hsmall⟩ := exists_scalarDensity_le_log
  let δ := min (Real.exp (-(2 * |B| + 1))) (1 / 2)
  have hδ : 0 < δ := lt_min (Real.exp_pos _) (by norm_num)
  let C := K + 2 * Real.exp 1 / δ
  let c := Real.exp (B + 1)
  refine ⟨C, c, by dsimp [C]; positivity, Real.exp_pos _, fun θ t hθ ht => ?_⟩
  have he := half_le_collisionTimeEnvelope ht
  have hepos : 0 < collisionTimeEnvelope t := lt_of_lt_of_le (by norm_num) he
  have hCt : 0 ≤ C := by dsimp [C]; positivity
  by_cases h : t ≤ δ
  · have ht2 : t ≤ 1 / 2 := h.trans (min_le_right _ _)
    have hbound := hsmall θ B t hθ ht (h.trans (min_le_left _ _))
    have hKenv : K / (t * (Real.log t) ^ 2) = K * collisionTimeEnvelope t := by
      unfold collisionTimeEnvelope
      rw [min_eq_left ht2, div_eq_mul_inv]
    rw [hKenv] at hbound
    calc scalarDensity θ t ≤ K * collisionTimeEnvelope t := hbound
      _ ≤ C * collisionTimeEnvelope t :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_add_of_nonneg_right (by positivity)) hepos.le
      _ ≤ C * collisionTimeEnvelope t * Real.exp (c * t) := by
        exact le_mul_of_one_le_right (mul_nonneg hCt hepos.le) (Real.one_le_exp (by dsimp [c]; positivity))
  · have hδt : δ ≤ t := (lt_of_not_ge h).le
    have hcoef : Real.exp 1 / t ≤ C * collisionTimeEnvelope t := by
      calc Real.exp 1 / t ≤ Real.exp 1 / δ := div_le_div_of_nonneg_left (Real.exp_nonneg _) hδ hδt
        _ ≤ (2 * Real.exp 1 / δ) * collisionTimeEnvelope t := by
          have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * Real.exp 1 / δ by positivity)
          convert hh using 1
          ring
        _ ≤ C * collisionTimeEnvelope t :=
          mul_le_mul_of_nonneg_right (by dsimp [C]; linarith only [hK]) hepos.le
    exact (scalarDensity_le_exp hθ ht).trans
      (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))

end Critical2DKPZ.DeltaBose
