/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Weight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds for translated negative Sobolev weights

The Fourier weight at a translated frequency is controlled by the original frequency and a
polynomial factor in the translation. This is the pointwise estimate used in the weighted Young
bound for multiplication by a smooth localizer.
-/

@[expose] public section

namespace Critical2DKPZ.Analysis.Sobolev

/-- The squared-frequency base at `ξ - η` is bounded by the product of the bases at `ξ` and
`η`, up to the factor two. -/
theorem one_add_norm_sub_sq_le_mul (ξ η : Plane) :
    1 + ‖ξ - η‖ ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) * (1 + ‖η‖ ^ 2) := by
  have htri := norm_sub_le ξ η
  have hsq : ‖ξ - η‖ ^ 2 ≤ 2 * ‖ξ‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    calc
      ‖ξ - η‖ ^ 2 ≤ (‖ξ‖ + ‖η‖) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (ξ - η)]) htri
      _ ≤ 2 * ‖ξ‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
        nlinarith [sq_nonneg (‖ξ‖ - ‖η‖)]
  nlinarith [sq_nonneg ‖ξ‖, sq_nonneg ‖η‖]

/-- Polynomial Sobolev weights obey the frequency-shift bound required for convolution:
`(1 + |ξ - η|²)^a ≤ 2^a (1 + |ξ|²)^a (1 + |η|²)^a` for every `a ≥ 0`. -/
theorem one_add_norm_sub_sq_rpow_le {a : ℝ} (ha : 0 ≤ a) (ξ η : Plane) :
    (1 + ‖ξ - η‖ ^ 2) ^ a ≤
      2 ^ a * (1 + ‖ξ‖ ^ 2) ^ a * (1 + ‖η‖ ^ 2) ^ a := by
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + ‖ξ - η‖ ^ 2)
    (one_add_norm_sub_sq_le_mul ξ η) ha
  rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) * (1 + ‖ξ‖ ^ 2))
      (by positivity : 0 ≤ 1 + ‖η‖ ^ 2),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2)] at hp
  exact hp

/-- The negative Sobolev weight at `ξ` is controlled by the weight at `ξ - η`, with
polynomial loss only in the translation frequency `η`. -/
theorem negSobolevWeight_shift_le {a : ℝ} (ha : 0 ≤ a) (ξ η : Plane) :
    (1 + ‖ξ‖ ^ 2) ^ (-a) ≤
      2 ^ a * (1 + ‖η‖ ^ 2) ^ a * (1 + ‖ξ - η‖ ^ 2) ^ (-a) := by
  let A : ℝ := 1 + ‖ξ‖ ^ 2
  let B : ℝ := 1 + ‖η‖ ^ 2
  let C : ℝ := 1 + ‖ξ - η‖ ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hAcancel : A ^ (-a) * A ^ a = 1 := by
    rw [← Real.rpow_add hA, neg_add_cancel, Real.rpow_zero]
  have hCcancel : C ^ (-a) * C ^ a = 1 := by
    rw [← Real.rpow_add hC, neg_add_cancel, Real.rpow_zero]
  have hAcancel' : A ^ a * A ^ (-a) = 1 := by simpa [mul_comm] using hAcancel
  have hCcancel' : C ^ a * C ^ (-a) = 1 := by simpa [mul_comm] using hCcancel
  have hpoly : C ^ a ≤ (2 ^ a * B ^ a) * A ^ a := by
    have h := one_add_norm_sub_sq_rpow_le ha ξ η
    dsimp [A, B, C] at h ⊢
    nlinarith [h]
  have hQ : 0 < A ^ a * C ^ a := by positivity
  change A ^ (-a) ≤ 2 ^ a * B ^ a * C ^ (-a)
  apply (mul_le_mul_iff_right₀ hQ).mp
  calc
    A ^ a * C ^ a * A ^ (-a) = C ^ a := by
      calc
        A ^ a * C ^ a * A ^ (-a) = (A ^ a * A ^ (-a)) * C ^ a := by ring
        _ = C ^ a := by rw [hAcancel', one_mul]
    _ ≤ (2 ^ a * B ^ a) * A ^ a := hpoly
    _ = A ^ a * C ^ a * (2 ^ a * B ^ a * C ^ (-a)) := by
      calc
        (2 ^ a * B ^ a) * A ^ a = (2 ^ a * B ^ a) * A ^ a * 1 := by simp
        _ = (2 ^ a * B ^ a) * A ^ a * (C ^ a * C ^ (-a)) := by rw [← hCcancel']
        _ = A ^ a * C ^ a * (2 ^ a * B ^ a * C ^ (-a)) := by ring

/-- The square root of the negative Sobolev weight obeys the frequency-shift estimate used by
the weighted `L²` translation operator. -/
theorem sqrt_negSobolevWeight_shift_le {a : ℝ} (ha : 0 ≤ a) (ξ η : Plane) :
    Real.sqrt ((1 + ‖ξ‖ ^ 2) ^ (-a)) ≤
      Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) *
        Real.sqrt ((1 + ‖ξ - η‖ ^ 2) ^ (-a)) := by
  have h := negSobolevWeight_shift_le ha ξ η
  calc
    Real.sqrt ((1 + ‖ξ‖ ^ 2) ^ (-a)) ≤
        Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a *
          (1 + ‖ξ - η‖ ^ 2) ^ (-a)) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (2 ^ a * (1 + ‖η‖ ^ 2) ^ a) *
          Real.sqrt ((1 + ‖ξ - η‖ ^ 2) ^ (-a)) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 ^ a * (1 + ‖η‖ ^ 2) ^ a)]

end Critical2DKPZ.Analysis.Sobolev

end
