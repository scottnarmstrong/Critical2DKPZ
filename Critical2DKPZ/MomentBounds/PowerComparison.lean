/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Uniform power comparisons on neighboring lattice intervals -/

public section

namespace Critical2DKPZ.MomentBounds

/-- Exponents at least minus one cost at most two on a positive interval of ratio two. -/
theorem rpow_le_two_mul_rpow {k x γ : ℝ} (hk : 0 < k) (hkx : k ≤ x)
    (hxk : x ≤ 2 * k) (hγ : -1 ≤ γ) : k ^ γ ≤ 2 * x ^ γ := by
  by_cases hγ0 : 0 ≤ γ
  · exact (Real.rpow_le_rpow hk.le hkx hγ0).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (hk.le.trans hkx) _) (by norm_num))
  · have hneg : γ ≤ 0 := (lt_of_not_ge hγ0).le
    have htwo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hγ
    rw [Real.rpow_neg_one] at htwo
    have hcoeff : 1 ≤ 2 * (2 : ℝ) ^ γ := by linarith only [htwo]
    have hcomp := Real.rpow_le_rpow_of_nonpos (hk.trans_le hkx) hxk hneg
    calc
      k ^ γ = 1 * k ^ γ := (one_mul _).symm
      _ ≤ (2 * (2 : ℝ) ^ γ) * k ^ γ :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hk.le _)
      _ = 2 * (2 * k) ^ γ := by rw [Real.mul_rpow (by norm_num) hk.le]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (by norm_num)

/-- Doubling the numerator and increasing the positive denominator by at most four changes the quotient by at most a factor of eight. -/
theorem div_le_eight_mul_div {u v A B : ℝ} (hu : u ≤ 2 * v) (hv : 0 ≤ v)
    (hA : 0 < A) (hB : 0 < B) (hBA : B ≤ 4 * A) :
    u / A ≤ 8 * (v / B) := by
  rw [show 8 * (v / B) = (8 * v) / B by ring, div_le_div_iff₀ hA hB]
  calc
    u * B ≤ (2 * v) * B := mul_le_mul_of_nonneg_right hu hB.le
    _ ≤ (2 * v) * (4 * A) := mul_le_mul_of_nonneg_left hBA (by positivity)
    _ = _ := by ring

/-- The radial shell summand is bounded by eight times its value on the next unit interval. -/
theorem radial_summand_le_eight {L k x γ : ℝ} (hL : 0 < L) (hk : 1 ≤ k)
    (hkx : k ≤ x) (hxk : x ≤ k + 1) (hγ : -1 ≤ γ) :
    k ^ γ / (L + k ^ 2) ≤ 8 * (x ^ γ / (L + x ^ 2)) := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hxdouble : x ≤ 2 * k := by linarith only [hxk, hk]
  have hdenom : L + x ^ 2 ≤ 4 * (L + k ^ 2) := by
    have hxnonneg : 0 ≤ x := hkpos.le.trans hkx
    have hsq := pow_le_pow_left₀ hxnonneg hxdouble 2
    nlinarith only [hsq, hL]
  exact div_le_eight_mul_div (rpow_le_two_mul_rpow hkpos hkx hxdouble hγ)
    (Real.rpow_nonneg (hkpos.le.trans hkx) _)
    (by positivity) (by positivity) hdenom

end Critical2DKPZ.MomentBounds
