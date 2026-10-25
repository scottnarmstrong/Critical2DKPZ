/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! # Laplace endpoint powers in the conjugated diagram chain -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Integrability and the positive-integral form of Mathlib's Gamma formula
for a Laplace-damped endpoint power. -/
theorem integrableOn_and_lintegral_exp_mul_rpow {b rate : ℝ} (hb : -1 < b) (hrate : 0 < rate) :
    IntegrableOn (fun t : ℝ => Real.exp (-(rate * t)) * t ^ b) (Ioi 0) ∧
      (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(rate * t)) * t ^ b)) =
        ENNReal.ofReal ((1 / rate) ^ (b + 1) * Real.Gamma (b + 1)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ b * Real.exp (-(rate * t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow hb one_pos hrate)
  have hi' : IntegrableOn (fun t : ℝ => Real.exp (-(rate * t)) * t ^ b) (Ioi 0) := by
    simpa only [mul_comm] using hi
  refine ⟨hi', ?_⟩
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ => Real.exp (-(rate * t)) * t ^ b) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi' hn]
  congr 1
  calc
    _ = ∫ t : ℝ in Ioi 0, t ^ b * Real.exp (-(rate * t)) := by
      apply integral_congr_ae
      filter_upwards with t
      exact mul_comm _ _
    _ = _ := by
      simpa only [add_sub_cancel_right] using
        (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := b + 1) (by linarith) hrate)

end Critical2DKPZ.SHF.Tsai

end
