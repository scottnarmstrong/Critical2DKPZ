/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The negative Sobolev Fourier weight has a Gamma-mixture representation. -/

public section

noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ

/-- Every negative Sobolev Fourier weight is nonnegative. -/
theorem negSobolev_weight_nonneg (a : ℝ) (ξ : Plane) :
    0 ≤ (1 + ‖ξ‖ ^ 2) ^ (-a) := Real.rpow_nonneg (by positivity) _


/-- A negative Sobolev Fourier weight of nonnegative order is at most one. -/
theorem negSobolev_weight_le_one {a : ℝ} (ha : 0 ≤ a) (ξ : Plane) :
    (1 + ‖ξ‖ ^ 2) ^ (-a) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [sq_nonneg ‖ξ‖]) (neg_nonpos.mpr ha)

/-- The Gamma mixture is integrable for every positive Sobolev order. -/
theorem integrableOn_negSobolev_weight_integrand {a : ℝ} (ha : 0 < a) (ξ : Plane) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-u) *
      Real.exp (-u * ‖ξ‖ ^ 2)) (Ioi 0) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
    (s := a - 1) (b := 1 + ‖ξ‖ ^ 2) (by linarith only [ha]) zero_lt_one (by positivity)
  convert hg using 1
  funext u
  rw [Real.rpow_one, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Laplace representation of the exact Fourier multiplier defining `H^{-a}`. -/
theorem negSobolev_weight_eq_gamma_integral {a : ℝ} (ha : 0 < a) (ξ : Plane) :
    (1 + ‖ξ‖ ^ 2) ^ (-a) = (Real.Gamma a)⁻¹ *
      ∫ u : ℝ in Ioi 0, u ^ (a - 1) * Real.exp (-u) * Real.exp (-u * ‖ξ‖ ^ 2) := by
  have he : (fun u : ℝ => u ^ (a - 1) * Real.exp (-u) * Real.exp (-u * ‖ξ‖ ^ 2)) =
      fun u : ℝ => u ^ (a - 1) * Real.exp (-((1 + ‖ξ‖ ^ 2) * u)) := by
    funext u
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by positivity), one_div,
    Real.inv_rpow (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2),
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2)]
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

end Critical2DKPZ

end
