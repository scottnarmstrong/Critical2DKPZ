/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Gamma estimates for the scalar collision density

A unit interval in the Gamma integral gives a lower bound at every exponential
rate. Together with the recurrence, this supplies an integrable majorant for
`t^(u-1) exp(θu) / Γ(u)` without Stirling's formula. The positive minimum of
Gamma gives the sharper bound needed at small times.
-/

public section

open MeasureTheory Set

namespace Critical2DKPZ.DeltaBose

/-- Restricting the Gamma integral to `[R,R+1]` yields an exponential lower bound. -/
theorem exp_neg_mul_rpow_le_gamma_add_one {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    Real.exp (-(R + 1)) * R ^ u ≤ Real.Gamma (u + 1) := by
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ u) (Ioi 0) := by
    simpa only [add_sub_cancel_right] using Real.GammaIntegral_convergent (by linarith : 0 < u + 1)
  have hsub : Icc R (R + 1) ⊆ Ioi (0 : ℝ) := fun _ hx => hR.trans_le hx.1
  have hib := hi.mono_set hsub
  calc
    Real.exp (-(R + 1)) * R ^ u
      = ∫ _x in Icc R (R + 1), Real.exp (-(R + 1)) * R ^ u := by
        simp [Real.volume_Icc, Measure.real]
    _ ≤ ∫ x in Icc R (R + 1), Real.exp (-x) * x ^ u := by
      apply setIntegral_mono_on (integrable_const _) hib measurableSet_Icc
      intro x hx
      exact mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hx.2))
        (Real.rpow_le_rpow hR.le hx.1 hu.le) (by positivity) (by positivity)
    _ ≤ ∫ x in Ioi 0, Real.exp (-x) * x ^ u :=
      setIntegral_mono_set hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx.le _))
        (Filter.Eventually.of_forall hsub)
    _ = Real.Gamma (u + 1) := by
      rw [Real.Gamma_eq_integral (by linarith : 0 < u + 1)]
      simp only [add_sub_cancel_right]

/-- A reciprocal Gamma bound at any prescribed exponential rate. -/
theorem inv_gamma_le_exp_mul {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    (Real.Gamma u)⁻¹ ≤ Real.exp (R + 1) * u * R ^ (-u) := by
  have hg := Real.Gamma_pos_of_pos hu
  have h := exp_neg_mul_rpow_le_gamma_add_one hu hR
  rw [Real.Gamma_add_one hu.ne'] at h
  have hp := Real.rpow_pos_of_pos hR u
  have he := Real.exp_pos (R + 1)
  have heq : Real.exp (R + 1) * Real.exp (-(R + 1)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.rpow_neg hR.le, inv_le_iff_one_le_mul₀ hg]
  calc
    1 = Real.exp (R + 1) * (Real.exp (-(R + 1)) * R ^ u) * (R ^ u)⁻¹ := by
      rw [← mul_assoc, heq, one_mul, mul_inv_cancel₀ hp.ne']
    _ ≤ Real.exp (R + 1) * (u * Real.Gamma u) * (R ^ u)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h he.le) (inv_nonneg.mpr hp.le)
    _ = (Real.exp (R + 1) * u * (R ^ u)⁻¹) * Real.Gamma u := by ring

/-- Gamma has a strictly positive lower bound on the positive half line. -/
theorem exists_pos_le_gamma : ∃ m : ℝ, 0 < m ∧ ∀ u : ℝ, 0 < u → m ≤ Real.Gamma u := by
  obtain ⟨x, hx, hmin⟩ := Real.exists_isMinOn_Gamma_Ioi
  exact ⟨Real.Gamma x, Real.Gamma_pos_of_pos (by linarith [hx.1]), fun u hu => hmin hu⟩

/-- Near zero, the reciprocal Gamma function is bounded by a multiple of its argument. -/
theorem exists_inv_gamma_le_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → (Real.Gamma u)⁻¹ ≤ C * u := by
  obtain ⟨m, hm, h⟩ := exists_pos_le_gamma
  refine ⟨m⁻¹, inv_pos.mpr hm, fun u hu => ?_⟩
  have hg := Real.Gamma_pos_of_pos hu
  rw [inv_le_iff_one_le_mul₀ hg]
  have hbound := h (u + 1) (by linarith)
  rw [Real.Gamma_add_one hu.ne'] at hbound
  calc 1 = m⁻¹ * m := (inv_mul_cancel₀ hm.ne').symm
    _ ≤ m⁻¹ * (u * Real.Gamma u) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hm.le)
    _ = (m⁻¹ * u) * Real.Gamma u := (mul_assoc _ _ _).symm

/-- The elementary exponential first moment used as a dominating function. -/
theorem integrableOn_mul_exp_neg {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-(r * u))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) (by norm_num) hr)

/-- Its value is the inverse square of the rate. -/
theorem integral_mul_exp_neg {r : ℝ} (hr : 0 < r) :
    ∫ u : ℝ in Ioi 0, u * Real.exp (-(r * u)) = r⁻¹ ^ 2 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, one_div, Real.Gamma_two, mul_one] using Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr

end Critical2DKPZ.DeltaBose
