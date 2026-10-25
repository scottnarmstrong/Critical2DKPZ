/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib.Tactic

/-! # Uniform bounds for the scalar collision density

The density has a logarithmic small-time bound and an exponential bound at all positive times, both uniform when the parameter is bounded above. -/

public section

open MeasureTheory Set

namespace Critical2DKPZ.DeltaBose

/-- An exponential bound valid at all positive times and uniform in `θ ≤ B`. -/
theorem scalarDensity_le_exp {θ B t : ℝ} (hθ : θ ≤ B) (ht : 0 < t) :
    scalarDensity θ t ≤ Real.exp 1 / t * Real.exp (Real.exp (B + 1) * t) := by
  rw [scalarDensity_eq_laplace θ ht]
  have hb : ∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u ≤
      Real.exp (Real.exp (B + Real.log t + 1) + 1) := by
    calc (∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u)
        ≤ ∫ u in Ioi 0, Real.exp (Real.exp (B + Real.log t + 1) + 1) *
            (u * Real.exp (-(1 * u))) := by
          apply integral_mono_ae (integrableOn_gammaLaplaceIntegrand _)
            ((integrableOn_mul_exp_neg zero_lt_one).const_mul _)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact gammaLaplaceIntegrand_le (add_le_add hθ le_rfl) hu
      _ = Real.exp (Real.exp (B + Real.log t + 1) + 1) := by
        rw [integral_const_mul, integral_mul_exp_neg zero_lt_one]
        norm_num
  refine (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht.le)).trans_eq ?_
  have he : Real.exp (B + Real.log t + 1) = Real.exp (B + 1) * t := by
    rw [show B + Real.log t + 1 = (B + 1) + Real.log t by ring, Real.exp_add,
      Real.exp_log ht]
  rw [he, Real.exp_add]
  ring

/-- A uniform logarithmic upper bound once the time is sufficiently small. -/
theorem exists_scalarDensity_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ θ B t : ℝ, θ ≤ B → 0 < t →
      t ≤ Real.exp (-(2 * |B| + 1)) →
      scalarDensity θ t ≤ C / (t * (Real.log t) ^ 2) := by
  obtain ⟨K, hK, hGamma⟩ := exists_inv_gamma_le_mul
  refine ⟨4 * K, by positivity, fun θ B t hθ ht hsmall => ?_⟩
  have hlog : Real.log t ≤ -(2 * |B| + 1) := by
    exact (Real.log_le_log ht hsmall).trans_eq (Real.log_exp _)
  have hL : 0 < -Real.log t := by linarith only [hlog, abs_nonneg B]
  have hr : 0 < -(θ + Real.log t) := by
    linarith only [hθ, hlog, le_abs_self B, abs_nonneg B]
  have hrL : (-Real.log t) / 2 ≤ -(θ + Real.log t) := by
    linarith only [hθ, hlog, le_abs_self B]
  have hpoint : ∀ u : ℝ, 0 < u → gammaLaplaceIntegrand (θ + Real.log t) u ≤
      K * (u * Real.exp (-((-(θ + Real.log t)) * u))) := by
    intro u hu
    unfold gammaLaplaceIntegrand
    rw [div_eq_mul_inv]
    calc Real.exp ((θ + Real.log t) * u) * (Real.Gamma u)⁻¹
        ≤ Real.exp ((θ + Real.log t) * u) * (K * u) :=
          mul_le_mul_of_nonneg_left (hGamma u hu) (Real.exp_nonneg _)
      _ = _ := by ring
  have hbound : ∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u ≤
      K * (-(θ + Real.log t))⁻¹ ^ 2 := by
    calc (∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u)
        ≤ ∫ u in Ioi 0, K * (u * Real.exp (-((-(θ + Real.log t)) * u))) := by
          apply integral_mono_ae (integrableOn_gammaLaplaceIntegrand _)
            ((integrableOn_mul_exp_neg hr).const_mul K)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact hpoint u hu
      _ = K * (-(θ + Real.log t))⁻¹ ^ 2 := by
        rw [integral_const_mul, integral_mul_exp_neg hr]
  have hrate : (-(θ + Real.log t))⁻¹ ^ 2 ≤ 4 / (Real.log t) ^ 2 := by
    have hs : (Real.log t) ^ 2 ≤ 4 * (-(θ + Real.log t)) ^ 2 := by
      nlinarith only [hrL, hL, hr]
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ (show 0 < (Real.log t) ^ 2 by
      simpa only [neg_sq] using sq_pos_of_pos hL), one_mul]
    exact hs
  rw [scalarDensity_eq_laplace θ ht]
  calc t⁻¹ * (∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u)
      ≤ t⁻¹ * (K * (-(θ + Real.log t))⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr ht.le)
    _ ≤ t⁻¹ * (K * (4 / (Real.log t) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrate hK.le) (inv_nonneg.mpr ht.le)
    _ = 4 * K / (t * (Real.log t) ^ 2) := by ring

end Critical2DKPZ.DeltaBose
