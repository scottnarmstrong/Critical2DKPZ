/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.GammaBounds
public import Critical2DKPZ.SHF.DeltaBose.CollisionScaling
public import Critical2DKPZ.SHF.DeltaBose.TwoParticle
import Mathlib.Tactic

/-! # Scalar Gamma identities and signed bounds

These scalar examples concern the Gamma-function and diagram estimates in GQT21. -/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata

/-- At two particles, the joint spatial Laplace domain has dimension six. -/
theorem gqt21_joint_laplace_dimension :
    Module.finrank ℝ (DeltaBose.Configuration 2 ×
      DeltaBose.FusedConfiguration DeltaBose.pairTwo) = 6 := by
  rw [Module.finrank_prod, DeltaBose.finrank_fusedConfiguration]
  norm_num [DeltaBose.Configuration, Module.finrank_pi_fintype,
    Plane, finrank_euclideanSpace]

/-- At `α = 2`, the proposed Gamma-function bound fails. -/
theorem gqt21_stirling_step_false (C : ℝ) (hC : 0 < C) :
    ¬ Real.exp (-Real.log (Real.Gamma 2)) ≤ (2 : ℝ) / 2 * Real.log 2 - C * 2 := by
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    simpa only [one_add_one_eq_two, Real.Gamma_one, mul_one] using
      Real.Gamma_add_one (show (1 : ℝ) ≠ 0 by norm_num)
  rw [hg, Real.log_one, neg_zero, Real.exp_zero]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul] at *
  linarith only [hl, hC]

/-- At `α = 2` and `k = 0`, the Gamma quotient is one rather than `α`. -/
theorem gqt21_polynomial_gamma_quotient_false :
    Real.Gamma (2 + 0 + 1) / Real.Gamma (2 + 1) ≠ (2 : ℝ) := by
  norm_num only [show (2 : ℝ) + 0 + 1 = 3 by norm_num,
    show (2 : ℝ) + 1 = 3 by norm_num]
  rw [div_self (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3)).ne']
  norm_num

/-- The reciprocal logarithmic factor is negative and cannot give the proposed positive bound. -/
theorem gqt21_diagram_log_factor_negative {t C : ℝ} (ht : 0 < t) (hC : 0 < C)
    (m : ℕ) : C * (Real.log (min (t / (2 * (m : ℝ) + 1)) (1 / 2)))⁻¹ < 0 := by
  have hpos : 0 < min (t / (2 * (m : ℝ) + 1)) (1 / 2) := by positivity
  have hlt : min (t / (2 * (m : ℝ) + 1)) (1 / 2) < 1 :=
    (min_le_right _ _).trans_lt (by norm_num)
  exact mul_neg_of_pos_of_neg hC (inv_neg''.mpr (Real.log_neg hpos hlt))

/-- A positive exponential factor cannot be discarded in the stated integral comparison. -/
theorem gqt21_positive_exponential_not_damping {a : ℝ} (ha : 0 < a) :
    ¬ Real.exp a ≤ 1 := by
  exact not_le.mpr (Real.one_lt_exp_iff.mpr ha)

end Critical2DKPZ.Errata
