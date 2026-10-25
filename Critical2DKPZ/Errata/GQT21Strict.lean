/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Critical2DKPZ.Definitions.Plane
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! # Positive heat times and Gamma-function identities -/

public section

namespace Critical2DKPZ.Errata.GQT21

open Critical2DKPZ MeasureTheory

/-- At `α = 2` and `m = 0`, the Gamma quotient differs from the product containing the extra factor `α`. -/
theorem gqt21_09_printed_gamma_product_false :
    Real.Gamma (2 + (0 : ℝ) + 1) / Real.Gamma (2 + 1) ≠
      ∏ i ∈ Finset.range (0 + 1), (2 + (i : ℝ)) := by
  norm_num [Real.Gamma_nat_eq_factorial]

/-- The exact normalized planar integral printed in the polar-coordinate step
of GQT21 Lemma 4.2. -/
noncomputable def gqt21_04_polarIntegral (a : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ ^ 2 * ∫ q : Plane, ((‖q‖ ^ 2 + a) ^ 2)⁻¹

private theorem gqt21_04_integral_scale :
    gqt21_04_polarIntegral 2 = (1 / 2 : ℝ) * gqt21_04_polarIntegral 1 := by
  let f : ℝ → Plane → ℝ := fun a q => ((‖q‖ ^ 2 + a) ^ 2)⁻¹
  have hdim : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume (f 2) (Real.sqrt 2)
    (hR := Real.sqrt_nonneg 2)
  have hscaled : (∫ q : Plane, f 2 (Real.sqrt 2 • q)) =
      (1 / 2 : ℝ) * ∫ q : Plane, f 2 q := by
    calc
      (∫ q : Plane, f 2 (Real.sqrt 2 • q)) =
          (Real.sqrt 2 ^ Module.finrank ℝ Plane)⁻¹ • ∫ q : Plane, f 2 q := hchange
      _ = (1 / 2 : ℝ) * ∫ q : Plane, f 2 q := by
        rw [hdim, smul_eq_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hnorm (q : Plane) : ‖Real.sqrt 2 • q‖ ^ 2 = 2 * ‖q‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpoint (q : Plane) : f 2 (Real.sqrt 2 • q) = (1 / 4 : ℝ) * f 1 q := by
    dsimp [f]
    rw [hnorm]
    have hpos : 0 < ‖q‖ ^ 2 + 1 := by positivity
    field_simp
    ring
  have hpoint_integral : (∫ q : Plane, f 2 (Real.sqrt 2 • q)) =
      (1 / 4 : ℝ) * ∫ q : Plane, f 1 q := by
    calc
      (∫ q : Plane, f 2 (Real.sqrt 2 • q)) =
          ∫ q : Plane, (1 / 4 : ℝ) * f 1 q :=
            integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (1 / 4 : ℝ) * ∫ q : Plane, f 1 q := by rw [integral_const_mul]
  have hmass : (∫ q : Plane, f 2 q) = (1 / 2 : ℝ) * ∫ q : Plane, f 1 q := by
    rw [hpoint_integral] at hscaled
    nlinarith
  dsimp [gqt21_04_polarIntegral]
  rw [hmass]
  ring

/-- The planar resolvent integral scales inversely between positive parameters one and two rather than linearly. -/
theorem gqt21_04_printed_polar_integral_false :
    ¬ ∀ a : ℝ, 0 < a → gqt21_04_polarIntegral a = a / (4 * Real.pi) := by
  intro hprinted
  have hscale := gqt21_04_integral_scale
  rw [hprinted 2 (by norm_num), hprinted 1 (by norm_num)] at hscale
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi] at hscale
  norm_num at hscale

/-- For every constant `C`, the choice `α = exp C` contradicts the proposed Stirling bound. -/
theorem gqt21_08_printed_gamma_estimate_false (C : ℝ) (hC : 0 < C) :
    ∃ α : ℝ, 1 < α ∧
      ¬ Real.exp (-Real.log (Real.Gamma α)) ≤ (α / 2) * Real.log α - C * α := by
  have hExp : C + 1 < Real.exp C := Real.add_one_lt_exp hC.ne'
  refine ⟨Real.exp C, by linarith, ?_⟩
  intro h
  rw [Real.log_exp] at h
  have hleft : 0 < Real.exp (-Real.log (Real.Gamma (Real.exp C))) := Real.exp_pos _
  have hright : (Real.exp C / 2) * C - C * Real.exp C < 0 := by
    nlinarith [Real.exp_pos C, hC]
  linarith

/-- For positive times and `m = 1`, the reciprocal logarithm cannot bound a nonnegative norm multiplied by positive factors. -/
theorem gqt21_17_printed_rhs_negative (C lam β t : ℝ)
    (hC : 0 < C) (hlam : 2 ≤ lam) (ht : 0 < t) :
    C * (Real.log (min (t / 3) (1 / 2)))⁻¹ * (1 : ℝ) ^ 2 *
        Real.exp (lam * C * (β + 1) * t) * (C / Real.log lam) ^ (1 - 1 : ℕ) < 0 := by
  have hargpos : 0 < min (t / 3) (1 / 2) := lt_min (by positivity) (by norm_num)
  have harglt : min (t / 3) (1 / 2) < 1 :=
    (min_le_right _ _).trans_lt (by norm_num)
  have hlog : Real.log (min (t / 3) (1 / 2)) < 0 := Real.log_neg hargpos harglt
  have hInv : (Real.log (min (t / 3) (1 / 2)))⁻¹ < 0 := inv_lt_zero.mpr hlog
  have hlogLam : 0 < Real.log lam := Real.log_pos (by linarith)
  have hexp : 0 < Real.exp (lam * C * (β + 1) * t) := Real.exp_pos _
  have hpow : (C / Real.log lam) ^ (1 - 1 : ℕ) = 1 := by norm_num
  rw [hpow]
  norm_num only [one_pow, one_mul]
  have hCi : C * (Real.log (min (t / 3) (1 / 2)))⁻¹ < 0 :=
    mul_neg_of_pos_of_neg hC hInv
  have hprod : (C * (Real.log (min (t / 3) (1 / 2)))⁻¹) *
      Real.exp (lam * C * (β + 1) * t) < 0 := mul_neg_of_neg_of_pos hCi hexp
  simpa [mul_assoc] using hprod

/-- The `m = 1` instance of the printed operator-norm inequality is impossible:
an operator norm is nonnegative, while its displayed right side is negative.
-/
theorem gqt21_17_printed_norm_bound_impossible (A C lam β t : ℝ)
    (hA : 0 ≤ A) (hC : 0 < C) (hlam : 2 ≤ lam) (ht : 0 < t) :
    ¬ A ≤ C * (Real.log (min (t / 3) (1 / 2)))⁻¹ * (1 : ℝ) ^ 2 *
        Real.exp (lam * C * (β + 1) * t) * (C / Real.log lam) ^ (1 - 1 : ℕ) := by
  intro hbound
  have hrhs := gqt21_17_printed_rhs_negative C lam β t hC hlam ht
  linarith

end Critical2DKPZ.Errata.GQT21

