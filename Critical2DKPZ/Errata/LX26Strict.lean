/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.LX26
import Mathlib.Tactic

/-! # Logarithmic-mean normalization

LX26 Remark 2.11 is tested on a nonconstant Ehrhard-type law, and the logarithmic-mean normalization identity is proved. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.Errata

/-- Division of a standard Gaussian by its logarithmic exponential mean gives exponential mean `exp 2`. -/
theorem lx26_division_normalization_strict_counterexample :
    let P := gaussianReal 0 1
    IsEhrhardType P ∧
      (¬ ∃ c : ℝ, (fun x : ℝ => x) =ᵐ[P] fun _ => c) ∧
      Integrable (fun x : ℝ => Real.exp x) P ∧
      (∫ x : ℝ, Real.exp x ∂P) = Real.exp (1 / 2) ∧
      (∫ x : ℝ, Real.exp (x / Real.log (∫ y : ℝ, Real.exp y ∂P)) ∂P) =
        Real.exp 2 ∧ Real.exp (2 : ℝ) ≠ 1 := by
  dsimp only
  have hm : (∫ x : ℝ, Real.exp x ∂gaussianReal 0 1) = Real.exp (1 / 2) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) 1
    simpa [mgf] using h
  refine ⟨EhrhardType.isEhrhardType_standardGaussian, ?_, ?_, hm, ?_, ?_⟩
  · rintro ⟨c, hc⟩
    have hv := variance_congr hc
    have hvc : Var[fun _ : ℝ => c; gaussianReal 0 1] = 0 := by
      rw [variance_eq_integral (X := fun _ : ℝ => c) measurable_const.aemeasurable]
      simp
    rw [variance_fun_id_gaussianReal, hvc] at hv
    norm_num at hv
  · simpa only [one_mul] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) 1)
  · rw [hm, Real.log_exp]
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) 2
    norm_num only [mgf, zero_mul, NNReal.coe_one, mul_one, zero_add, OfNat.ofNat_ne_zero,
      div_eq_mul_inv, inv_div, inv_one] at h ⊢
    convert h using 1
    norm_num [div_eq_mul_inv, mul_comm]
  · exact ne_of_gt ((Real.one_lt_exp_iff).mpr (by norm_num))

/-- A normalized nonconstant Gaussian violates the two-sided comparison at orders minus one and one under total real division. -/
theorem lx26_order_one_strict_counterexample :
    let P := gaussianReal (-(1 / 2 : ℝ)) 1
    IsEhrhardType P ∧
      (¬ ∃ c : ℝ, (fun x : ℝ => x) =ᵐ[P] fun _ => c) ∧
      Integrable id P ∧ (∀ r : ℝ, Integrable (fun x => Real.exp (r * x)) P) ∧
      (∫ x : ℝ, Real.exp x ∂P) = 1 ∧
      ∃ p q : ℝ, p < 0 ∧ 0 < q ∧
        ¬ (-(Real.log (∫ x : ℝ, Real.exp (q * x) ∂P)) / (q * (q - 1)) ≤
            ∫ x : ℝ, x ∂P ∧
          (∫ x : ℝ, x ∂P) ≤
            -(Real.log (∫ x : ℝ, Real.exp (p * x) ∂P)) / (p * (p - 1))) := by
  dsimp only
  obtain ⟨hE, hi, _, hm, hfalse⟩ := lx26_order_one_mean_bound_counterexample
  refine ⟨hE, ?_, hi, ?_, hm, -1, 1, by norm_num, by norm_num, ?_⟩
  · rintro ⟨c, hc⟩
    have hv := variance_congr hc
    have hvc : Var[fun _ : ℝ => c; gaussianReal (-(1 / 2 : ℝ)) 1] = 0 := by
      rw [variance_eq_integral (X := fun _ : ℝ => c) measurable_const.aemeasurable]
      simp
    rw [variance_fun_id_gaussianReal, hvc] at hv
    norm_num at hv
  · intro r
    exact integrable_exp_mul_gaussianReal r
  · intro hh
    exact hfalse (by simpa only [one_mul] using hh.1)

/-- Subtracting the logarithmic exponential mean normalizes any random variable with integrable exponential. -/
theorem lx26_translation_normalization_strict {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Integrable (fun ω => Real.exp (X ω)) P) :
    0 < (∫ ω, Real.exp (X ω) ∂P) ∧
      Integrable (fun ω => Real.exp (X ω - Real.log (∫ η, Real.exp (X η) ∂P))) P ∧
      (∫ ω, Real.exp (X ω - Real.log (∫ η, Real.exp (X η) ∂P)) ∂P) = 1 := by
  have hpos := integral_exp_pos hX
  have heq : (fun ω => Real.exp (X ω - Real.log (∫ η, Real.exp (X η) ∂P))) =
      fun ω => Real.exp (X ω) / (∫ η, Real.exp (X η) ∂P) := by
    funext ω
    rw [Real.exp_sub, Real.exp_log hpos]
  rw [heq]
  exact ⟨hpos, hX.div_const _, by rw [integral_div, div_self hpos.ne']⟩

end Critical2DKPZ.Errata
