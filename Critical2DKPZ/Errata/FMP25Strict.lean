/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.FMP25
public import Mathlib.Order.WithBot
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-! # Gaussian quantiles at the top endpoint

The codomain `WithBot ℝ` in the concave-superlevel branch of FMP25 Lemma 3.1 includes the lower infinite endpoint but has no value whose Gaussian distribution function is one. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Critical2DKPZ.Errata

/-- The Gaussian CDF on exactly the codomain printed in FMP25 Lemma 3.1. -/
def fmp25PrintedCDF : WithBot ℝ → ℝ :=
  WithBot.recBotCoe 0 Ehrhard.gaussianCDF

/-- The superlevel probability of a constant concave function is outside the Gaussian CDF image of `WithBot ℝ`. -/
theorem fmp25_superlevel_codomain_strict_counterexample :
    let γ := gaussianReal 0 1
    let f : ℝ → ℝ := fun _ => 0
    IsGaussian γ ∧ ConcaveOn ℝ univ f ∧
      γ {x | (-1 : ℝ) < f x} = 1 ∧
      ¬ ∃ q : WithBot ℝ, fmp25PrintedCDF q = (γ {x | (-1 : ℝ) < f x}).toReal := by
  dsimp only
  refine ⟨inferInstance, concaveOn_const 0 convex_univ, by simp, ?_⟩
  simp only [show {x : ℝ | (-1 : ℝ) < (0 : ℝ)} = univ by ext; simp,
    measure_univ, ENNReal.toReal_one]
  rintro ⟨q, hq⟩
  induction q using WithBot.recBotCoe with
  | bot => norm_num [fmp25PrintedCDF] at hq
  | coe q => exact (ne_of_lt (Ehrhard.gaussianCDF_lt_one q)) hq

/-- The standard Gaussian satisfies the upper-quantile and two-moment hypotheses while its proposed quantile identity fails. -/
theorem fmp25_upper_quantile_sign_strict_counterexample :
    let γ := gaussianReal 0 1
    let Λ : ℝ → ℝ := fun p => Real.log (∫ x : ℝ, Real.exp (p * x) ∂γ) / p
    let Q : ℝ → ℝ := fun t => Ehrhard.gaussianCDFChart.symm ((γ (Set.Ioi t)).toReal)
    IsGaussian γ ∧
      (∀ p : ℝ, Integrable (fun x : ℝ => Real.exp (p * x)) γ) ∧
      ConcaveOn ℝ Set.univ Q ∧ Λ 1 = 1 / 2 ∧ Λ 2 = 1 ∧
      (2 * Λ 1 - Λ 2) / (2 - 1) = 0 ∧
      2 * (Λ 2 - Λ 1) / (2 - 1) = 1 ∧
      ¬ (Q 1 - Q 1 = Q 1 - (1 - (0 : ℝ)) / 1) := by
  dsimp only
  have hQ (t : ℝ) :
      Ehrhard.gaussianCDFChart.symm (((gaussianReal 0 1) (Set.Ioi t)).toReal) = -t := by
    simpa only [one_mul, add_zero, zero_sub, div_one, Set.Ioi_def] using
      fmp25_upper_tail_quantile (by norm_num : (0 : ℝ) < 1) 0 t
  have hm (p : ℝ) : (∫ x : ℝ, Real.exp (p * x) ∂gaussianReal 0 1) = Real.exp (p ^ 2 / 2) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) p
    simpa [mgf] using h
  have h1 : Real.log (∫ x : ℝ, Real.exp ((1 : ℝ) * x) ∂gaussianReal 0 1) / 1 = 1 / 2 := by
    rw [hm, Real.log_exp]
    norm_num
  have h2 : Real.log (∫ x : ℝ, Real.exp ((2 : ℝ) * x) ∂gaussianReal 0 1) / 2 = 1 := by
    rw [hm, Real.log_exp]
    norm_num
  refine ⟨inferInstance, (fun p => integrable_exp_mul_gaussianReal p), ?_, h1, h2, ?_, ?_, ?_⟩
  · have heq : (fun t : ℝ => Ehrhard.gaussianCDFChart.symm
        (((gaussianReal 0 1) (Set.Ioi t)).toReal)) = fun t => -t := funext hQ
    rw [heq]
    exact (convexOn_id convex_univ : ConvexOn ℝ Set.univ (fun x : ℝ => x)).neg
  · rw [h1, h2]
    norm_num
  · rw [h1, h2]
    norm_num
  · rw [hQ]
    norm_num

end Critical2DKPZ.Errata
