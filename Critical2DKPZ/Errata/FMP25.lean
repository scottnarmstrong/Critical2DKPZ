/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.ScalarOUProfile
public import Mathlib.Analysis.Convex.Function

/-! # Gaussian upper tails

The Gaussian upper-tail comparison in FMP25 Theorem 3.1 and Lemma 3.1 is evaluated at probabilities strictly between zero and one. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Critical2DKPZ.Errata

/-- The upper-tail quantile of an affine Gaussian has the opposite sign from its lower-tail quantile. -/
theorem fmp25_upper_tail_quantile {σ : ℝ} (hσ : 0 < σ) (μ t : ℝ) :
    Ehrhard.gaussianCDFChart.symm
      (((gaussianReal 0 1) {z : ℝ | t < σ * z + μ}).toReal) = (μ - t) / σ := by
  have hs : {z : ℝ | t < σ * z + μ} = Ioi (-((μ - t) / σ)) := by
    ext z
    simp only [mem_ofPred_eq, mem_Ioi]
    rw [show -((μ - t) / σ) = (t - μ) / σ by ring, div_lt_iff₀ hσ]
    constructor <;> intro h <;> linarith
  rw [hs, Ehrhard.gaussian_tail_neg_eq_CDF]
  exact Ehrhard.gaussianCDFChart.left_inv (by trivial)

/-- The normalized logarithmic moment of the constant Gaussian variable zero is not strictly convex. -/
theorem fmp25_zero_logMoment_not_strictConvex :
    ¬ StrictConvexOn ℝ (Ioi (0 : ℝ))
      (fun p : ℝ => Real.log (∫ _z : ℝ, Real.exp (p * 0) ∂gaussianReal 0 1) / p) := by
  intro h
  have hh := h.2
  have hlt := hh (x := 1) (by norm_num) (y := 2) (by norm_num)
    (by norm_num) (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hlt

/-- A constant concave function has a Gaussian superlevel probability of one, outside the range of finite Gaussian quantiles. -/
theorem fmp25_constant_superlevel_endpoint :
    ConcaveOn ℝ (univ : Set ℝ) (fun _ : ℝ => (0 : ℝ)) ∧
      ((gaussianReal 0 1) {z : ℝ | (-1 : ℝ) < (fun _ : ℝ => (0 : ℝ)) z}).toReal = 1 ∧
      ¬ ∃ q : ℝ, Ehrhard.gaussianCDF q = 1 := by
  refine ⟨concaveOn_const 0 convex_univ, ?_, ?_⟩
  · simp
  · rintro ⟨q, hq⟩
    exact (ne_of_lt (Ehrhard.gaussianCDF_lt_one q)) hq

end Critical2DKPZ.Errata

end
