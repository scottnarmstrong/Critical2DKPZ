/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.FMP25
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! # Affine normalized Gaussian logarithmic moments

A nondegenerate Gaussian satisfies the upper-tail concavity assumption of FMP25 Theorem 3.1 and has an affine normalized logarithmic moment on `[1, 3]`, with positive integrable exponential moments. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Critical2DKPZ.Errata

/-- The standard Gaussian satisfies the printed tail hypothesis but refutes unconditional strict convexity away from zero. -/
theorem gaussian_normalized_logMoment_not_strictConvex :
    let P := gaussianReal 0 1
    ConcaveOn ℝ univ (fun t : ℝ => Ehrhard.gaussianCDFChart.symm
      ((P {x : ℝ | t < x}).toReal)) ∧
      (∀ t : ℝ, 0 < (P {x : ℝ | t < x}).toReal ∧
        (P {x : ℝ | t < x}).toReal < 1) ∧
      (∀ p ∈ Icc (1 : ℝ) 3, Integrable (fun x : ℝ => Real.exp (p * x)) P ∧
        0 < ∫ x : ℝ, Real.exp (p * x) ∂P) ∧
      ¬ StrictConvexOn ℝ (Icc (1 : ℝ) 3)
        (fun p : ℝ => Real.log (∫ x : ℝ, Real.exp (p * x) ∂P) / p) := by
  dsimp only
  have hq : (fun t : ℝ => Ehrhard.gaussianCDFChart.symm
      (((gaussianReal 0 1) {x : ℝ | t < x}).toReal)) = fun t => -t := by
    funext t
    simpa only [one_mul, add_zero, zero_sub, div_one] using
      fmp25_upper_tail_quantile (σ := 1) (by norm_num) 0 t
  have hm (p : ℝ) : (∫ x : ℝ, Real.exp (p * x) ∂gaussianReal 0 1) =
      Real.exp (p ^ 2 / 2) := by
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) p
    simpa [mgf] using h
  have hΛ (p : ℝ) (hp : 0 < p) :
      Real.log (∫ x : ℝ, Real.exp (p * x) ∂gaussianReal 0 1) / p = p / 2 := by
    rw [hm, Real.log_exp]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq]
    exact (convexOn_id (𝕜 := ℝ) convex_univ).neg
  · intro t
    have htail := Ehrhard.gaussian_tail_neg_eq_CDF (-t)
    simp only [neg_neg] at htail
    change ((gaussianReal 0 1) (Ioi t)).toReal > 0 ∧
      ((gaussianReal 0 1) (Ioi t)).toReal < 1
    rw [htail]
    exact ⟨Ehrhard.gaussianCDF_pos _, Ehrhard.gaussianCDF_lt_one _⟩
  · intro p _
    exact ⟨integrable_exp_mul_gaussianReal p, by rw [hm]; exact Real.exp_pos _⟩
  · intro h
    have hstrict := h.2
    have hh := hstrict (x := 1) (by norm_num) (y := 3) (by norm_num)
      (by norm_num) (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [show (1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 3 = 2 by norm_num,
      hΛ 2 (by norm_num), hΛ 1 (by norm_num), hΛ 3 (by norm_num)] at hh
    norm_num at hh

end Critical2DKPZ.Errata
