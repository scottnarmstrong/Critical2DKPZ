/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic

/-! # Uniqueness of Laplace transforms on the positive half-line -/

@[expose] public section

open MeasureTheory Set
open scoped ProbabilityTheory ENNReal

namespace Critical2DKPZ.Analysis


/-- Finite measures on the line are determined by their real moment generating
functions on any open interval containing zero. Analytic continuation gives
equality of characteristic functions. -/
theorem measure_eq_of_mgf_eq_on_Ioo {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ} (hε : 0 < ε)
    (hμ : Ioo (-ε) ε ⊆ interior (ProbabilityTheory.integrableExpSet id μ))
    (hν : Ioo (-ε) ε ⊆ interior (ProbabilityTheory.integrableExpSet id ν))
    (hm : ∀ t ∈ Ioo (-ε) ε,
      ProbabilityTheory.mgf id μ t = ProbabilityTheory.mgf id ν t) : μ = ν := by
  let U : Set ℂ := {z | z.re ∈ Ioo (-ε) ε}
  have hAnalyticμ : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id μ) U := by
    apply ProbabilityTheory.analyticOnNhd_complexMGF.mono
    intro z hz
    exact hμ hz
  have hAnalyticν : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ν) U := by
    apply ProbabilityTheory.analyticOnNhd_complexMGF.mono
    intro z hz
    exact hν hz
  have hUconvex : Convex ℝ U := by
    intro z hz w hw a b ha hb hab
    change -ε < z.re ∧ z.re < ε at hz
    change -ε < w.re ∧ w.re < ε at hw
    change -ε < (a • z + b • w).re ∧ (a • z + b • w).re < ε
    have hza : (a • z).re = a * z.re := by simp [Complex.mul_re]
    have hwb : (b • w).re = b * w.re := by simp [Complex.mul_re]
    rw [Complex.add_re, hza, hwb]
    constructor
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1]
        simpa using hw.1
      · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hza' := mul_lt_mul_of_pos_left hz.1 haPos
        have hwb' := mul_le_mul_of_nonneg_left hw.1.le hb
        have hsum : a * (-ε) + b * (-ε) = -ε := by rw [← add_mul, hab]; ring
        linarith
    · by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1]
        simpa using hw.2
      · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hza' := mul_lt_mul_of_pos_left hz.2 haPos
        have hwb' := mul_le_mul_of_nonneg_left hw.2.le hb
        have hsum : a * ε + b * ε = ε := by rw [← add_mul, hab]; ring
        linarith
  have hU : IsPreconnected U := hUconvex.isPreconnected
  have hzeroU : (0 : ℂ) ∈ U := by simp [U, hε]
  have hcl : (0 : ℂ) ∈ closure
      ({z : ℂ | ProbabilityTheory.complexMGF id μ z =
        ProbabilityTheory.complexMGF id ν z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    let r := min δ ε
    let t : ℝ := r / 2
    have hr : 0 < r := lt_min hδ hε
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : t < ε := by
      dsimp [t]
      exact (half_lt_self hr).trans_le (min_le_right δ ε)
    have htδ : t < δ := by
      dsimp [t]
      exact (half_lt_self hr).trans_le (min_le_left δ ε)
    have htin : t ∈ Ioo (-ε) ε := ⟨by linarith, htε⟩
    refine ⟨(t : ℂ), ⟨?_, ?_⟩, ?_⟩
    · change ProbabilityTheory.complexMGF id μ (t : ℂ) =
        ProbabilityTheory.complexMGF id ν (t : ℂ)
      rw [ProbabilityTheory.complexMGF_ofReal, ProbabilityTheory.complexMGF_ofReal]
      exact congrArg Complex.ofReal (hm t htin)
    · change (t : ℂ) ≠ 0
      exact_mod_cast (ne_of_gt ht)
    · have htNorm : ‖(t : ℂ)‖ < δ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
        exact htδ
      simpa [dist_eq_norm] using htNorm
  have hfreq := mem_closure_ne_iff_frequently_within.mp hcl
  have hEqOn := hAnalyticμ.eqOn_of_preconnected_of_frequently_eq hAnalyticν hU hzeroU hfreq
  have hchar : MeasureTheory.charFun μ = MeasureTheory.charFun ν := by
    funext t
    rw [← ProbabilityTheory.complexMGF_id_mul_I, ← ProbabilityTheory.complexMGF_id_mul_I]
    exact hEqOn (by simp [U, hε])
  exact Measure.ext_of_charFun hchar

end Critical2DKPZ.Analysis

end
