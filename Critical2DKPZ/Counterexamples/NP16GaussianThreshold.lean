/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Ehrhard.ScalarOUProfile
import Mathlib.Tactic

/-! # Gaussian exponential and distribution-function thresholds -/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Critical2DKPZ.Errata

/-- The half-probability Gaussian sublevel equals the nonpositive quantile sublevel for every finite input. -/
theorem gaussianCDF_le_half_iff_and_not_le_zero (z : ℝ) :
    (Ehrhard.gaussianCDF z ≤ (1 / 2 : ℝ) ↔ z ≤ 0) ∧
      ¬ Ehrhard.gaussianCDF z ≤ 0 := by
  have htail := Ehrhard.gaussian_tail_neg_eq_CDF 0
  have hcompl := MeasureTheory.probReal_compl_eq_one_sub
    (μ := ProbabilityTheory.gaussianReal 0 1) (s := Set.Iic (0 : ℝ)) measurableSet_Iic
  have hz : Ehrhard.gaussianCDF 0 = (1 / 2 : ℝ) := by
    simp only [Set.compl_Iic] at hcompl
    simp only [neg_zero] at htail
    rw [Ehrhard.gaussianCDF, ProbabilityTheory.cdf_eq_real] at htail ⊢
    change (ProbabilityTheory.gaussianReal 0 1).real (Set.Ioi 0) =
      (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic 0) at htail
    linarith
  constructor
  · rw [← hz]
    exact Ehrhard.strictMono_gaussianCDF.le_iff_le
  · exact not_le_of_gt (Ehrhard.gaussianCDF_pos z)

end Critical2DKPZ.Errata
