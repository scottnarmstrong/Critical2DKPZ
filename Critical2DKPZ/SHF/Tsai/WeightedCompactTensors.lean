/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Tsai.CenteredKernel
import Critical2DKPZ.SHF.Flow.WeightMeasurability
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Finite weighted Lᵖ norms of compact configuration tensors

A finite tensor of compact endpoint tests has compact support in configuration
space. Multiplication by the continuous exponential configuration weight
therefore preserves membership in every Lᵖ space, including p = infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A finite configuration tensor of compact endpoint tests has compact support. -/
theorem hasCompactSupport_configurationTensor {n : ℕ} (g : Fin n → C_c(Plane, ℝ)) :
    HasCompactSupport (fun x : Configuration n => ∏ i, g i (x i)) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun i => (g i).hasCompactSupport))
  intro x hx i _hi
  apply subset_tsupport
  exact Finset.prod_ne_zero_iff.1 hx i (Finset.mem_univ i)

/-- The exponential-weighted compact configuration tensor belongs to every Lᵖ space. -/
theorem memLp_exp_weighted_configurationTensor {n : ℕ} (a : ℝ) (p : ℝ≥0∞)
    (g : Fin n → C_c(Plane, ℝ)) :
    MemLp (fun x : Configuration n => Real.exp (a * configL1Norm x) * ∏ i, g i (x i)) p := by
  have hTensor : Continuous (fun x : Configuration n => ∏ i, g i (x i)) :=
    continuous_finsetProd _ (fun i _ => (g i).continuous.comp (continuous_apply i))
  have hWeight : Continuous (fun x : Configuration n => Real.exp (a * configL1Norm x)) :=
    Real.continuous_exp.comp (continuous_const.mul (Flow.continuous_configurationOneNorm n))
  exact (hWeight.mul hTensor).memLp_of_hasCompactSupport
    (hasCompactSupport_configurationTensor g).mul_left

end Critical2DKPZ.SHF.Tsai

end
