/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.TimeBlocks
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

/-! # Resampling independent time slabs in discrepancy moment expansions -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Blocks

/-- A block-measurable function is unchanged when its block is kept during resampling. -/
theorem blockMeasurable_resample_keep {a b : ℕ} {F : Disorder → ℝ}
    (hF : Measurable[Gaussian.disorderBlock a b] F) (ω η : Disorder) :
    F (Gaussian.resample (Gaussian.timeBlock a b) ω η) = F ω := by
  change Measurable[MeasurableSpace.comap
    (fun ξ (j : Gaussian.timeBlock a b) => ξ j) inferInstance] F at hF
  apply hF.factorsThrough
  funext j
  simp only [Gaussian.resample, j.property, ite_true]

/-- A function of an earlier block is copied from the other sample when a later block is kept. -/
theorem blockMeasurable_resample_earlier {a b c d : ℕ} {F : Disorder → ℝ}
    (hbc : b ≤ c) (hF : Measurable[Gaussian.disorderBlock a b] F) (ω η : Disorder) :
    F (Gaussian.resample (Gaussian.timeBlock c d) ω η) = F η := by
  change Measurable[MeasurableSpace.comap
    (fun ξ (j : Gaussian.timeBlock a b) => ξ j) inferInstance] F at hF
  apply hF.factorsThrough
  funext j
  have hj : (j : ℕ × Site) ∉ Gaussian.timeBlock c d := by
    intro hj
    exact (not_lt_of_ge (j.property.2.trans hbc)) hj.1
  simp only [Gaussian.resample, hj, ite_false]

/-- Averaging a resampled block and its complement preserves the full disorder integral. -/
theorem integral_integral_resample_block (a b : ℕ) (F : Disorder → ℝ)
    (hm : Measurable F) (hF : Integrable F disorderLaw) :
    (∫ ω, ∫ η, F (Gaussian.resample (Gaussian.timeBlock a b) ω η)
      ∂disorderLaw ∂disorderLaw) = ∫ ω, F ω ∂disorderLaw := by
  have hce := Gaussian.condExp_disorderBlock_ae_eq a b hm hF
  calc
    _ = ∫ ω, disorderLaw[F | Gaussian.disorderBlock a b] ω ∂disorderLaw :=
      (integral_congr_ae hce).symm
    _ = _ := integral_condExp (Gaussian.disorderBlock_le a b)

end Critical2DKPZ.Blocks
