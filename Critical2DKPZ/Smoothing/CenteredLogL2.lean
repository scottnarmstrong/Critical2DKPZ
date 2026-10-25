/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Centering is an `L²` contraction up to a factor of two -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Smoothing

/-- On a probability space, subtracting the mean of a square-integrable function `G` from `F` costs at most the sum of their `L²` seminorms. -/
theorem eLpNorm_sub_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F G : Ω → ℝ) (hG : MemLp G 2 μ) :
    eLpNorm (fun ω => F ω - (∫ ω', G ω' ∂μ)) 2 μ ≤
      eLpNorm F 2 μ + eLpNorm G 2 μ := by
  have hG1 : eLpNorm G 1 μ ≤ eLpNorm G 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hmean : ‖∫ ω, G ω ∂μ‖ₑ ≤ eLpNorm G 2 μ := by
    calc
      _ ≤ ∫⁻ ω, ‖G ω‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm G 1 μ := (eLpNorm_one_eq_lintegral_enorm
        hG.aestronglyMeasurable).symm
      _ ≤ eLpNorm G 2 μ := hG1
  have hconst : eLpNorm (fun _ : Ω => ∫ ω, G ω ∂μ) 2 μ =
      ‖∫ ω, G ω ∂μ‖ₑ := by
    rw [eLpNorm_const (∫ ω, G ω ∂μ) (by norm_num) (by
      intro hzero
      have := congrArg (fun ν : Measure Ω => ν Set.univ) hzero
      simp only [measure_univ] at this
      norm_num at this)]
    simp [measure_univ]
  calc
    _ ≤ eLpNorm F 2 μ + eLpNorm (fun _ : Ω => ∫ ω, G ω ∂μ) 2 μ :=
      eLpNorm_sub_le (by norm_num)
    _ ≤ eLpNorm F 2 μ + eLpNorm G 2 μ := add_le_add le_rfl (hconst ▸ hmean)

/-- On a probability space, subtracting the mean costs at most a factor two in the `L²`
seminorm. -/
theorem eLpNorm_sub_integral_le_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    eLpNorm (fun ω => F ω - (∫ ω', F ω' ∂μ)) 2 μ ≤ 2 * eLpNorm F 2 μ := by
  calc
    _ ≤ eLpNorm F 2 μ + eLpNorm F 2 μ := eLpNorm_sub_integral_le μ F F hF
    _ = 2 * eLpNorm F 2 μ := by ring

/-- The difference of two centered fields is controlled by the uncentered difference. Both fields
are assumed square integrable, which makes their centerings well-defined as Bochner integrals. -/
theorem eLpNorm_centered_sub_le_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F G : Ω → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    eLpNorm (fun ω => (F ω - (∫ ω', F ω' ∂μ)) - (G ω - (∫ ω', G ω' ∂μ))) 2 μ ≤
      2 * eLpNorm (fun ω => F ω - G ω) 2 μ := by
  have hD : MemLp (fun ω => F ω - G ω) 2 μ := hF.sub hG
  have hcenter :
      (fun ω => (F ω - (∫ ω', F ω' ∂μ)) - (G ω - (∫ ω', G ω' ∂μ))) =
        fun ω => (F ω - G ω) - (∫ ω', (F ω' - G ω') ∂μ) := by
    funext ω
    rw [integral_sub (hF.integrable (by norm_num)) (hG.integrable (by norm_num))]
    ring
  rw [hcenter]
  exact eLpNorm_sub_integral_le_two μ (fun ω => F ω - G ω) hD

end Critical2DKPZ.Smoothing

end
