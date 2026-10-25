/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioExpansion
import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Tactic

/-! # Reciprocal block-mass expectation -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The expected reciprocal of a normalized block mass is at least one. -/
theorem one_le_integral_inv_blockMass (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    1 ≤ ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
  let Z : Disorder → ℝ := blockMass β t i
  have hZpos (ω : Disorder) : 0 < Z ω := by
    exact blockMass_pos β t i ω
  have hmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z, blockMass]
    exact Polymer.integral_smoothedP2Plane β (t (i - 1)) (t i) 0
  have hZint : Integrable Z disorderLaw := integrable_of_integral_eq_one hmean
  have hInvPow : Integrable (fun ω => Z ω ^ (-1 : ℝ)) disorderLaw := by
    simpa [Z, blockMass] using
      integrable_rpow_smoothedP2Plane β (t (i - 1)) (t i) 0 (-1)
  have hInvEq : (fun ω => (Z ω)⁻¹) = fun ω => Z ω ^ (-1 : ℝ) := by
    funext ω
    rw [Real.rpow_neg_one]
  have hInvInt : Integrable (fun ω => (Z ω)⁻¹) disorderLaw := hInvEq.symm ▸ hInvPow
  have hlinearInt : Integrable (fun ω => 2 - Z ω) disorderLaw :=
    (integrable_const (2 : ℝ)).sub hZint
  have hpoint (ω : Disorder) : 2 - Z ω ≤ (Z ω)⁻¹ := by
    have hsquare : 0 ≤ (Z ω - 1) ^ 2 / Z ω :=
      div_nonneg (sq_nonneg _) (le_of_lt (hZpos ω))
    have halgebra : (Z ω - 1) ^ 2 / Z ω = Z ω + (Z ω)⁻¹ - 2 := by
      field_simp [ne_of_gt (hZpos ω)]
      ring
    rw [halgebra] at hsquare
    linarith
  have hmono := integral_mono hlinearInt hInvInt hpoint
  have hlinear : ∫ ω, (2 - Z ω) ∂disorderLaw = 1 := by
    rw [integral_sub (integrable_const (2 : ℝ)) hZint, hmean]
    norm_num
  calc
    1 = ∫ ω, (2 - Z ω) ∂disorderLaw := hlinear.symm
    _ ≤ ∫ ω, (Z ω)⁻¹ ∂disorderLaw := hmono
    _ = ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by rfl

end Critical2DKPZ.OnePoint

end
