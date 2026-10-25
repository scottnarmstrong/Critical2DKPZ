/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.Positivity

/-! Changing from unitary to angular Fourier coordinates introduces the planar factor `(2π)⁻²`, including for infinite nonnegative energies. -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ

/-- In dimension two the factor `(2π)⁻²` cancels exactly the angular-frequency Jacobian. -/
theorem lintegral_angular_frequency_scaling {H : Plane → ℝ≥0∞} (hH : Measurable H) :
    ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
      (∫⁻ ξ : Plane, H ((2 * Real.pi)⁻¹ • ξ)) = ∫⁻ ξ : Plane, H ξ := by
  have hs : Measurable (fun ξ : Plane => (2 * Real.pi)⁻¹ • ξ) :=
    ((continuous_id : Continuous (fun ξ : Plane => ξ)).const_smul ((2 * Real.pi)⁻¹ : ℝ)).measurable
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hc : ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
      ENNReal.ofReal |(((2 * Real.pi)⁻¹) ^ 2)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  rw [← lintegral_map hH hs, Measure.map_addHaar_smul volume
    (by positivity : (2 * Real.pi)⁻¹ ≠ 0), hd, lintegral_smul_measure,
    smul_eq_mul, ← mul_assoc, hc, one_mul]

end Critical2DKPZ

end
