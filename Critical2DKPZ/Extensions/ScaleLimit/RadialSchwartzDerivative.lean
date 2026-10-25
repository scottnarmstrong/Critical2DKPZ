/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzSpectralLp
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic

/-! # The radial derivative of a planar Schwartz function -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Evaluation of the Schwartz differential against the identity vector
field preserves Schwartz decay by the temperate multiplier theorem. -/
def radialSchwartzDerivative (m : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip
    (ContinuousLinearMap.id ℝ Plane).hasTemperateGrowth (SchwartzMap.fderivCLM ℝ Plane ℂ m)

/-- The radial Schwartz derivative has its literal differential value. -/
theorem radialSchwartzDerivative_apply (m : SchwartzMap Plane ℂ) (ξ : Plane) :
    radialSchwartzDerivative m ξ = fderiv ℝ m ξ ξ := rfl

/-- Differentiating a Schwartz shape along a nonzero radial scale. -/
theorem hasDerivAt_schwartz_radial (m : SchwartzMap Plane ℂ)
    (ξ : Plane) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => m (t • ξ)) (r⁻¹ • radialSchwartzDerivative m (r • ξ)) r := by
  have hs : HasDerivAt (fun t : ℝ => t • ξ) ξ r := by
    convert (hasDerivAt_id r).smul_const ξ using 1 <;> simp only [id_eq, one_smul]
  have hd := m.hasFDerivAt (r • ξ)
  have hh := hd.comp_hasDerivAt r hs
  have heq : r⁻¹ • radialSchwartzDerivative m (r • ξ) = fderiv ℝ m (r • ξ) ξ := by
    rw [radialSchwartzDerivative_apply, map_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]
  rw [heq]
  exact hh

end Critical2DKPZ.Extensions.ScaleLimit
