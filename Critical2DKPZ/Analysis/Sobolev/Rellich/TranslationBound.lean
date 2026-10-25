/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Defs
public import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A quantitative bound on the Fourier character near the origin.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich


/-- **The phase estimate.**  `‖𝐞 t − 1‖ ≤ 4π|t|` for `2π|t| ≤ 1`, from
`Complex.norm_exp_sub_one_le`.  This is the small-frequency bound that makes the phase factor of
the translation identity vanish as `h → 0`. -/
theorem norm_fourierChar_sub_one_le {t : ℝ} (ht : 2 * Real.pi * |t| ≤ 1) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ 4 * Real.pi * |t| := by
  rw [Real.fourierChar_apply', Circle.coe_exp]
  have hx : ‖(((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one,
      show ‖(((2 * Real.pi * t : ℝ)) : ℂ)‖ = |2 * Real.pi * t| from by simp,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact ht
  refine (Complex.norm_exp_sub_one_le hx).trans ?_
  rw [Complex.norm_mul, Complex.norm_I, mul_one,
    show ‖(((2 * Real.pi * t : ℝ)) : ℂ)‖ = |2 * Real.pi * t| from by simp,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  exact le_of_eq (by ring)


end Critical2DKPZ.Analysis.Sobolev.Rellich

end
