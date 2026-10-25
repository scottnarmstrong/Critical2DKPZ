/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.TranslationBound
import Mathlib.Tactic.NormNum

/-! The Fourier character differs from one by at most two in norm, providing a uniform bound at high frequencies.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open scoped FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- The Fourier character differs from one by at most two in norm. -/
theorem norm_fourierChar_sub_one_le_two (t : ℝ) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ 2 := by
  calc ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ ‖((𝐞 t : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
