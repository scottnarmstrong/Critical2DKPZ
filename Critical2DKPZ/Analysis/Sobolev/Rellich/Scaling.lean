/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quadratic homogeneity of the squared Fourier-side Sobolev norm.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Scaling a test function by a real constant scales its squared Sobolev norm by the square of that constant. -/
theorem sobolevNormSq_const_mul (d : ℕ) (s c : ℝ) (φ : Space d → ℝ) :
    sobolevNormSq d s (fun x => c * φ x) = ENNReal.ofReal (c ^ 2) * sobolevNormSq d s φ := by
  rw [sobolevNormSq, sobolevNormSq]
  have hpt : ∀ ξ : Space d,
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => ((c * φ x : ℝ) : ℂ)) ξ‖ ^ 2)
        = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    have hf : 𝓕 (fun x : Space d => ((c * φ x : ℝ) : ℂ)) ξ = (c : ℂ) * 𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ := by
      rw [Real.fourier_eq, Real.fourier_eq]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      rw [Circle.smul_def, Circle.smul_def, Complex.ofReal_mul]
      ring
    rw [hf, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c ^ 2)]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (|c| * ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖) ^ 2
        = c ^ 2 * ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2 by rw [mul_pow, sq_abs]]
    ring
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
