/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Basic
public import Critical2DKPZ.Analysis.Sobolev.Rellich.Scaling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The squared Sobolev norm of a sum of integrable functions is at most twice the sum of their squared norms.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Additivity of the Fourier integral for integrable functions. -/
private theorem fourier_add_of_integrable {d : ℕ} {f g : Space d → ℝ}
    (hf : Integrable (fun x => (f x : ℂ))) (hg : Integrable (fun x => (g x : ℂ)))
    (ξ : Space d) :
    𝓕 (fun x => ((f x + g x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (f x : ℂ)) ξ + 𝓕 (fun x => (g x : ℂ)) ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  rw [← integral_add]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Circle.smul_def, Complex.ofReal_add]
    ring
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr hf
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr hg

/-- `2 * ofReal x = ofReal (2 * x)` on `ℝ≥0∞`. -/
private theorem ofReal_two_mul (x : ℝ) :
    ENNReal.ofReal (2 * x) = 2 * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- The base of the Sobolev weight is positive. -/
private theorem sobolevWeight_pos {d : ℕ} (x : Space d) :
    (0 : ℝ) < 1 + (2 * Real.pi * ‖x‖) ^ 2 := by
  nlinarith [sq_nonneg (2 * Real.pi * ‖x‖)]

/-- The Sobolev weight is continuous. -/
private theorem continuous_sobolevWeight {d : ℕ} (s : ℝ) :
    Continuous fun ξ : Space d => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s :=
  (continuous_const.add (((continuous_const : Continuous fun _ : Space d => (2 * Real.pi : ℝ)).mul
    continuous_norm).pow 2)).rpow_const (fun x => Or.inl (sobolevWeight_pos x).ne')

/-- The integrand of the Sobolev norm is measurable for an integrable function. -/
private theorem measurable_sobolevWeight {d : ℕ} (s : ℝ) (h : Space d → ℂ) (hh : Integrable h) :
    Measurable fun ξ : Space d => ENNReal.ofReal
      ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 h ξ‖ ^ 2) := by
  apply ENNReal.measurable_ofReal.comp
  exact ((continuous_sobolevWeight s).mul
    (((VectorFourier.fourierIntegral_continuous (L := innerₗ (Space d))
      Real.continuous_fourierChar continuous_inner hh).norm).pow 2)).measurable

/-- For integrable functions, the squared Sobolev norm of their sum is at most twice the sum of their squared norms. -/
theorem sobolevNormSq_add_le (d : ℕ) (s : ℝ) (f g : Space d → ℝ)
    (hf : Integrable (fun x => (f x : ℂ))) (hg : Integrable (fun x => (g x : ℂ))) :
    sobolevNormSq d s (fun x => f x + g x)
      ≤ 2 * sobolevNormSq d s f + 2 * sobolevNormSq d s g := by
  unfold sobolevNormSq
  have hpt : ∀ ξ : Space d,
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
          * ‖𝓕 (fun x => ((f x + g x : ℝ) : ℂ)) ξ‖ ^ 2)
        ≤ 2 * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2)
          + 2 * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    rw [fourier_add_of_integrable hf hg ξ]
    set w : ℝ := (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s with hw
    set A : ℂ := 𝓕 (fun x => (f x : ℂ)) ξ with hA
    set B : ℂ := 𝓕 (fun x => (g x : ℂ)) ξ with hB
    have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) s
    have hsq : (‖A‖ + ‖B‖) ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
    have htri : ‖A + B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by
      have := norm_add_le A B
      nlinarith [norm_nonneg (A + B), add_nonneg (norm_nonneg A) (norm_nonneg B)]
    have h1 : ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := htri.trans hsq
    have h1' : w * ‖A + B‖ ^ 2 ≤ 2 * (w * ‖A‖ ^ 2) + 2 * (w * ‖B‖ ^ 2) := by
      nlinarith [h1, hw0]
    calc ENNReal.ofReal (w * ‖A + B‖ ^ 2)
        ≤ ENNReal.ofReal (2 * (w * ‖A‖ ^ 2) + 2 * (w * ‖B‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal h1'
      _ = ENNReal.ofReal (2 * (w * ‖A‖ ^ 2)) + ENNReal.ofReal (2 * (w * ‖B‖ ^ 2)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = 2 * ENNReal.ofReal (w * ‖A‖ ^ 2) + 2 * ENNReal.ofReal (w * ‖B‖ ^ 2) := by
          rw [ofReal_two_mul, ofReal_two_mul]
  have hA : Measurable fun ξ : Space d => ENNReal.ofReal
      ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) :=
    measurable_sobolevWeight s _ hf
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
        * ‖𝓕 (fun x => ((f x + g x : ℝ) : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ, (2 * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2)
          + 2 * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2)) :=
        lintegral_mono hpt
    _ = (∫⁻ ξ, 2 * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2))
          + ∫⁻ ξ, 2 * ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2) := by
        rw [lintegral_add_left (hA.const_mul 2)]
    _ = 2 * (∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2))
          + 2 * (∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2)) := by
        rw [lintegral_const_mul' 2 _ (by norm_num),
          lintegral_const_mul' 2 _ (by norm_num)]


end Critical2DKPZ.Analysis.Sobolev.Rellich

end
