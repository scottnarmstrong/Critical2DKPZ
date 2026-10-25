/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Algebra
public import Critical2DKPZ.Analysis.Sobolev.TestFunctionFamily
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! The local negative Sobolev extended seminorm is the square root of localNegSobolevSq. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ

/-- Fourier transform of the compactly localized real distribution, at angular frequency `ξ`. -/
def localizedFourier (T : Distr) (χ : TestFn) (ξ : Plane) : ℂ :=
  (T (χ.mulCos ξ) : ℂ) - Complex.I * (T (χ.mulSin ξ) : ℂ)

/-- The Fourier transform of a localized distribution is continuous in frequency. -/
theorem continuous_localizedFourier (T : Distr) (χ : TestFn) :
    Continuous (localizedFourier T χ) := by
  have hc := T.continuous.comp (continuous_testFn_mulCos χ)
  have hs := T.continuous.comp (continuous_testFn_mulSin χ)
  exact (Complex.continuous_ofReal.comp hc).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp hs))


/-- The squared localized Fourier modulus is the sum of the squared cosine and sine pairings. -/
theorem norm_localizedFourier_sq (T : Distr) (χ : TestFn) (ξ : Plane) :
    ‖localizedFourier T χ ξ‖ ^ 2 = (T (χ.mulCos ξ)) ^ 2 + (T (χ.mulSin ξ)) ^ 2 := by
  rw [Complex.sq_norm]
  simp only [localizedFourier, Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
    sub_zero, Complex.sub_im, Complex.mul_im, zero_add, zero_sub]
  ring

/-- The Fourier-side measure, including the normalization `(2π)⁻²`. -/
def negSobolevFourierMeasure (a : ℝ) : Measure Plane :=
  volume.withDensity (fun ξ => ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)))

/-- The normalized negative Sobolev Fourier weight is measurable. -/
theorem measurable_negSobolevFourierDensity (a : ℝ) :
    Measurable (fun ξ : Plane => ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a))) := by
  have hw : Continuous (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ (-a)) := (continuous_const.add (continuous_norm.pow 2)).rpow_const (fun ξ =>
      Or.inl (by positivity : (1 : ℝ) + ‖ξ‖ ^ 2 ≠ 0))
  exact measurable_const.mul hw.measurable.ennreal_ofReal

/-- Extended local Sobolev seminorm, before restricting to finite-energy distributions. -/
def localNegSobolevENorm (a : ℝ) (T : Distr) (χ : TestFn) : ℝ≥0∞ :=
  eLpNorm (localizedFourier T χ) 2 (negSobolevFourierMeasure a)

/-- The square of the extended local seminorm equals localNegSobolevSq. -/
theorem localNegSobolevENorm_sq (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevENorm a T χ ^ 2 = localNegSobolevSq a T χ := by
  have hf := (continuous_localizedFourier T χ).aestronglyMeasurable
    (μ := negSobolevFourierMeasure a)
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hf
  simp only [localNegSobolevENorm]
  rw [show (eLpNorm (localizedFourier T χ) 2 (negSobolevFourierMeasure a)) ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (‖localizedFourier T χ ξ‖ ^ 2) ∂negSobolevFourierMeasure a by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
      ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using he]
  have hm : Measurable (fun ξ : Plane => ENNReal.ofReal (‖localizedFourier T χ ξ‖ ^ 2)) := by
    simpa only [Pi.pow_apply] using
      ((continuous_localizedFourier T χ).norm.pow 2).measurable.ennreal_ofReal
  rw [negSobolevFourierMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_negSobolevFourierDensity a) hm]
  simp only [Pi.mul_apply, mul_assoc, localNegSobolevSq]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext ξ
  rw [← ENNReal.ofReal_mul (negSobolev_weight_nonneg a ξ), norm_localizedFourier_sq]

/-- The localized Fourier transform preserves addition of distributions. -/
theorem localizedFourier_add (T U : Distr) (χ : TestFn) :
    localizedFourier (T + U) χ = localizedFourier T χ + localizedFourier U χ := by
  funext ξ
  simp only [localizedFourier, add_apply, Complex.ofReal_add, Pi.add_apply]
  ring

/-- The local negative Sobolev seminorm satisfies the triangle inequality. -/
theorem localNegSobolevENorm_add_le (a : ℝ) (T U : Distr) (χ : TestFn) :
    localNegSobolevENorm a (T + U) χ ≤ localNegSobolevENorm a T χ +
      localNegSobolevENorm a U χ := by
  rw [localNegSobolevENorm, localizedFourier_add]
  exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- Homogeneity, including zero scalar and infinite energy. -/
theorem localNegSobolevENorm_smul (a : ℝ) (T : Distr) (χ : TestFn) (c : ℝ) :
    localNegSobolevENorm a (c • T) χ = ENNReal.ofReal |c| * localNegSobolevENorm a T χ := by
  have he : localizedFourier (c • T) χ = c • localizedFourier T χ := by
    funext ξ
    simp only [localizedFourier, smul_apply, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_mul, Pi.smul_apply]
    ring
  rw [localNegSobolevENorm, he, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs]
  rfl

/-- The local negative Sobolev seminorm is finite exactly when its square is finite. -/
theorem localNegSobolevENorm_lt_top_iff (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevENorm a T χ < ⊤ ↔ localNegSobolevSq a T χ < ⊤ := by
  simpa only [ENNReal.rpow_two, localNegSobolevENorm_sq] using
    (ENNReal.rpow_lt_top_iff_of_pos (x := localNegSobolevENorm a T χ)
      (by norm_num : (0 : ℝ) < 2)).symm

/-- Finite local negative Sobolev energy is closed under addition. -/
theorem MemLocalNegSobolev.add {a : ℝ} {T U : Distr}
    (hT : MemLocalNegSobolev a T) (hU : MemLocalNegSobolev a U) :
    MemLocalNegSobolev a (T + U) := by
  intro χ
  apply (localNegSobolevENorm_lt_top_iff a (T + U) χ).mp
  apply (localNegSobolevENorm_add_le a T U χ).trans_lt
  exact ENNReal.add_lt_top.mpr ⟨(localNegSobolevENorm_lt_top_iff a T χ).mpr (hT χ),
    (localNegSobolevENorm_lt_top_iff a U χ).mpr (hU χ)⟩

end Critical2DKPZ

end
