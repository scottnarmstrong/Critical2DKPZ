/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.WeightBounds
public import Critical2DKPZ.Definitions.TestFn
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomially weighted integrability of Schwartz Fourier transforms

Smooth compactly supported kernels have Schwartz Fourier transforms. This file supplies the
weighted `L¹` integrability needed for the Fourier-side multiplication estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Critical2DKPZ.Analysis.Sobolev

private theorem one_add_pow_le_two_pow_mul_add_pow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (1 + r) ^ n ≤ 2 ^ n * (1 + r ^ n) := by
  have hbase : 1 + r ≤ 2 * max 1 r := by
    by_cases h : r ≤ 1
    · rw [max_eq_left h]
      linarith
    · rw [max_eq_right (le_of_lt (lt_of_not_ge h))]
      linarith
  have hpow : (1 + r) ^ n ≤ (2 * max 1 r) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hmax : (max 1 r) ^ n ≤ 1 + r ^ n := by
    by_cases h : r ≤ 1
    · rw [max_eq_left h]
      calc
        1 ^ n ≤ 1 := by simp
        _ ≤ 1 + r ^ n := le_add_of_nonneg_right (pow_nonneg hr n)
    · rw [max_eq_right (le_of_lt (lt_of_not_ge h))]
      exact le_add_of_nonneg_left (by positivity)
  calc
    (1 + r) ^ n ≤ 2 ^ n * (max 1 r) ^ n := by
      calc
        (1 + r) ^ n ≤ (2 * max 1 r) ^ n := hpow
        _ = 2 ^ n * (max 1 r) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (1 + r ^ n) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)

/-- A Schwartz function remains integrable after multiplication by any nonnegative polynomial
Fourier weight `(1 + ‖ξ‖²)^a`. -/
theorem integrable_one_add_norm_sq_rpow_mul_norm_schwartz {a : ℝ} (ha : 0 ≤ a)
    (f : 𝓢(Plane, ℂ)) :
    Integrable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * a)
  have hn' : 2 * a ≤ (n : ℝ) := le_of_lt hn
  have hfnorm : Integrable (fun ξ : Plane => ‖f ξ‖) := f.integrable.norm
  have hfpow : Integrable (fun ξ : Plane => ‖ξ‖ ^ n * ‖f ξ‖) :=
    f.integrable_pow_mul volume n
  have hmajor : Integrable
      (fun ξ : Plane => (2 : ℝ) ^ n * (‖f ξ‖ + ‖ξ‖ ^ n * ‖f ξ‖)) :=
    (hfnorm.add hfpow).const_mul ((2 : ℝ) ^ n)
  have hmeas : Measurable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖) := by
    fun_prop
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ξ
  have hr : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hb : 1 + ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by
    nlinarith [sq_nonneg ‖ξ‖]
  have hweight : (1 + ‖ξ‖ ^ 2) ^ a ≤ (1 + ‖ξ‖) ^ n := by
    calc
      (1 + ‖ξ‖ ^ 2) ^ a ≤ ((1 + ‖ξ‖) ^ 2) ^ a :=
        Real.rpow_le_rpow (by positivity) hb ha
      _ = (1 + ‖ξ‖) ^ (2 * a) := by
        rw [← Real.rpow_natCast (1 + ‖ξ‖) 2]
        exact (Real.rpow_mul
          (le_of_lt (by positivity : 0 < 1 + ‖ξ‖)) (2 : ℝ) a).symm
      _ ≤ (1 + ‖ξ‖) ^ n := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_le_rpow_of_exponent_le
            (show (1 : ℝ) ≤ 1 + ‖ξ‖ by linarith) hn')
  have hpoly := one_add_pow_le_two_pow_mul_add_pow hr n
  have hpoint : (1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖ ≤
      (2 : ℝ) ^ n * (‖f ξ‖ + ‖ξ‖ ^ n * ‖f ξ‖) := by
    calc
      (1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖ ≤ (1 + ‖ξ‖) ^ n * ‖f ξ‖ :=
        mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
      _ ≤ 2 ^ n * (1 + ‖ξ‖ ^ n) * ‖f ξ‖ :=
        mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ = _ := by ring
  have htarget_nonneg : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖ := by positivity
  calc
    ‖(1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖‖ =
        (1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
    _ ≤ (2 : ℝ) ^ n * (‖f ξ‖ + ‖ξ‖ ^ n * ‖f ξ‖) := hpoint

/-- The angular Fourier transform of a Schwartz function is Schwartz, so every nonnegative
Sobolev polynomial weight is integrable against its norm. -/
theorem integrable_negSobolevWeight_mul_norm_fourier_schwartz {a : ℝ} (ha : 0 ≤ a)
    (f : 𝓢(Plane, ℂ)) :
    Integrable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ a * ‖(𝓕 f) ξ‖) :=
  integrable_one_add_norm_sq_rpow_mul_norm_schwartz ha (𝓕 f)

/-- The square-root polynomial factor controlling one translated negative-Sobolev weight is
integrable against every Schwartz function. -/
theorem integrable_sqrt_polynomial_mul_norm_schwartz {a : ℝ} (ha : 0 ≤ a)
    (f : 𝓢(Plane, ℂ)) :
    Integrable (fun ξ : Plane =>
      Real.sqrt (2 ^ a * (1 + ‖ξ‖ ^ 2) ^ a) * ‖f ξ‖) := by
  have hpoly := integrable_one_add_norm_sq_rpow_mul_norm_schwartz ha f
  have hb : Continuous (fun ξ : Plane => (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
  have hp : Continuous (fun ξ : Plane => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ a) :=
    hb.rpow_const fun ξ => Or.inl (by positivity)
  have hmajor : Integrable (fun ξ : Plane =>
      (2 : ℝ) ^ a * ((1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖)) :=
    hpoly.const_mul ((2 : ℝ) ^ a)
  have hc : Continuous (fun ξ : Plane => Real.sqrt (2 ^ a *
      ((1 : ℝ) + ‖ξ‖ ^ 2) ^ a)) :=
    (continuous_const.mul hp).sqrt
  have hmeas : AEStronglyMeasurable (fun ξ : Plane =>
      Real.sqrt (2 ^ a * (1 + ‖ξ‖ ^ 2) ^ a) * ‖f ξ‖) volume :=
    (hc.mul f.continuous.norm).measurable.aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards with ξ
  set K : ℝ := 2 ^ a * (1 + ‖ξ‖ ^ 2) ^ a
  have hK1 : 1 ≤ K := by
    dsimp [K]
    have hA : 1 ≤ (2 : ℝ) ^ a := Real.one_le_rpow (by norm_num) ha
    have hB : 1 ≤ (1 + ‖ξ‖ ^ 2) ^ a :=
      Real.one_le_rpow (by nlinarith [sq_nonneg ‖ξ‖]) ha
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ a * (1 + ‖ξ‖ ^ 2) ^ a :=
        mul_le_mul hA hB (by norm_num) (by linarith)
  have hKpos : 0 ≤ K := le_trans zero_le_one hK1
  have hsqrt : Real.sqrt K ≤ K := by
    rw [Real.sqrt_le_left hKpos]
    nlinarith [sq_nonneg (K - 1)]
  calc
    ‖Real.sqrt K * ‖f ξ‖‖ = Real.sqrt K * ‖f ξ‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ K * ‖f ξ‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    _ = 2 ^ a * ((1 + ‖ξ‖ ^ 2) ^ a * ‖f ξ‖) := by
      dsimp [K]
      ring

/-- The real test function viewed as a complex Schwartz function. -/
def testFnSchwartz (χ : TestFn) : 𝓢(Plane, ℂ) :=
  (χ.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp χ.contDiff)


/-- The square-root polynomial factor needed for weighted `L²` translation is integrable against
the Fourier transform of a compactly supported test function. -/
theorem integrable_sqrt_negSobolevWeight_mul_norm_fourier_testFn {a : ℝ} (ha : 0 ≤ a)
    (χ : TestFn) :
    Integrable (fun ξ : Plane => Real.sqrt (2 ^ a * (1 + ‖ξ‖ ^ 2) ^ a) *
      ‖(𝓕 (testFnSchwartz χ)) ξ‖) :=
  integrable_sqrt_polynomial_mul_norm_schwartz ha (𝓕 (testFnSchwartz χ))

/-- A smooth compactly supported test function has an integrable polynomially weighted
Fourier transform of every nonnegative order. -/
theorem integrable_negSobolevWeight_mul_norm_fourier_testFn {a : ℝ} (ha : 0 ≤ a)
    (χ : TestFn) :
    Integrable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ a * ‖(𝓕 (testFnSchwartz χ)) ξ‖) :=
  integrable_negSobolevWeight_mul_norm_fourier_schwartz ha (testFnSchwartz χ)

/-- Schwartz Fourier inversion for a test function, in the explicit positive-phase form
used to transfer multiplication by a cutoff into frequency convolution. -/
theorem testFn_eq_integral_fourier_inverse (χ : TestFn) (x : Plane) :
    (χ x : ℂ) = ∫ η : Plane,
      Complex.exp ((↑(2 * Real.pi * inner ℝ η x) * Complex.I)) *
        𝓕 (fun y : Plane => (χ y : ℂ)) η := by
  calc
    (χ x : ℂ) = testFnSchwartz χ x := by simp [testFnSchwartz]
    _ = (𝓕⁻ (𝓕 (testFnSchwartz χ))) x := by simp
    _ = ∫ η : Plane,
        Complex.exp ((↑(2 * Real.pi * inner ℝ η x) * Complex.I)) *
          𝓕 (fun y : Plane => (χ y : ℂ)) η := by
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
      rw [Real.fourierInv_eq']
      rfl

/-- The square-root frequency-shift factor remains integrable after the `2π` rescaling in the
Schwartz Fourier inversion formula. -/
theorem integrable_scaled_sqrt_negSobolevWeight_mul_norm_fourier_testFn {a : ℝ}
    (ha : 0 ≤ a) (χ : TestFn) :
    Integrable (fun η : Plane =>
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a) *
        ‖(𝓕 (testFnSchwartz χ)) η‖) := by
  have hpoly := integrable_negSobolevWeight_mul_norm_fourier_testFn ha χ
  have hb : Continuous (fun η : Plane => (1 : ℝ) + (2 * Real.pi * ‖η‖) ^ 2) := by
    fun_prop
  have hp : Continuous (fun η : Plane =>
      ((1 : ℝ) + (2 * Real.pi * ‖η‖) ^ 2) ^ a) :=
    hb.rpow_const fun η => Or.inl (by positivity)
  have hc : Continuous (fun η : Plane => Real.sqrt
      (2 ^ a * ((1 : ℝ) + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) :=
    (continuous_const.mul hp).sqrt
  have hmeas : AEStronglyMeasurable (fun η : Plane =>
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a) *
        ‖(𝓕 (testFnSchwartz χ)) η‖) volume :=
    (hc.mul (𝓕 (testFnSchwartz χ)).continuous.norm).measurable.aestronglyMeasurable
  let C : ℝ := 2 ^ a * (1 + (2 * Real.pi) ^ 2) ^ a
  have hmajor : Integrable (fun η : Plane => C *
      ((1 + ‖η‖ ^ 2) ^ a * ‖(𝓕 (testFnSchwartz χ)) η‖)) volume := by
    simpa only [C] using hpoly.const_mul (2 ^ a * (1 + (2 * Real.pi) ^ 2) ^ a)
  refine hmajor.mono' hmeas ?_
  filter_upwards with η
  let K : ℝ := 2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a
  have hK1 : 1 ≤ K := by
    dsimp [K]
    have hA : 1 ≤ (2 : ℝ) ^ a := Real.one_le_rpow (by norm_num) ha
    have hB : 1 ≤ (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a :=
      Real.one_le_rpow (by nlinarith [sq_nonneg (2 * Real.pi * ‖η‖)]) ha
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (2 : ℝ) ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a :=
        mul_le_mul hA hB (by norm_num) (by linarith)
  have hKpos : 0 ≤ K := le_trans zero_le_one hK1
  have hsqrt : Real.sqrt K ≤ K := by
    rw [Real.sqrt_le_left hKpos]
    nlinarith [sq_nonneg (K - 1)]
  have hbase : 1 + (2 * Real.pi * ‖η‖) ^ 2 ≤
      (1 + (2 * Real.pi) ^ 2) * (1 + ‖η‖ ^ 2) := by
    nlinarith [sq_nonneg (2 * Real.pi * ‖η‖), sq_nonneg ‖η‖]
  have hweight : (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a ≤
      (1 + (2 * Real.pi) ^ 2) ^ a * (1 + ‖η‖ ^ 2) ^ a := by
    calc
      (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a ≤
          ((1 + (2 * Real.pi) ^ 2) * (1 + ‖η‖ ^ 2)) ^ a :=
        Real.rpow_le_rpow (by positivity) hbase ha
      _ = (1 + (2 * Real.pi) ^ 2) ^ a * (1 + ‖η‖ ^ 2) ^ a :=
        Real.mul_rpow (by positivity) (by positivity)
  have hbound : K ≤ C * (1 + ‖η‖ ^ 2) ^ a := by
    dsimp [K, C]
    calc
      2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a ≤
          2 ^ a * ((1 + (2 * Real.pi) ^ 2) ^ a * (1 + ‖η‖ ^ 2) ^ a) :=
        mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ (2 : ℝ) ^ a)
      _ = (2 ^ a * (1 + (2 * Real.pi) ^ 2) ^ a) * (1 + ‖η‖ ^ 2) ^ a := by ring
  calc
    ‖Real.sqrt K * ‖(𝓕 (testFnSchwartz χ)) η‖‖ =
        Real.sqrt K * ‖(𝓕 (testFnSchwartz χ)) η‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ K * ‖(𝓕 (testFnSchwartz χ)) η‖ :=
      mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    _ ≤ C * (1 + ‖η‖ ^ 2) ^ a * ‖(𝓕 (testFnSchwartz χ)) η‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = C * ((1 + ‖η‖ ^ 2) ^ a * ‖(𝓕 (testFnSchwartz χ)) η‖) := by ring

end Critical2DKPZ.Analysis.Sobolev

end
